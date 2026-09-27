/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file FastCondensation.cpp
 * Implements class FastCondensation.
 */

#include "Lib/DHMap.hpp"
#include "Debug/TimeProfiling.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Kernel/InferenceStore.hpp"
#include "Kernel/Substitution.hpp"
#include "Lib/DHSet.hpp"

#include "FastCondensation.hpp"

#undef LOGGING
#define LOGGING 0

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

namespace {

template<bool higherOrder>
struct CondensationBinder
{
  void init(DHMap<unsigned, int, FnvHash, IdentityHash>* varMap_)
  {
    varMap=varMap_;
  }
  void reset()
  {
    bindings.reset();
  }
  /** What `var` was bound to, if it was. */
  bool binding(unsigned var, TermList& term)
  {
    return bindings.find(var, term);
  }
  bool bind(unsigned var, TermList term)
  {
    if(varMap->get(var)==-1) {
      return term.isVar() && var==term.var();
    }

    if constexpr (higherOrder) {
      if (term.containsLooseDBIndex()) {
        return false;
      }
    }

    TermList* binding;
    if(bindings.getValuePtr(var,binding,term)) {
      return true;
    }
    return *binding==term;
  }
  void specVar(unsigned var, TermList term)
  { ASSERTION_VIOLATION; }
private:
  DHMap<unsigned, int, FnvHash, IdentityHash>* varMap;
  DHMap<unsigned, TermList, FnvHash, IdentityHash> bindings;
};

}

template<bool higherOrder>
Clause* FastCondensation<higherOrder>::simplify(Clause* cl)
{
  TIME_TRACE("fast condensation");

  unsigned clen=cl->length();
  if(clen<=1) {
    return cl;
  }

  //if variable is present in only one literal, the map contains its index,
  //otherwise it contains -1
  static DHMap<unsigned, int, FnvHash, IdentityHash> varLits;
  varLits.reset();

  for(unsigned i=0;i<clen;i++) {
    VariableIterator vit((*cl)[i]);
    while(vit.hasNext()) {
      unsigned var=vit.next().var();
      int* pvlit;
      if(!varLits.getValuePtr(var, pvlit)) {
        if(*pvlit!=static_cast<int>(i)) {
          *pvlit=-1;
        }
      }
      else {
        *pvlit=i;
      }
    }
  }

  static CondensationBinder<higherOrder> cbinder;
  cbinder.init(&varLits);

  for(unsigned cIndex=0;cIndex<clen;cIndex++) {
    Literal* cLit=(*cl)[cIndex];
    if(cLit->ground()) {
      //succeeding with ground literal would mean there are duplitace
      //literals in the clause, which should have already been removed
      continue;
    }
    for(unsigned mIndex=0;mIndex<clen;mIndex++) {
      if(mIndex==cIndex) {
        continue;
      }
      if(MatchingUtils::match(cLit, (*cl)[mIndex], false, cbinder)) {
        RStack<Literal*> resLits;

        for(unsigned ci=0;ci<clen;ci++) {
          if(ci!=cIndex) {
            resLits->push((*cl)[ci]);
          }
        }
 
        Clause* res = Clause::fromStack(*resLits, SimplifyingInference1(InferenceRule::CONDENSATION, cl));
        // The conclusion is the premise at the matcher of one of its literals
        // onto another, which moves only the variables that literal alone has,
        // less the literal that then duplicates the other: which instance it
        // is is the whole of what the step did, as for `Condensation`.
        // Only the dropped literal's variables are read off the binder, which
        // is not reset between attempts and can hold what a failed one bound.
        {
          Substitution s;
          DHSet<unsigned, FnvHash, IdentityHash> vars;
          cl->collectVars(vars);
          DHSet<unsigned, FnvHash, IdentityHash> moved;
          for (unsigned v : iterTraits(VariableIterator(cLit)).map([](TermList t) { return t.var(); }))
            moved.insert(v);
          for (unsigned v : iterTraits(vars.iterator())) {
            TermList bound;
            s.bindUnbound(v, moved.contains(v) && cbinder.binding(v, bound)
                ? bound : TermList(v, false));
          }
          InferenceStore::instance()->recordPremiseUse(res, cl, nullptr,
            TermList::empty(), 0, s);
        }
        return res;
      }
    }
  }
  return cl;
}

template class FastCondensation<false>;
template class FastCondensation<true>;

}
