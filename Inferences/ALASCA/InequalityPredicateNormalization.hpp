/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __ALASCA_Inferences_InequalityPredicateNormalization__
#define __ALASCA_Inferences_InequalityPredicateNormalization__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA.hpp"
#include "Kernel/InferenceStore.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

/* an inference rule that rewrites 
 *  s >= t ==> s > t \/ s == t 
 *  and 
 *  s != t ==> s > t \/ t > s
 */
// TODO write tests
class InequalityPredicateNormalization
: public ImmediateSimplificationEngine
{
public:
  USE_ALLOCATOR(InequalityPredicateNormalization);

  Clause* simplify(Clause* premise) override 
  {
    RStack<Literal*> res; 
    bool changed = false;
    // the two literals each rewritten literal became
    Stack<Literal*> built;
    Stack<Literal*> sources;
    for (auto l : premise->iterLits()) {
      auto norm = forAnyNumTraits([&](auto n) -> bool {
        if (n.isGeq(l)) {
          res->push(n.greater(true, l->termArg(0), l->termArg(1)));
          res->push(n.eq(true, l->termArg(0), l->termArg(1)));
          built.push((*res)[res->size() - 2]); built.push(res->top());
          sources.push(l); sources.push(l);
          return true;
        } else if (n.isNegEq(l)) {
          res->push(n.greater(true, l->termArg(0), l->termArg(1)));
          res->push(n.greater(true, l->termArg(1), l->termArg(0)));
          built.push((*res)[res->size() - 2]); built.push(res->top());
          sources.push(l); sources.push(l);
          return true;
        } else {
          return false;
        }
      });
      if (norm) {
        changed = true;
      } else {
        res->push(l);
      }
    }
    
    if (changed) {
      auto out = Clause::fromStack(*res, SimplifyingInference1(Kernel::InferenceRule::ALASCA_NORMALIZATION, premise));
      // no literal images, unlike the same rule applied by ALASCA::Normalization
      InferenceStore::instance()->recordLiteralImages(out,
          InferenceStore::LiteralProcedure::INEQUALITY_PREDICATE_NORMALIZATION,
          Stack<InferenceStore::LiteralImage>());
      InferenceStore::instance()->recordIntroduced(out, built, 0, sources);
      return out;
    } else {
      return premise;
    }
  }
};



#undef DEBUG
} // namespaceALASCA 
} // namespace Inferences

#endif /*__ALASCA_Inferences_InequalityPredicateNormalization__*/
