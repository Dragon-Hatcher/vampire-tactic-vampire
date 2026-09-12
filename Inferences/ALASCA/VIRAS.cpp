/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "VIRAS.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Substitution.hpp"
#include "Lib/Option.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }

using namespace Kernel;
using namespace Inferences;
using namespace ALASCA;
using namespace Lib;

#include "VirasInterfacing.hpp"

/* turns a viras::iter iterator into a Lib/Metaiterators.hpp iterator */
template<class VirasIter>
class IntoVampireIter {
  VirasIter _iter;
  Option<std::optional<viras::iter::value_type<VirasIter>>> _next;
public:
  IntoVampireIter(VirasIter iter) : _iter(std::move(iter)), _next() {}

  using ElementType = viras::iter::value_type<VirasIter>;
  void loadNext() {
    if (_next.isNone()) {
      _next = some(_iter.next());
    }
  }

  bool hasNext() {
    loadNext();
    return bool(*_next);
  }

  viras::iter::value_type<VirasIter> next() {
    loadNext();
    return std::move(*_next.take().unwrap());
  }
};

template<class VirasIter>
auto intoVampireIter(VirasIter i)
{ return iterTraits(IntoVampireIter<VirasIter>(std::move(i))); }

struct Void {};

template<class NumTraits, class F>
void traverseLiraVars(TermList self, F f) {
  VampireVirasConfig<NumTraits>{}.
    matchTerm(self,
      /* var v */ [&](auto y) { f(y); return Void {}; },
      /* numeral 1 */ [&]() { return Void {}; },
      /* k * t */ [&](auto k, auto t)  { traverseLiraVars<NumTraits>(t, f); return Void {}; },
      /* l + r */ [&](auto l, auto r)  {
        traverseLiraVars<NumTraits>(l, f);
        traverseLiraVars<NumTraits>(r, f);
        return Void {};
      },
      /* floor */ [&](auto t) { traverseLiraVars<NumTraits>(t, f); return Void {}; }
      );
}


template<class NumTraits>
Option<SimplifyingGeneratingInference::ClauseGenerationResult> VirasQuantifierElimination::generateSimplify(NumTraits n, Clause* premise) {
  DEBUG(0, *premise)
  auto viras = viras::viras(VampireVirasConfig<NumTraits>{});
  Recycled<DHSet<unsigned, FnvHash, IdentityHash>> shieldedVars;
  Recycled<DHSet<unsigned, FnvHash, IdentityHash>> candidateVars;
  Recycled<Stack<Literal*>> toElim;
  Recycled<Stack<Literal*>> otherLits;
  auto noteShielded = [&](Term* t) {
    VariableIterator vars(t);
    while (vars.hasNext()) {
      auto v = vars.next();
      shieldedVars->insert(v.var());
    }
  };

  Recycled<DHSet<unsigned, FnvHash, IdentityHash>> topLevelVars;
  for (auto l : premise->iterLits()) {
    Option<AlascaLiteral<NumTraits>> norm = _shared.norm().tryNormalizeInterpreted(l)
      .flatMap([](auto l) { return l.template as<AlascaLiteral<NumTraits>>().toOwned(); })
      .filter([](auto l) { switch(l.symbol()) {
          case AlascaPredicate::EQ:
          case AlascaPredicate::NEQ:
          case AlascaPredicate::GREATER:
          case AlascaPredicate::GREATER_EQ: return true;
          }
          ASSERTION_VIOLATION
          });

    if (norm.isNone()) {
      otherLits->push(l);
      noteShielded(l);
    } else {
      toElim->push(l);
      traverseLiraVars<NumTraits>(norm->term().denormalize(),
          [&](TermList t) {
            if (t.isVar()) {
              candidateVars->insert(t.var());
            } else {
              noteShielded(t.term());
            }
          });
    }
  }

  auto unshielded = iterTraits(candidateVars->iterator())
    .filter([&](auto x) { return !shieldedVars->contains(x); })
    .tryNext();

  if (unshielded.isNone()) {
    return {};
  } else {
    auto var = typename VampireVirasConfig<NumTraits>::VarWrapper(TermList::var(*unshielded));
    // Quantifier elimination takes the clause's behaviour at an end of the
    // order, which is no term: what makes that sound is that the clause holds
    // of every value, and below every point at which one of its literals
    // changes sign each literal takes the value the end of the order gives it.
    // A point below all of them is worked out here, so that replaying the step
    // is a matter of taking the premise at it. Only the ends of the order are
    // covered: an elimination set can also hold a term, a term and an
    // infinitesimal, or a periodic family, and for those nothing is recorded
    // and the step cannot be replayed.
    using Numeral = typename NumTraits::ConstantType;
    Option<Numeral> point;
    {
      bool numeric = true;
      for (auto l : *toElim) {
        auto norm = _shared.norm().tryNormalizeInterpreted(l)
          .flatMap([](auto l) { return l.template as<AlascaLiteral<NumTraits>>().toOwned(); });
        if (norm.isNone()) { numeric = false; break; }
        Option<Numeral> coeff;
        Numeral constant(0);
        for (auto monom : norm->term().iterSummands()) {
          if (monom.tryVar() == some(Variable(*unshielded))) {
            coeff = some(monom.numeral);
          } else if (monom.factors->nFactors() == 0) {
            constant = constant + monom.numeral;
          } else {
            /* a summand that is neither the variable nor a number: where it
             * changes sign depends on another variable and is no numeral */
            numeric = false;
            break;
          }
        }
        if (!numeric) break;
        if (coeff.isNone()) continue;
        auto changesAt = -constant / coeff.unwrap();
        if (point.isNone() || changesAt < point.unwrap())
          point = some(changesAt);
      }
      if (!numeric)
        point = Option<Numeral>();
    }
    unsigned elimVar = *unshielded;
    return some(ClauseGenerationResult {
      .clauses = pvi(
          intoVampireIter(viras.quantifier_elimination(var, &*toElim))
            .map([premise, elimVar, point, otherLits = std::move(otherLits)](auto litIter) {
              auto cl = Clause::fromIterator(
                  concatIters(
                    intoVampireIter(litIter),
                    otherLits->iter()
                    ),
                  Inference(SimplifyingInference1(InferenceRule::ALASCA_VIRAS_QE, premise)));
              if (point.isSome()) {
                Substitution subst;
                subst.bindUnbound(elimVar,
                  NumTraits::constantTl(point.unwrap() - Numeral(1)));
                InferenceStore::instance()->recordPremiseUse(cl, premise,
                  nullptr, TermList::empty(), 0, subst);
              }
              return cl;
            })
          )
        ,
      .premiseRedundant = true,
    });
  }
}

Option<SimplifyingGeneratingInference::ClauseGenerationResult> VirasQuantifierElimination::generateSimplify(IntTraits n, Clause* premise) {
  // TODO viras for integers ? (=  cooper)
  return {};
}

VirasQuantifierElimination::VirasQuantifierElimination(SaturationAlgorithm& salg) : _shared(salg.alascaState()) {}

SimplifyingGeneratingInference::ClauseGenerationResult VirasQuantifierElimination::generateSimplify(Clause* premise) {
  return 
    forAnyNumTraits([&](auto n) { return generateSimplify(n, premise); })
    .unwrapOrElse([]() {
      return ClauseGenerationResult {
        .clauses = VirtualIterator<Clause*>::getEmpty(),
        .premiseRedundant = false,
      };
    });
}

