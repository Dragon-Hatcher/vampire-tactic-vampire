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
 * @file FloorBounds.hpp
 * Defines class FloorBounds
 *
 */

#ifndef __ALASCA_Inferences_FloorBounds__
#define __ALASCA_Inferences_FloorBounds__

#include "Kernel/InferenceStore.hpp"
#include "Kernel/Substitution.hpp"
#include "Debug/Assertion.hpp"
#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Superposition.hpp"
#include "FourierMotzkin.hpp"
#include "Lib/Metaiterators.hpp"

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class FloorBounds 
  : public GeneratingInferenceEngine 
{
  using NumTraits = RealTraits;

  AlascaState& _shared;

  static TermList floor(TermList t) { return TermList(NumTraits::floor(t)); }
  static TermList minus(TermList t) { return TermList(NumTraits::minus(t)); }
  static TermList ceil(TermList t) { return minus(floor(minus(t))); }

  template<class... Args>
  static TermList sum(Args... args) 
  { return NumTraits::sum(iterItems(args...)); }

  static Literal* greater0(TermList t) 
  { return NumTraits::greater(/* polarity */ true, t, NumTraits::zero()); }

  static Literal* geq0(TermList t) 
  { return NumTraits::geq(/* polarity */ true, t, NumTraits::zero()); }

  static Literal* eq(TermList s, TermList t) 
  { return NumTraits::eq(/* polarity */ true, s, t); }

  static Literal* eq0(TermList s) 
  { return NumTraits::eq(/* polarity */ true, s, numeral(0)); }

  static TermList numeral(int i) 
  { return NumTraits::constantTl(i); }

  template<class Premise, class... Lits>
  static auto resClause(Premise const& premise, Lits... lits) {
    return Clause::fromIterator(
        concatIters(premise.contextLiterals(), iterItems(lits...)),
        GeneratingInference1(InferenceRule::ALASCA_FLOOR_BOUNDS, premise.clause()));
  }

  /**
   * `resClause`, recording for replay which of the rule's six shapes it is,
   * the premise's floor `⌊s⌋` and other term `t`, the coefficient `k` of the
   * floor (its magnitude), and the literals it built.
   */
  template<class Premise, class... Lits>
  static Clause* recorded(Premise const& premise, unsigned variant, TermList other,
      TermList factor, Lits... lits) {
    Clause* cl = resClause(premise, lits...);
    InferenceStore::instance()->recordPremiseUse(cl, premise.clause(), premise.literal(),
      premise.selectedAtom(), 0, Substitution());
    InferenceStore::instance()->recordOther(cl, premise.clause(), other);
    InferenceStore::instance()->recordFactor(cl, premise.clause(), factor);
    Stack<Literal*> built;
    (built.push(lits), ...);
    InferenceStore::instance()->recordIntroduced(cl, built, variant);
    return cl;
  }

  auto generateClauses(Superposition::Lhs const& premise) const
  {
    auto s = NumTraits::ifFloor(premise.selectedAtom(), [](auto s) { return s; }).unwrap();
    auto t = premise.smallerSide();
    // C \/ ⌊s⌋ = t
    // ===========
    // C \/ t − s + 1 > 0
    // C \/ s − t ≥ 0
    return iterItems<Clause*>(
        recorded(premise, 0, t, premise.factor(), greater0(sum(t, minus(s), numeral(1)))),
        recorded(premise, 1, t, premise.factor(), geq0(sum(s, minus(t))))
        );
  }

  auto generateClauses(FourierMotzkin::Lhs const& premise) const 
  {
    ASS(premise.numeral<NumTraits>().isPositive())
    auto s = NumTraits::ifFloor(premise.selectedAtom(), [](auto s) { return s; }).unwrap();
    auto t = premise.notSelectedTerm();
    auto pred = premise.alascaPredicate().unwrap();
    ASS(isInequality(pred))
    auto k = NumTraits::constantTl(premise.template numeral<NumTraits>().abs());


    return iterItems(
        // +⌊s⌋ >=  -t       x - ⌊x⌋ >= 0
        // ================================
        // C ∨ s + ⌊t⌋ > 0 ∨ ⌊s⌋ + ⌊t⌋ ≈ 0
          pred == AlascaPredicate::GREATER_EQ ? recorded(premise, 2, t, k,
              greater0(sum(s, floor(t))), 
              eq0(sum(floor(s), floor(t))))
        // +⌊s⌋ + t > 0      
        // ======================================
        // +s + ⌈t⌉ - 1 > 0 \/  ⌊s⌋ + ⌈t⌉ - 1 = 0
        : pred == AlascaPredicate::GREATER    ? recorded(premise, 3, t, k,
            greater0(sum(s, ceil(t), numeral(-1))),
            eq0(sum(floor(s), ceil(t), numeral(-1))))
        : assertionViolation<Clause*>()
        );
  }


  auto generateClauses(FourierMotzkin::Rhs const& premise) const 
  {
    ASS(premise.numeral<NumTraits>().isNegative())
    auto s = NumTraits::ifFloor(premise.selectedAtom(), [](auto s) { return s; }).unwrap();
    auto t = premise.notSelectedTerm();
    auto pred = premise.alascaPredicate().unwrap();
    ASS(isInequality(pred))
    auto k = NumTraits::constantTl(premise.template numeral<NumTraits>().abs());

    return iterItems(
          //       -⌊s⌋ + t >= 0        
          // ============================
          // −s + ⌊t⌋ > 0 ∨ -⌊s⌋ + ⌊t⌋ ≈ 0
            pred == AlascaPredicate::GREATER_EQ ? recorded(premise, 4, t, k,
                               greater0(sum(minus(s), floor(t))),
                               eq0(sum(minus(floor(s)), floor(t))))
          //             -⌊s⌋ + t > 0
          // =====================================
          // −⌊s⌋ + ⌈t⌉ − 1 ≈ 0 ∨ −s + ⌈t⌉ − 1 > 0
          : pred == AlascaPredicate::GREATER ?  recorded(premise, 5, t, k,
                               greater0(sum(minus(s), ceil(t), numeral(-1))),
                               eq0(sum(minus(floor(s)), ceil(t), numeral(-1))))
          : assertionViolation<Clause*>()
          );
  }

  template<class RuleKind>
  auto generateClauses(Clause* premise) const {
    return iterTraits(RuleKind::iter(_shared, premise))
      .filter([](auto x) { return NumTraits::ifFloor(x.selectedAtom(), [](auto...) { return true; }); })
      .flatMap([this](auto x) { return this->generateClauses(x); });
  }

public:
  USE_ALLOCATOR(FloorBounds);

  FloorBounds(FloorBounds&&) = default;
  FloorBounds(SaturationAlgorithm& salg) 
    : _shared(salg.alascaState())
  {  }

  ClauseIterator generateClauses(Clause* premise) final
  {
    return pvi(concatIters(
          generateClauses<Superposition::Lhs>(premise),
          generateClauses<FourierMotzkin::Lhs>(premise),
          generateClauses<FourierMotzkin::Rhs>(premise)
    ));
  }
};

} // namespace ALASCA 
} // namespace Inferences 


#endif /*__ALASCA_Inferences_FloorBounds__*/
