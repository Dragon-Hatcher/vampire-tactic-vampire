/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Demodulation.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Lib/StringUtils.hpp"

namespace Inferences {
namespace ALASCA {

// ±ks + t ≈ 0              C[sσ]
// ==============================
//       C[sσ -> (∓ (1/k) t)σ]
// where
// • sσ ≻ tσ
// • C[sσ] ≻ (±ks + t ≈ 0)σ
//
Option<Clause*> Demodulation::apply(
                      AlascaState& shared,
                      Lhs lhs, // <- { ±ks + t ≈ 0 }
                      Rhs rhs) // <- C[sσ]
{
  TIME_TRACE("alasca demodulation")
  auto nothing = [&]() { return Option<Clause*>(); };

  {
    TIME_TRACE("sort check")
    RobSubstitution sortUnif;
    if (!sortUnif.match(SortHelper::getEqualityArgumentSort(lhs.literal()), 0, rhs.sort(), 1))
      return nothing();
  }

  ASS(lhs.clause()->size() == 1)
  ASS(lhs.literal()->isEquality())
  ASS(lhs.literal()->isPositive())

  unsigned lBank = 0, rBank = 1;
  RobSubstitution subs;
  {
    // TODO we are unifying here again, as the interface to the substitution tree is to tedious to use. this might need some refactor in order to not to double work in the future.
    TIME_TRACE("extra unification that makes implementation much easier but maybe sacrifices some performance")
    ALWAYS(subs.match(lhs.biggerSide(), lBank, rhs.term, rBank));
  }
  auto sigmaL = [&](auto t) { return subs.apply(t, lBank); };
  auto sigmaR = [&](auto t) { return subs.apply(t, rBank); }; // <- is just a variable renaming
  ASS_EQ(sigmaL(lhs.biggerSide()), sigmaR(rhs.term));


  // TODO i think this assertion always holds due to the QKBO properties on the ground level, but the impl might return incomparable if the lifting's too weak
  // ASS_REP(shared.ordering->compare(lhs.biggerSide(), lhs.smallerSide()) == Ordering::Result::GREATER, lhs)

  // checking `C[sσ] ≻ (±ks + t ≈ 0)σ`
  {
    TIME_TRACE("checking C[sσ] ≻ (±ks + t ≈ 0)σ")
    auto lhs_sigma = sigmaL(lhs.literal());
    // TODO more optimizations
    auto optimized_greater = rhs.ordOptimization;
    auto greater = optimized_greater || iterTraits(rhs.clause->iterLits())
      .any([&](auto lit)
          { return shared.greater(sigmaR(lit), lhs_sigma); });
    if (!greater)  {
      return nothing();
    }
  }

  auto replacement = sigmaL(lhs.smallerSide());

  auto altered = false;
  // The premise's literals the rewrite changed, and what each became.
  Stack<std::pair<Literal*, Literal*>> rewritten;
  auto lits = iterTraits(rhs.clause->iterLits())
    .map([&](auto lit) {
        auto repl = EqHelper::replace(sigmaR(lit), sigmaR(rhs.term), replacement);
        altered |= repl != lit;
        if (repl != sigmaR(lit)) {
          rewritten.push({lit, repl});
        }
        return repl;
    })
    .template collect<Stack>();
  ASS_REP(altered, outputToString("\n", lhs, "\n", rhs))

  Inference inf(SimplifyingInference2(Kernel::InferenceRule::ALASCA_FWD_DEMODULATION, lhs.clause(), rhs.clause));
  auto out = Clause::fromStack(lits, inf);
  // What the inference did to each premise, as superposition records it: the
  // equation and which side of it, the term it rewrote throughout the other
  // premise, and the match -- and the renaming of the other premise's
  // variables, which is all its bank is put through.
  {
    auto record = [&](Clause* premise, unsigned bank, Literal* on, TermList term,
                      unsigned flags) {
      Substitution s;
      DHSet<unsigned, FnvHash, IdentityHash> vars;
      premise->collectVars(vars);
      for (unsigned v : iterTraits(vars.iterator()))
        s.bindUnbound(v, subs.apply(TermList(v, false), bank));
      InferenceStore::instance()->recordPremiseUse(out, premise, on, term, flags, s);
    };
    record(lhs.clause(), lBank, lhs.literal(), lhs.biggerSide(), 0);
    auto eq = lhs.literal();
    auto t = lhs.smallerSide();
    if (!(*eq->nthArgument(0) == t || *eq->nthArgument(1) == t)) {
      InferenceStore::instance()->recordOther(out, lhs.clause(), t);
    }
    // The rewrite is of the whole premise; the literal recorded is one it
    // rewrote in.
    ASS(rewritten.isNonEmpty())
    record(rhs.clause, rBank, rewritten[0].first, rhs.term,
      InferenceStore::rewritesWholePremise);
    for (auto [from, to] : iterTraits(rewritten.iter())) {
      TermList lhsArg = from->isEquality()
        ? EqHelper::replace(sigmaR(from->termArg(0)), sigmaR(rhs.term), replacement)
        : TermList::empty();
      InferenceStore::instance()->recordRewritten(out, rhs.clause, from, to, lhsArg);
    }
  }
  return Option<Clause*>(out);
}





} // namespace ALASCA
} // namespace Inferences
