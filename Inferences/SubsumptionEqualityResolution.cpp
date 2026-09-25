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
 * @file SubsumptionEqualityResolution.cpp
 * Implements class SubsumptionEqualityResolution.
 */

#include "Inferences/DemodulationHelper.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SubstHelper.hpp"

#include "SubsumptionEqualityResolution.hpp"

namespace Inferences
{

/**
 * What the premise's variables were bound to: the conclusion keeps the other
 * literals as they are, the unifier being a renaming on them, so each is read
 * back through that renaming into the conclusion's own variables; one only
 * the removed literal had is numbered after them, so that it is not taken for
 * one of them.
 */
template<class Unifier>
static void recordUse(Clause* res, Clause* premise, Literal* removed, Unifier& unifier)
{
  DHMap<unsigned, unsigned> back;
  DHSet<unsigned, FnvHash, IdentityHash> kept;
  res->collectVars(kept);
  unsigned fresh = 0;
  for (unsigned v : iterTraits(kept.iterator())) {
    back.set(unifier.apply(v).var(), v);
    fresh = std::max(fresh, v + 1);
  }
  struct Back {
    DHMap<unsigned, unsigned>* back;
    unsigned* fresh;
    TermList apply(unsigned v) {
      unsigned w;
      if (!back->find(v, w)) {
        w = (*fresh)++;
        back->insert(v, w);
      }
      return TermList(w, false);
    }
  } readBack{&back, &fresh};
  Stack<std::pair<unsigned, TermList>> bindings;
  DHSet<unsigned, FnvHash, IdentityHash> vars;
  premise->collectVars(vars);
  for (unsigned v : iterTraits(vars.iterator()))
    bindings.push({v, SubstHelper::apply(unifier.apply(v), readBack)});
  InferenceStore::instance()->recordPremiseUse(res, premise, removed, TermList::empty(), 0,
    bindings);
}

Clause* SubsumptionEqualityResolution::simplify(Clause* cl)
{
  for (const auto& lit : *cl) {
    if (!lit->isEquality() || lit->isPositive()) {
      continue;
    }

    auto [lhs, rhs] = lit->eqArgs();

    struct Unifier : SubstApplicator {
      bool unify(TermList lhs, TermList rhs) {
        return subst.unify(lhs, 0, rhs, 0);
      }
      TermList apply(unsigned v) const override {
        return subst.apply(TermList::var(v), 0);
      }
      RobSubstitution subst;
    } unifier;

    if (!unifier.unify(lhs, rhs)) {
      continue;
    }

    RStack<Literal*> resLits;
    DHSet<unsigned, FnvHash, IdentityHash> renamingDomain;
    DHSet<unsigned, FnvHash, IdentityHash> renamingRange;
    for (const auto& curr : *cl) {
      if (lit == curr) {
        continue;
      }
      if (!DemodulationHelper::isRenamingOn(&unifier, curr, renamingDomain, renamingRange)) {
        goto fail;
      }
      resLits->push(curr);
    }
    {
      Clause* res = Clause::fromStack(*resLits, SimplifyingInference1(InferenceRule::SUBSUMPTION_EQUALITY_RESOLUTION, cl));
      recordUse(res, cl, lit, unifier);
      return res;
    }
fail:
    continue;
  }
  return cl;
}

}
