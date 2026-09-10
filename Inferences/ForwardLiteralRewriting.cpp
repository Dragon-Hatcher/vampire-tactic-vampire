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
 * @file ForwardLiteralRewriting.cpp
 * Implements class ForwardLiteralRewriting.
 */

#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/ColorHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Kernel/InferenceStore.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "ForwardLiteralRewriting.hpp"

namespace Inferences
{

ForwardLiteralRewriting::ForwardLiteralRewriting(SaturationAlgorithm& salg)
  : _ord(salg.getOrdering()),
    _index(salg.getSimplifyingIndex<RewriteRuleIndex>())
{}

bool ForwardLiteralRewriting::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  TIME_TRACE("forward literal rewriting");

  unsigned clen=cl->length();

  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*cl)[i];
    auto git = _index->getGeneralizations(lit, lit->isNegative());
    while(git.hasNext()) {
      auto qr = git.next();
      Clause* counterpart=_index->getCounterpart(qr.data->clause);

      if(!ColorHelper::compatible(cl->color(), qr.data->clause->color()) ||
         !ColorHelper::compatible(cl->color(), counterpart->color()) ) {
        continue;
      }

      if(cl==qr.data->clause || cl==counterpart) {
  continue;
      }
      
      Literal* rhs0 = (qr.data->literal==(*qr.data->clause)[0]) ? (*qr.data->clause)[1] : (*qr.data->clause)[0];
      Literal* rhs = lit->isNegative() ? rhs0 : Literal::complementaryLiteral(rhs0);
      auto subs = qr.unifier;

      //Due to the way we build the _index, we know that rhs contains only
      //variables present in qr.data->literal
      ASS(qr.data->literal->containsAllVariablesOf(rhs));
      auto rhsS = subs.apply(rhs);

      if(_ord.compare(lit, rhsS)!=Ordering::GREATER) {
  continue;
      }

      Clause* premise=lit->isNegative() ? qr.data->clause : counterpart;
      // Martin: reductionPremise does not justify soundness of the inference
      //  (and brings in extra dependency which confuses splitter).
      //  Is there any other use for it?
      // TODO - reductionPremise is required for proof construction only,
      //        it should be included in some kind of Inference object. Consider this
      //        when reviewing proof construction
      /*
      Clause* reductionPremise=lit->isNegative() ? counterpart : qr.data->clause;
      if(reductionPremise==premise) {
  reductionPremise=0;
      }
      */

      RStack<Literal*> resLits;

      resLits->push(rhsS);

      for(Literal* curr : cl->iterLits()) {
        if(curr!=lit) {
          resLits->push(curr);
        }
      }

      premises = pvi( getSingletonIterator(premise));
      replacement = Clause::fromStack(*resLits, SimplifyingInference2(InferenceRule::FORWARD_LITERAL_REWRITING, cl, premise));
      // The premise is one half of an equivalence, and rewriting with it is
      // resolving against it: its other literal is what goes into the
      // conclusion. Which of its literals was resolved on, and at what match,
      // is recovered here -- the halves are variants of one another, so the
      // literal the index gave need not be one of this premise's.
      for (unsigned i = 0; i < premise->length(); i++) {
        Substitution s;
        if (!MatchingUtils::match((*premise)[i], lit, /*complementary=*/true, s)) {
          continue;
        }
        Literal* other = (*premise)[premise->length() - 1 - i];
        if (SubstHelper::apply(other, s) != rhsS) {
          continue;
        }
        InferenceStore::instance()->recordPremiseUse(replacement, cl, lit,
          TermList::empty(), 0, Substitution());
        InferenceStore::instance()->recordPremiseUse(replacement, premise,
          (*premise)[i], TermList::empty(), 0, s);
        break;
      }
      return true;
    }
  }

  return false;
}

};
