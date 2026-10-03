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
 * @file InterpretedEvaluation.cpp
 * Implements class InterpretedEvaluation.
 */

#include "Kernel/InferenceStore.hpp"
#include "Lib/Stack.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"

#include "InterpretedEvaluation.hpp"

#undef LOGGING
#define LOGGING 0

namespace Inferences
{
using namespace std;
using namespace Lib;
using namespace Kernel;


InterpretedEvaluation::InterpretedEvaluation(bool doNormalize) :
  _simpl(new InterpretedLiteralEvaluator(doNormalize)), _doNormalize(doNormalize)
{
}

InterpretedEvaluation::~InterpretedEvaluation()
{
  delete _simpl;
}



bool InterpretedEvaluation::simplifyLiteral(Literal* lit,
	bool& constant, Literal*& res, bool& constantTrue)
{
  if(lit->numTermArguments()==0) {
    //we have no interpreted predicates of zero arity
    return false;
  }

  return _simpl->evaluate(lit, constant, res, constantTrue);
}

Clause* InterpretedEvaluation::simplify(Clause* cl)
{
    TIME_TRACE("interpreted evaluation");

    /* do not evaluate theory axioms (both internal and external theory axioms)
     * Note: We want to skip the evaluation of internal theory axioms, because we already assume that
     *       internally added theory axioms are simplified as much as possible.
     *       We currently also skip externally added theory axioms. But by doing so we risk that we don't
     *       simplify simplifiable theory axioms, which were added by users unfamiliar with theorem proving.
     */
    if(cl->isTheoryAxiom()) return cl;


    RStack<Literal*> resLits;
    // What each literal became -- itself, another, or nothing where it was
    // found false -- for replaying the step; made into its images only if
    // the clause changes, which it seldom does.
    RStack<Literal*> became;
    unsigned clen=cl->length();
    bool modified=false;
    for(unsigned li=0;li<clen; li++) {
      Literal* lit=(*cl)[li];
      Literal* res;
      bool constant, constTrue;
      bool litMod=simplifyLiteral(lit, constant, res, constTrue);
      if(!litMod) {
        became->push(lit);
        resLits->push(lit);
        continue;
      }
      modified=true;
      if(constant) {
        if(constTrue) {
          //cout << "evaluate " << cl->toString() << " to true" << endl;
          return 0;
        } else {
          became->push(nullptr);
          continue;
        }
      }

      became->push(res);
      resLits->push(res);
    }
    if(!modified) {
      return cl;
    }

    Stack<InferenceStore::LiteralImage> images;
    for(unsigned li=0;li<clen; li++) {
      images.push({(*cl)[li], (*became)[li], RationalConstantType(1)});
    }
    Clause* result = Clause::fromStack(*resLits,SimplifyingInference1(InferenceRule::EVALUATION, cl));
    InferenceStore::instance()->recordLiteralImages(result,
      _doNormalize ? InferenceStore::LiteralProcedure::INTERPRETED_EVALUATION_NORMALIZING
                       : InferenceStore::LiteralProcedure::INTERPRETED_EVALUATION,
      std::move(images));
    return result;
}

}
