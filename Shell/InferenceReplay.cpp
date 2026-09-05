#include "Lib/DHSet.hpp"
#include "Shell/InferenceReplay.hpp"
#include "Inferences/BackwardDemodulation.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Inferences/EqualityFactoring.hpp"
#include "Inferences/EqualityResolution.hpp"
#include "Inferences/Factoring.hpp"
#include "Inferences/ForwardDemodulation.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Inferences/Superposition.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Shell/EqResWithDeletion.hpp"
#include "Shell/InferenceRecorder.hpp"
#include "Shell/Rectify.hpp"

namespace Shell {
void InferenceReplayer::replayInference(Kernel::Unit *u)
{
  auto it = u->getParents();
  ClauseStack stack;
  while (it.hasNext()) {
    auto parent = it.next();
    if (parent->isClause()) {
      stack.push((parent->asClause()));
    }
  }

  if (u->inference().rule() == InferenceRule::RESOLUTION) {
    BinaryResolution br(*alg);
    runGenerating(&br, stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::FORWARD_DEMODULATION){
      ForwardDemodulationReplay fd(*alg);
      runGenerating(&fd,
      stack, u->asClause());
  }
  else if(u->inference().rule() == InferenceRule::BACKWARD_DEMODULATION){
      BackwardDemodulation<false> bd(*alg);
      runBackwardsSimp(&bd,
      stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::SUPERPOSITION) {
    Inferences::Superposition sp(*alg);
    runGenerating(&sp,
                         stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::EQUALITY_RESOLUTION) {
    Inferences::EqualityResolution eq(*alg);
    runGenerating(&eq,
                         stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::EQUALITY_RESOLUTION_WITH_DELETION) {

    auto ul = UnitList::empty();
    UnitList::pushFromIterator(ClauseStack::Iterator(stack), ul);
    Problem p(ul);
    env.setMainProblem(&p);
    Inferences::EqResWithDeletion eq;
    eq.apply(p);
  }
  else if(u->inference().rule() == InferenceRule::EQUALITY_FACTORING){
      auto ul = UnitList::empty();
      UnitList::pushFromIterator(ClauseStack::Iterator(stack), ul);
      Problem p(ul);      
      env.setMainProblem(&p);
      Inferences::EqualityFactoring eqf(*alg);
      runGenerating(&eqf, stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::FACTORING) {
    Inferences::Factoring fact(*alg);
    runGenerating(&fact,
                         stack, u->asClause());
  } 
  else if (u->inference().rule() == InferenceRule::RECTIFY) {
    FormulaUnit *fu = static_cast<FormulaUnit *>(u->getParents().next());
    Rectify::rectify(fu);
  }
  else {
    return; // not replayable yet
  }
  return;
}

Clause *InferenceReplayer::runGenerating(GeneratingInferenceEngine *rule,
                                         ClauseStack& context, Clause *goal)
{
  // init problem
  ASS(alg != nullptr);
  Problem p;
  auto ul = UnitList::empty();
  UnitList::pushFromIterator(ClauseStack::Iterator(context), ul);
  p.addUnits(ul);

  env.setMainProblem(&p);

  ClauseStack added;
  addToActive(context, added);

  auto res = rule->generateSimplify(context[0]);

  while(res.clauses.hasNext()){
    //Iterate through generation of all clauses
    res.clauses.next();
  }
  removeFromActive(added);

  // alg->~SaturationAlgorithm();
  Ordering::unsetGlobalOrdering();

  return nullptr;
}

void InferenceReplayer::runForwardsSimp(ForwardSimplificationEngine *rule,
                                        ClauseStack& context, Clause *goal)
{
  Problem p;
  ASS(alg);
  ClauseStack added;
  addToActive(ClauseStack{context[1]}, added);
  Clause *clause = context[0];
  Clause *replacement = nullptr;
  Kernel::ClauseIterator clauses;
  rule->perform(clause, replacement, clauses);
  removeFromActive(added);
  Ordering::unsetGlobalOrdering();
}

/**
 * Put `clauses` into the active container, recording in `added` what actually went in.
 *
 * Two things this is careful about, both of which have crashed an embedded run.
 *
 * Once per clause, not once per premise: an inference can name the same clause twice — a
 * self-resolution, a superposition of a clause with itself — and the caller's stack is
 * the parent list verbatim. `ActiveClauseContainer::add` guards the duplicate with an
 * `ALWAYS` whose check `-DVDEBUG=0` strips, so a second `add` does nothing to the
 * container and fires `addedEvent` anyway: the term indexes take the clause's terms
 * twice, and a single removal leaves half of it behind.
 *
 * And once per *call*: the container may not be empty, because a previous replay may have
 * left something in it, and adding a clause that is already there has the same effect.
 */
void InferenceReplayer::addToActive(const ClauseStack &clauses, ClauseStack &added)
{
  ASS(alg != nullptr);
  // The active container for both halves, so that what is added and what is removed are
  // the same container by construction. Under the DISCOUNT `makeInferenceEngine` forces,
  // it is also `getSimplifyingClauseContainer()`, which is what the simplification paths
  // used to add to; only `RandomAccessClauseContainer` can remove, so naming the active
  // one is what makes a symmetric pair expressible at all.
  ActiveClauseContainer *container = alg->getActiveClauseContainer();
  DHSet<unsigned> seen;
  auto present = container->clauses();
  while (present.hasNext()) {
    seen.insert(present.next()->number());
  }
  for (Clause *c : clauses) {
    if (!seen.insert(c->number())) {
      continue;
    }
    c->setStore(Clause::ACTIVE);
    c->setAge(0);
    container->add(c);
    added.push(c);
  }
}

/**
 * Take back out exactly what `addToActive` put in.
 *
 * Exactly that, and not "everything in the container": removing a clause fires
 * `removedEvent`, and an index asked to remove terms it never inserted walks off the end
 * of its substitution tree. What is in the container and was not added here belongs to
 * whoever put it there.
 */
void InferenceReplayer::removeFromActive(const ClauseStack &added)
{
  ASS(alg != nullptr);
  ActiveClauseContainer *container = alg->getActiveClauseContainer();
  for (Clause *c : added) {
    container->remove(c);
  }
}

void InferenceReplayer::runBackwardsSimp(Inferences::BackwardSimplificationEngine *rule,
                                         ClauseStack& context, Clause *goal)
{
  Problem p;
  ASS(alg != nullptr);
  
  // Backward simplification, so we add the clause to be simplified to the simplifying
  // container
  ClauseStack added;
  addToActive(ClauseStack{context[0]}, added);

  Clause *clause = Clause::fromClause(context[1]);

  Inferences::BwSimplificationRecordIterator simpls;
  rule->perform(clause, simpls);

  while(simpls.hasNext()){
    simpls.next();
  }

  // Put the container back the way it was found, as the other two do. Without this a
  // backward simplification leaves its premise in the active container and the term
  // indexes keep the entries that went in with it, which the next replay to name that
  // clause then doubles.
  removeFromActive(added);

  Ordering::unsetGlobalOrdering();
}

} // namespace Shell
