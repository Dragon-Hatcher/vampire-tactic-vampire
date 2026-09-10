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
 * @file URResolution.cpp
 * Implements class URResolution.
 */

#include "Lib/DArray.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Lib/DHSet.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/Inference.hpp"

#include "Indexing/Index.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/AnswerLiteralManager.hpp"
#include "Shell/Options.hpp"

#include "URResolution.hpp"

namespace Inferences
{

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

template<bool synthesis>
URResolution<synthesis>::URResolution(SaturationAlgorithm& salg)
: _full(salg.getOptions().unitResultingResolution() == Options::URResolution::FULL),
  _emptyClauseOnly(salg.getOptions().unitResultingResolution() == Options::URResolution::EC_ONLY),
  _selectedOnly(false),
  _unitIndex(salg.getGeneratingIndex<UnitIndexType>()),
  _nonUnitIndex(salg.getGeneratingIndex<NonUnitIndexType>())
{
  ASS_NEQ(salg.getOptions().unitResultingResolution(),  Options::URResolution::OFF);
}

/**
 * Composes @b s with what @b u does to the bank @b bank.
 *
 * The unifiers a unit resulting resolution uses come one at a time and are
 * applied to the literals as they come; nothing keeps what they did to each
 * premise's variables, which is what replaying the step needs.
 */
static void composeInto(Substitution& s, ResultSubstitution* u, bool bank)
{
  Stack<std::pair<unsigned, TermList>> items;
  for (auto item : iterTraits(s.items())) {
    items.push(item);
  }
  for (auto [v, t] : items) {
    s.rebind(v, u->apply(t, bank));
  }
}

/** Makes @b s the identity on @b cl's variables, to compose as unifiers come. */
static void identityOn(Substitution& s, Clause* cl)
{
  s.reset();
  DHSet<unsigned, FnvHash, IdentityHash> vars;
  cl->collectVars(vars);
  for (unsigned v : iterTraits(vars.iterator())) {
    s.bindUnbound(v, TermList(v, false));
  }
}

template<bool synthesis>
struct URResolution<synthesis>::Item
{
  USE_ALLOCATOR(URResolution::Item);

  Item(Clause* cl, bool selectedOnly, URResolution& parent, bool mustResolveAll)
  : _orig(cl), _color(cl->color()), _parent(parent)
  {
    unsigned clen = cl->length();
    _ansLit = synthesis ? cl->getAnswerLiteral() : nullptr;
    _mustResolveAll = mustResolveAll || (selectedOnly ? true : (clen < 2 + (_ansLit ? 1 : 0)));
    unsigned litslen = clen - (_ansLit ? 1 : 0);
    _premises.init(litslen, 0);
    _lits.reserve(litslen);
    unsigned nonGroundCnt = 0;
    for(unsigned i=0; i<clen; i++) {
      if(!(*cl)[i]->ground()) nonGroundCnt++;
      if ((*cl)[i] != _ansLit) {
        _lits.push((*cl)[i]);
      }
    }
    _atMostOneNonGround = nonGroundCnt<=1;
    identityOn(_origSubst, cl);
    _premiseSubsts.ensure(litslen);

    _activeLength = selectedOnly ? cl->numSelected() : litslen;
    ASS_REP2(_activeLength>=litslen-1, cl->toString(), cl->numSelected());
  }

  /**
   * Resolve away @c idx -th literal of the clause. This involves
   * applying the substitution in @c unif to all remaining literals.
   * If @c useQuerySubstitution is true, the query part of the
   * substitution is applied to the literals, otherwise the result
   * part is applied.
   */
  void resolveLiteral(unsigned idx, QueryRes<ResultSubstitutionSP, LiteralClause>& unif, Clause* premise, bool useQuerySubstitution)
  {
    Literal* rlit = _lits[idx];
    _lits[idx] = 0;
    _premises[idx] = premise;
    // What this unifier does to the premise it resolves with, and to everything
    // already collected.
    {
      composeInto(_origSubst, unif.unifier.ptr(), !useQuerySubstitution);
      for (unsigned i = 0; i < _premiseSubsts.size(); i++) {
        if (_premises[i] && i != idx) {
          composeInto(_premiseSubsts[i], unif.unifier.ptr(), !useQuerySubstitution);
        }
      }
      identityOn(_premiseSubsts[idx], premise);
      composeInto(_premiseSubsts[idx], unif.unifier.ptr(), useQuerySubstitution);
    }
    _color = static_cast<Color>(_color | premise->color());
    ASS_NEQ(_color, COLOR_INVALID)

    if (_ansLit && !_ansLit->ground()) {
      _ansLit = unif.unifier->apply(_ansLit, !useQuerySubstitution);
    }
    Literal* premAnsLit = nullptr;
    if (synthesis && premise->hasAnswerLiteral()) {
      premAnsLit = premise->getAnswerLiteral();
      if (!premAnsLit->ground()) {
        premAnsLit = unif.unifier->apply(premAnsLit, useQuerySubstitution);
      }
      if (!_ansLit) {
        _ansLit = premAnsLit;
      } else if (_ansLit != premAnsLit) {
        bool neg = rlit->isNegative();
        Literal* resolved = unif.unifier->apply(rlit, !useQuerySubstitution);
        if (neg) {
          resolved = Literal::complementaryLiteral(resolved);
        }
        _ansLit = AnswerLiteralManager::getInstance()->makeITEAnswerLiteral(resolved, neg ? _ansLit : premAnsLit, neg ? premAnsLit : _ansLit);
      }
    }

    if(_atMostOneNonGround) {
      return;
    }

    unsigned nonGroundCnt = _ansLit ? !_ansLit->ground() : 0;
    unsigned clen = _lits.size();
    for(unsigned i=0; i<clen; i++) {
      Literal*& lit = _lits[i];
      if(!lit) {
        continue;
      }
      lit = unif.unifier->apply(lit, !useQuerySubstitution);
      if(!lit->ground()) {
        nonGroundCnt++;
      }
    }
    _atMostOneNonGround = nonGroundCnt<=1;
  }

  Clause* generateClause() const
  {
    UnitList* premLst = 0;
    Literal* single = 0;
    unsigned clen = _lits.size();
    for(unsigned i=0; i<clen; i++) {
      if(_lits[i]!=0) {
        ASS_EQ(single,0);
        ASS_EQ(_premises[i],0);
        single = _lits[i];
      }
      else {
        Clause* premise = _premises[i];
        ASS(premise);
        UnitList::push(premise, premLst);
      }
    }
    UnitList::push(_orig, premLst);

    Inference inf(GeneratingInferenceMany(InferenceRule::UNIT_RESULTING_RESOLUTION, premLst));
    Clause* res;

    LiteralIterator it = _ansLit ? pvi(getSingletonIterator(_ansLit)) : LiteralIterator::getEmpty();
    // The literal that survives is stated with its variables normalised, so
    // what the premises were bound to is normalised the same way.
    Renaming norm;
    if(single) {
      if (!_ansLit || _ansLit->ground()) {
        norm.normalizeVariables(single);
        single = norm.apply(single);
      }
      res = Clause::fromIterator(concatIters(getSingletonIterator(single), std::move(it)), inf);
    }
    else {
      res = Clause::fromIterator(std::move(it), inf);
    }

    // A variable the surviving literal does not mention is not in the
    // conclusion at all, so it can stand for anything as long as both the
    // clause and the premise resolved with it say the same.
    auto normalised = [&norm](Substitution& s) {
      Substitution renaming;
      Stack<std::pair<unsigned, TermList>> items;
      for (auto item : iterTraits(s.items())) {
        items.push(item);
      }
      for (auto [v0, t] : items) {
        VariableIterator vit(t);
        while (vit.hasNext()) {
          unsigned v = vit.next().var();
          TermList bound;
          if (!renaming.findBinding(v, bound) && norm.contains(v)) {
            renaming.bindUnbound(v, TermList(norm.get(v), false));
          }
        }
      }
      Stack<std::pair<unsigned, TermList>> out;
      for (auto [v, t] : items) {
        out.push({v, SubstHelper::apply(t, renaming)});
      }
      return out;
    };
    // In the order the premises are stated: the clause, then the units, each
    // against the literal of the clause it resolved away.
    InferenceStore::instance()->recordPremiseUse(res, _orig,
      InferenceStore::literalNone, TermList::empty(), 0,
      normalised(const_cast<Item*>(this)->_origSubst));
    for (unsigned i = _premiseSubsts.size(); i-- > 0; ) {
      if (!_premises[i]) {
        continue;
      }
      InferenceStore::instance()->recordPremiseUse(res, _premises[i], i,
        TermList::empty(), 0,
        normalised(const_cast<Item*>(this)->_premiseSubsts[i]));
    }
    return res;
  }

  int getGoodness(Literal* lit)
  {
    return lit->weight() - lit->getDistinctVars();
  }

  /**
   * From among the remaining literals (i.e. those with index at
   * least @c idx), select the one most suitable for resolving
   * (according to the @c getGoodness() function) and move it to
   * the @c idx position (so that it is resolved next).
   */
  void getBestLiteralReady(unsigned idx)
  {
    ASS_L(idx, _activeLength);

    unsigned choiceSize = _activeLength - idx;
    if(choiceSize==1) {
      return;
    }

    unsigned bestIdx = idx;
    ASS(_lits[bestIdx]);
    int bestVal = getGoodness(_lits[bestIdx]);

    for(unsigned i=idx+1; i<_activeLength; i++) {
      ASS(_lits[i]);
      int val = getGoodness(_lits[i]);
      if(val>bestVal) {
        bestVal = val;
        bestIdx = i;
      }
    }
    if(idx!=bestIdx) {
      swap(_lits[idx], _lits[bestIdx]);
    }
  }

  /** If true, we may skip resolving one of the remaining literals */
  bool _mustResolveAll;

  /** All remaining literals except for one are ground */
  bool _atMostOneNonGround;

  /** The original clause we are resolving */
  Clause* _orig;

  Color _color;

  /** Premises used to resolve away particular literals */
  DArray<Clause*> _premises;
  /**
   * What each premise's variables have been bound to, composed as the unifiers
   * came, and normalised as the conclusion is: what replaying the step needs.
   */
  Substitution _origSubst;
  DArray<Substitution> _premiseSubsts;

  /** Unresolved literals, or zeroes at positions of the resolved ones
   *
   * The unresolved literals have the substitutions from other resolutions
   * applied to themselves */
  Stack<Literal*> _lits;

  Literal* _ansLit;

  unsigned _activeLength;
  URResolution& _parent;
};

/**
 * Perform one level of the BFS traversal of possible resolution
 * sequences
 *
 * (See documentation to the @c processAndGetClauses() function.)
 */
template<bool synthesis>
void URResolution<synthesis>::processLiteral(ItemList*& itms, unsigned idx)
{
  typename ItemList::DelIterator iit(itms);
  while(iit.hasNext()) {
    Item* itm = iit.next();
    itm->getBestLiteralReady(idx);
    Literal* lit = itm->_lits[idx];
    ASS(lit);

    if(!itm->_mustResolveAll) {
      Item* itm2 = new Item(*itm);
      itm2->_mustResolveAll = true;
      iit.insert(itm2);
    }

    auto unifs = _unitIndex->getUnifications(lit, true, true);
    while(unifs.hasNext()) {
      auto unif = unifs.next();

      if( !ColorHelper::compatible(itm->_color, unif.data->clause->color()) ) {
        continue;
      }

      Item* itm2 = new Item(*itm);
      itm2->resolveLiteral(idx, unif, unif.data->clause, true);
      iit.insert(itm2);

      if(!_full && itm->_atMostOneNonGround && (!synthesis || !unif.data->clause->hasAnswerLiteral())) {
        /* if there is only one non-ground literal left, there is no need to retrieve all unifications.
           However, this does not hold under AVATAR where different empty clauses may close different
           splitting branches, that's why only "full" URR is complete under AVATAR (see Options::complete)
        */
        break;
      }
    }

    iit.del();
    delete itm;
  }
}

/**
 * Explore possible ways of resolving away literals in @c itm,
 * and from the successful ones add the resulting clause into
 * @c acc. The search starts at literal with index @c startIdx.
 *
 * What we do is a BFS traversal of all possible resolutions
 * on the clause represented in @c itm. In the @c itms list we
 * store all elements of @c i -th level of the search, and a
 * call to the @c processLiteral() function moves us to the next
 * level of the traversal.
 */
template<bool synthesis>
void URResolution<synthesis>::processAndGetClauses(Item* itm, unsigned startIdx, ClauseList*& acc)
{
  unsigned activeLen = itm->_activeLength;

  ItemList* itms = 0;
  ItemList::push(itm, itms);
  for(unsigned i = startIdx; itms && i<activeLen; i++) {
    processLiteral(itms, i);
  }

  while(itms) {
    Item* itm = ItemList::pop(itms);
    ClauseList::push(itm->generateClause(), acc);
    delete itm;
  }
}

/**
 * Perform URR inferences between a newly derived unit clause
 * @c cl and non-unit active clauses
 */
template<bool synthesis>
void URResolution<synthesis>::doBackwardInferences(Clause* cl, ClauseList*& acc)
{
  ASS((cl->size() == 1) || (cl->size() == 2 && cl->hasAnswerLiteral()));

  Literal* lit = (*cl)[0];
  if (lit->isAnswerLiteral()) {
    lit = (*cl)[1];
  }

  auto unifs = _nonUnitIndex->getUnifications(lit, true, true);
  while(unifs.hasNext()) {
    auto unif = unifs.next();
    Clause* ucl = unif.data->clause;

    if( !ColorHelper::compatible(cl->color(), ucl->color()) ) {
      continue;
    }

    Item* itm = new Item(ucl, _selectedOnly, *this, _emptyClauseOnly);
    unsigned pos = UINT_MAX;
    if (!itm->_ansLit) {
      pos = ucl->getLiteralPosition(unif.data->literal);
    } else {
      for (unsigned i = 0; i < itm->_lits.size(); ++i) {
        if (itm->_lits[i] == unif.data->literal) {
          pos = i;
          break;
        }
      }
    }
    ASS(!_selectedOnly || pos<ucl->numSelected());
    swap(itm->_lits[0], itm->_lits[pos]);
    itm->resolveLiteral(0, unif, cl, /* useQuerySubstitution */ false);

    processAndGetClauses(itm, 1, acc);
  }
}

template<bool synthesis>
ClauseIterator URResolution<synthesis>::generateClauses(Clause* cl)
{
  unsigned clen = cl->size();
  if(clen<1) {
    return ClauseIterator::getEmpty();
  }

  TIME_TRACE("unit resulting resolution");

  ClauseList* res = 0;
  processAndGetClauses(new Item(cl, _selectedOnly, *this, _emptyClauseOnly), 0, res);

  if (clen==1 ||
      (synthesis && clen==2 && cl->hasAnswerLiteral())) {
    doBackwardInferences(cl, res);
  }

  return getPersistentIterator(ClauseList::DestructiveIterator(res));
}

template class URResolution<true>;
template class URResolution<false>;

}
