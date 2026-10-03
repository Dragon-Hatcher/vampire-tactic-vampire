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
 * @file FlatTerm.cpp
 * Implements class FlatTerm.
 */

#include <cstring>

#include "Lib/Allocator.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Timer.hpp"

#include "SortHelper.hpp"
#include "Term.hpp"

#include "FlatTerm.hpp"

namespace Kernel
{

using namespace Lib;

/**
 * Allocate a FlatTerm object having @b num entries.
 */
void* FlatTerm::operator new(size_t sz,unsigned num)
{
  ASS_GE(num,0);
  ASS_EQ(sz, sizeof(FlatTerm));

  //one entry is already accounted for in the size of the FlatTerm object
  size_t size = sizeof(FlatTerm);
  if (num > 0) {
    size += (num-1)*sizeof(Entry);
  }

  return ALLOC_KNOWN(size,"FlatTerm");
}

/**
 * Destroy the FlatTerm object
 */
void FlatTerm::destroy()
{
  ASS_GE(_capacity,_length);

  //one entry is already accounted for in the size of the FlatTerm object
  size_t size = sizeof(FlatTerm);
  if (_capacity > 0) {
    size += (_capacity-1)*sizeof(Entry);
  }

  DEALLOC_KNOWN(this, size,"FlatTerm");
}

template<bool mightBeLiteral>
size_t FlatTerm::getEntryCount(Term* t)
{
  if constexpr (mightBeLiteral) {
    //FUNCTION_ENTRY_COUNT entries per function and one per variable
    if (t->isLiteral() && static_cast<Literal*>(t)->isEquality()) {
      // we add the type to the flat term for equalities as an extra,
      // which requires some additional calculation
      auto sort = SortHelper::getEqualityArgumentSort(static_cast<Literal*>(t));
      unsigned numVarOccs = t->numVarOccs();
      if (!t->isTwoVarEquality()) {
        // in case of non-two-var equalities, the variables in
        // the type are not counted by Term::numVarOccs
        numVarOccs += sort.isVar() ? 1 : sort.term()->numVarOccs();
      }
      // the weight is corrected to be conservative in the
      // monomorphic case, we uncorrect it by adding 1
      return (t->weight()+1)*FUNCTION_ENTRY_COUNT-(FUNCTION_ENTRY_COUNT-1)*numVarOccs;
    }
  } else {
    ASS(!t->isLiteral());
  }
  return t->weight()*FUNCTION_ENTRY_COUNT-(FUNCTION_ENTRY_COUNT-1)*t->numVarOccs();
}

/**
 * Heartbeats for flattening, and for copying, @b entries entries: the work
 * is proportional to the size of the term, and a term large enough to take
 * milliseconds to flatten is one a strategy can otherwise spend its whole
 * budget on -- forward subsumption flattens every literal of every clause it
 * is asked about -- while counting nothing. Whole multiples only, so the many
 * small terms cost what they did.
 */
static const size_t ENTRIES_PER_CREATE_BEAT = 768;
static const size_t ENTRIES_PER_COPY_BEAT = 6144;

FlatTerm* FlatTerm::create(TermList t)
{
  return create(t, nullptr);
}

FlatTerm* FlatTerm::create(TermList t, FlatTerm* reuse)
{
  size_t entries = t.isVar() ? 1 : getEntryCount</*mightBeLiteral=*/true>(t.term());
  Timer::beat(entries / ENTRIES_PER_CREATE_BEAT);
  FlatTerm* res;
  if (reuse && reuse->_capacity >= entries) {
    res = reuse;
    res->_length = entries;
  } else {
    if (reuse) {
      reuse->destroy();
    }
    res = new(entries) FlatTerm(entries);
  }

  size_t pos = 0;
  pushTerm</*mightBeLiteral=*/true>(res->_data, pos, TermList(t));
  ASS_EQ(entries, pos);

  return res;
}

FlatTerm* FlatTerm::create(TermStack ts)
{
  size_t entries=0;
  for (auto& tl : ts) {
    entries += tl.isVar() ? 1 : getEntryCount</*mightBeLiteral=*/true>(tl.term());
  }
  Timer::beat(entries / ENTRIES_PER_CREATE_BEAT);

  FlatTerm* res=new(entries) FlatTerm(entries);
  size_t fti=0;

  for (auto& tl : ts) {
    pushTerm</*mightBeLiteral=*/true>(res->_data, fti, tl);
  }
  ASS_EQ(fti, entries);

  return res;
}

/**
 * The entries of @b src[0, len) that hold anything, copied to the same places
 * in @b dst: a function not yet expanded is its three entries and then room
 * its expansion will fill, written from the term itself, so the room is not
 * copied. What a flat term is made with is mostly such room.
 */
void FlatTerm::copyWritten(Entry* dst, const Entry* src, size_t len)
{
  size_t pos = 0;
  while (pos < len) {
    switch (src[pos]._tag()) {
      case VAR:
        dst[pos] = src[pos];
        pos++;
        break;
      case FUN_UNEXPANDED:
        ASS_EQ(src[pos+2]._tag(), FUN_RIGHT_OFS);
        memcpy(&dst[pos], &src[pos], FUNCTION_ENTRY_COUNT*sizeof(Entry));
        pos += src[pos+2]._number();
        break;
      default:
        ASS_EQ(src[pos]._tag(), FUN);
        // expanded: its arguments follow it
        memcpy(&dst[pos], &src[pos], FUNCTION_ENTRY_COUNT*sizeof(Entry));
        pos += FUNCTION_ENTRY_COUNT;
        break;
    }
  }
  ASS_EQ(pos, len);
}

FlatTerm* FlatTerm::copy(const FlatTerm* ft)
{
  return copy(ft, nullptr);
}

FlatTerm* FlatTerm::copy(const FlatTerm* ft, FlatTerm* reuse)
{
  size_t entries=ft->_length;
  Timer::beat(entries / ENTRIES_PER_COPY_BEAT);
  FlatTerm* res;
  if (reuse && reuse->_capacity >= entries) {
    res = reuse;
    res->_length = entries;
  } else {
    if (reuse) {
      reuse->destroy();
    }
    res = new(entries) FlatTerm(entries);
  }
  copyWritten(res->_data, ft->_data, entries);
  return res;
}

void FlatTerm::swapCommutativePredicateArguments()
{
  // expand the top-level to get rid of unknown arguments
  (*this)[0].expand();

  ASS_EQ((*this)[0]._tag(), FUN);
  ASS_EQ((*this)[0]._number()|1, 1); //as for now, the only commutative predicate is equality

  ASS((*this)[1]._term()->isLiteral());
  auto lit = static_cast<Literal*>((*this)[1]._term());
  ASS(lit->isEquality());

  auto getLen = [this](size_t start) -> unsigned {
    if ((*this)[start]._tag() == FUN || (*this)[start]._tag() == FUN_UNEXPANDED) {
      ASS_EQ((*this)[start+2]._tag(), FUN_RIGHT_OFS);
      return (*this)[start+2]._number();
    }
    ASS_EQ((*this)[start]._tag(), VAR);
    return 1;
  };

  size_t firstStart = 3;
  auto sort = SortHelper::getEqualityArgumentSort(lit);
  firstStart += sort.isVar() ? 1 : getEntryCount</*mightBeLiteral=*/false>(sort.term());

  size_t firstLen = getLen(firstStart);

  size_t secStart = firstStart+firstLen;
  size_t secLen = getLen(secStart);

  ASS_EQ(secStart+secLen,_length);

  // Each argument is moved by what it holds (`copyWritten`), through a buffer
  // holding both: they may overlap where they end up.
  static DArray<Entry> buf;
  buf.ensure(firstLen + secLen);
  copyWritten(buf.array(), &_data[secStart], secLen);
  copyWritten(buf.array() + secLen, &_data[firstStart], firstLen);
  copyWritten(&_data[firstStart], buf.array(), secLen);
  copyWritten(&_data[firstStart + secLen], buf.array() + secLen, firstLen);
}

void FlatTerm::Entry::expandUnexpanded()
{
  ASS_EQ(_tag(), FUN_UNEXPANDED);
  ASS_EQ(this[1]._tag(), FUN_TERM_PTR);
  ASS_EQ(this[2]._tag(), FUN_RIGHT_OFS);
  Term* t = this[1]._term();
  size_t pos = FlatTerm::FUNCTION_ENTRY_COUNT;

  // If literal is equality, we add a type argument
  // to properly match with two variable equalities.
  // This has to be done also in the code tree.
  if (t->isLiteral() && static_cast<Literal*>(t)->isEquality()) {
    pushTerm</*mightBeLiteral=*/false>(this, pos, SortHelper::getEqualityArgumentSort(static_cast<Literal*>(t)));
  }

  for (unsigned i = 0; i < t->arity(); i++) {
    pushTerm</*mightBeLiteral=*/false>(this, pos, *t->nthArgument(i));
  }
  ASS_EQ(pos,this[2]._number());
  _setTag(FUN);
}

};
