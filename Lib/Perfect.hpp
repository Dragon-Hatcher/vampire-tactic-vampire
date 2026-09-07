/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __UNIQUE_SHARED_HPP__
#define __UNIQUE_SHARED_HPP__

#include <functional>
#include "Lib/Reset.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/Sort.hpp"

namespace Lib {

#define DEBUG(...) // DBG(__VA_ARGS__)
struct PerfectPtrComparison ;
struct PerfectIdComparison ;

/** 
 * Smart pointer for perfectly sharing objects.
 *
 * This means that all objects of type T that are structurally equal, will be represented by the same pointer Perfect<T>.
 * This makes equality comparisons, hashing, and copying constant time operations.
 *
 * The type parameter DfltComparison defines how two objects of this type should be compared in operator<, operator==, 
 * and std::hash. Available options are:
 * - PerfectIdComparison : deterministic, an id is addigned to each term
 * - PerfectPtrComparison: indeterministic, pointers are compared
 *
 * T is required to be comparable with `bool operator==(const T&, const T&)`, and hashable with `std::hash<T>`.
 */
template<class T, class DfltComparison = PerfectIdComparison>
class Perfect 
{
  using IdMap = Map<const T*, Perfect, DerefPtrHash<StlHash>>;

  unsigned _id;
  const T* _ptr;
  static IdMap _ids;
  /** Which signature `_ids` was filled against; see `intern`. */
  static unsigned _gen;
  /** Monotonic id source; never reset, so ids cannot collide across generations. */
  static unsigned _nextId;

  Perfect(unsigned id, const T* ptr) : _id(id), _ptr(ptr) {}

  /**
   * The memo lookup, with the memo dropped when the signature has been replaced.
   *
   * `_ids` is a process-global cache of `T`s, and the `T`s that matter here --
   * `Polynom`, `MonomFactors` -- hold `TermList`s from the term-sharing table and
   * functor numbers from the signature. Embedded Vampire (`Lib::resetGlobalState`)
   * builds a new signature per run, so an entry cached under an earlier one hands back
   * a term whose functor indexes past the end of `Signature::_funs`. That surfaces far
   * from here: `Inferences::cancelAdd` denormalises the cached polynomial, and
   * `Literal::createEquality` then asks `SortHelper` for its sort and dereferences a
   * garbage `Symbol*`.
   *
   * Dropping the map leaks the `T`s it owned. That is what perfect sharing does anyway
   * -- nothing ever freed them -- and the allocator keeps its pools across runs by
   * design; see `docs/vampire-global-state.md`.
   */
  static Perfect intern(T elem)
  {
    if (_gen != Lib::signatureGeneration()) {
      _ids.reset();
      _gen = Lib::signatureGeneration();
    }
    return _ids.tryGet(&elem).toOwned()
      .unwrapOrElse([&](){
          // `_nextId++`, not `_ids.size()`. The id is what `PerfectIdComparison`
          // compares by, and dropping the map above resets its size -- so ids would
          // restart from 0 and a value interned before the reset would compare *equal*
          // to an unrelated one interned after it. Two distinct `Polynom`s comparing
          // equal does not crash; it makes normalisation disagree with itself, and the
          // symptom is a strategy that the binary finishes in 0.018s running for over a
          // minute embedded. A counter that only goes up costs nothing and cannot
          // collide.
          auto entry = Perfect(_nextId++, new T(std::move(elem)));
          _ids.insert(entry._ptr, entry);
          return entry;
        });
  }

public:
  /** 
   * If an equal object to elem exists, a pointer to that object is returned.
   * Otherwise elem is moved to the heap, and a pointer to that heap location is returned.
   */
  explicit Perfect(T elem) : Perfect(intern(std::move(elem))) { }

  /** copy constructor. Constant time. */
  Perfect(Perfect const& t) : _id(t._id), _ptr(t._ptr) {  }

  /** default constructor. for this T must be default-constructible itself. */
  Perfect() : Perfect(T()) {}

  template<class U, class C> friend bool operator==(Perfect<U, C> const& l, Perfect<U, C> const& r);

  /** dereferencing the smart pointer */
  T const* operator->() const& { return _ptr; }
  T const& operator*() const& { return *_ptr; }

  friend std::ostream& operator<<(std::ostream& out, const Perfect& self) 
  { return out << *self; }

  friend struct std::hash<Perfect<T, DfltComparison>>;

  friend struct PerfectPtrComparison;
  friend struct PerfectIdComparison;

  Lib::Comparison compare(Perfect const& rhs) const 
  { return DfltComparison::compare(*this, rhs); }
  IMPL_COMPARISONS_FROM_COMPARE(Perfect);
  IMPL_EQ_FROM_COMPARE(Perfect);

  unsigned defaultHash () const { return DfltComparison::template defaultHash<DefaultHash >(*this); }
  unsigned defaultHash2() const { return DfltComparison::template defaultHash<DefaultHash2>(*this); }

}; // class Perfect


/** instantiating the cache */
template<class T, class Cmp> typename Perfect<T, Cmp>::IdMap Perfect<T, Cmp>::_ids;
/** 0, so that the first use always misses and refills against the live signature. */
template<class T, class Cmp> unsigned Perfect<T, Cmp>::_gen = 0;
template<class T, class Cmp> unsigned Perfect<T, Cmp>::_nextId = 0;

struct PerfectPtrComparison 
{
  template<class T, class Cmp>
  static Lib::Comparison compare(const Perfect<T, Cmp>& lhs, const Perfect<T, Cmp>& rhs)
  { return DefaultComparator::compare((size_t)lhs._ptr, (size_t)rhs._ptr); }

  template<class T, class Cmp>
  static bool equals(const Perfect<T, Cmp>& lhs, const Perfect<T, Cmp>& rhs) 
  { return compare(lhs, rhs) == Comparison::EQUAL; }

  template<class T, class Cmp>
  static size_t hash(Lib::Perfect<T, Cmp> const& self) 
  { return std::hash<size_t>{}((size_t)self._ptr); }

  template<class DH, class T, class Cmp> 
  static size_t defaultHash(Lib::Perfect<T, Cmp> const& self) 
  { return DH::hash((size_t)self._ptr); }
};


struct PerfectIdComparison 
{

  template<class T, class Cmp>
  static Lib::Comparison compare(const Perfect<T, Cmp>& lhs, const Perfect<T, Cmp>& rhs)
  { return DefaultComparator::compare(lhs._id, rhs._id); }

  template<class T, class Cmp>
  static bool equals(const Perfect<T, Cmp>& lhs, const Perfect<T, Cmp>& rhs) 
  { return compare(lhs, rhs) == Comparison::EQUAL; }

  template<class T, class Cmp>
  static size_t hash(Lib::Perfect<T, Cmp> const& self) 
  { return std::hash<unsigned>{}(self._id); }

  template<class DH, class T, class Cmp> 
  static size_t defaultHash(Lib::Perfect<T, Cmp> const& self) 
  { return DH::hash(self._id); }
};


/** function to create a Perfect<T> ergonomically (with the help of type deduction) */
template<class T, class Cmp = PerfectIdComparison> 
Perfect<T, Cmp> perfect(T t) 
{ return Perfect<T, Cmp>(std::move(t)); } } // namespace Lib

template<class A, class B, class Cmp> 
auto operator*(A const& l, Perfect<B, Cmp> const& r) 
{ return perfect(l * (*r)); }

template<class A, class B> 
auto operator*(Perfect<A> const& l, B const& r) 
{ return perfect((*l) * r); }

template<class A, class B> 
auto operator*(Perfect<A> const& l, Perfect<B> const& r) 
{ return perfect((*l) * (*r)); }

template<class A> 
auto operator-(Perfect<A> const& x) 
{ return perfect(-(*x)); }


template<class T, class Cmp> struct std::hash<Lib::Perfect<T, Cmp>> 
{
  size_t operator()(Lib::Perfect<T, Cmp> const& self) const 
  { return Cmp::hash(self); }
};


template<class T, class Cmp> struct std::less<Lib::Perfect<T, Cmp>> 
{
  bool operator()(Lib::Perfect<T, Cmp> const& lhs, Lib::Perfect<T, Cmp> const& rhs) const 
  { return Cmp{}(lhs, rhs); }
};


#undef DEBUG
#endif // __UNIQUE_SHARED_HPP__
