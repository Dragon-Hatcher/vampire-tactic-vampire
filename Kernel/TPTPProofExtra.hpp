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
 * @file TPTPProofExtra.hpp
 * The TPTP proof printed by `--proof tptp --proof_extra full`.
 *
 * This is the usual TPTP proof, extended with what each inference did to its
 * premises: the literal and subterm it acted on, the unifier, where each
 * premise literal went in the conclusion, and anything else the rule recorded
 * in the InferenceStore. It is meant to be read by a program.
 *
 * Every line is a TPTP annotated formula, except for two leading comments:
 *
 *   % VAMPIRE format: 2
 *   % VAMPIRE refutation: fN       the step that is the refutation
 *
 * Declarations. Every sort and uninterpreted symbol gets a TFF type
 * declaration, named as in vampire's TPTP proofs. `created(C)` is the symbol's
 * creation index, counted over functions and predicates together; a symbol
 * introduced by vampire is created after the symbols it is built from.
 *
 *   tff(type_def_I, type, s: $tType).
 *   tff(func_def_I, type, f: (s1 * s2) > s, unknown, [created(C)]).
 *   tff(pred_def_I, type, p: s1 > $o, unknown, [created(C), pure(V,K)]).
 *   tff(split_def_I, type, spl0_3: $o, unknown, [split_name]).
 *
 * `pure(V,K)`: pure predicate removal replaced the predicate by the truth
 * value V, and it was the Kth predicate found pure. A split name is a
 * propositional symbol naming an AVATAR component; split names share a prefix
 * that no other symbol starts with, and are marked by `split_name`.
 * TPTP's own sorts, numerals and operations are not declared. Numerals are
 * written as in TPTP, `3` and `1/3`, except that reals are written
 * `$to_real(1/3)`. ALASCA's multiplication by a numeral k has no TPTP name, so
 * it is named by a fresh prefix followed by the sort and k, and declared with
 * `[created(C), lin_mul($fot(k))]`.
 *
 * Steps, ordered by vampire's unit number (so premises come first) and named
 * by it:
 *
 *   tcf(fN, Role, ! [X0: s0, X1: s1] : (L1 | L2 | ~spl0_3), Source).
 *   tff(fN, Role, Formula, Source).
 *
 * `tcf` is a clause and `tff` a formula. A clause is quantified over its
 * variables in the order SortHelper collects their sorts, and its literals
 * are in vampire's order, which is what the records index. A clause derived
 * under AVATAR split names is written with the negations of those names after
 * its own literals. `$false` is the empty clause. In a formula, `~p` is a
 * negative literal and `~ (f)` a negation; a split name is a literal of its
 * own. Polarity flipping makes vampire use `p` for `~p` for the chosen
 * predicates; steps from the flipping on are written with those literals
 * turned back, so every formula reads in the problem's signature and the
 * flipping step restates its premise.
 *
 * Sources. An input formula has `file('path', name)`, or `file('unknown')`
 * when it has no name. A step without premises has
 * `introduced(definition, [rule, ...], [])` if it introduced a symbol and
 * `introduced(theory, [rule, ...], [])` otherwise. Any other step has
 * `inference(rule, [...], [premises])`. A rule is vampire's rule name with
 * spaces replaced by `_`. The information list starts with `status(esa)` for
 * skolemisation and `status(cth)` for a negated conjecture, as in vampire's
 * TPTP proofs, followed by these items where applicable (for an input formula
 * they go in the annotation's useful info instead):
 *
 *   new_symbols(skolem|definition, [f, ...])   the symbols introduced; a
 *                     split name gets a list of its own
 *   skolemize(X, t)   the existential variable replaced by skolemisation, and
 *                     the skolem term replacing it
 *   variable_sorts([X0:s, ...])  sorts of a formula's variables, in the order
 *                     SortHelper collects them
 *   bound_sorts([X3:s, ...])     sorts of variables that occur in the
 *                     step's premise uses (unifier images, terms acted on)
 *                     but not in the step itself
 *   input_name(n)     the input name of a non-input step
 *   sat_premise(sN)   the propositional refutation the step depends on
 *   namings([naming(p, [X1, ...], F)])  a predicate introduced by
 *                     clausification to name formula F, applied to the
 *                     listed variables
 *   gen_clause(gN)    the generalised clause the clause was produced from
 *   choices([choice([I, ...], K)])  for each conjunction the clausifier went
 *                     into, the conjunct K it took; the conjunction is given
 *                     by its path of subformula indices in the premise
 *                     formula, so equal conjunctions at different positions
 *                     are distinct
 *   congruences([...])  the derivation of a congruence-closure conflict,
 *                     steps numbered from 0:
 *                     input(L), the equality denied by literal L;
 *                     congruence($fot(a), $fot(b), [S, ...]), a = b from one
 *                     step per argument pair, `none` for identical arguments;
 *                     trans(S1, S2); symm(S);
 *                     goal_equality(L, S), literal L is the equality proved
 *                     by step S (`none` only if its sides are identical);
 *                     goal_literals(L1, L2, [S, ...]), literal L1 denies and
 *                     L2 asserts the same atom, with arguments as above
 *   constraints([L, ...])  the literals that are the disequalities left by
 *                     an abstracting unifier
 *   splitting_name(L) the literal of a general splitting step that is the
 *                     name it introduced
 *   literal_factors([Q, ...])  for a literal-wise simplification that scaled
 *                     a literal, per premise literal the rational Q such that
 *                     the difference of its sides is Q times that of its image
 *   procedure(P)      the procedure of a literal-wise simplification
 *                     (InferenceStore::LiteralProcedure): theory_normalization,
 *                     interpreted_evaluation, interpreted_evaluation_normalizing,
 *                     polynomial_evaluation, push_unary_minus,
 *                     alasca_normalization, cancellation, generalization, viras
 *                     or inequality_predicate_normalization
 *   introduced([lit(L, S), ...])  the literals the step built rather than
 *                     carried over, in the order built, each with the literal
 *                     of the first premise it was built from, or `none`
 *   variant(N)        which of the shapes its rule builds this one is
 *   introduced_terms([T, ...])  terms the step built, `$fot(t)` or `none`
 *
 * Literals are indexed by their position in the clause as written. A formula
 * in a record carries the sorts of its free variables:
 * `scoped([X0:s, ...], $tff(F))`.
 *
 * Premises. Each premise is followed by the step's records about it, as TPTP
 * parent details `fN:[...]`: one `use(...)` per recorded use, or a bare `use`
 * when the use has no items. The Jth occurrence of a premise among the parents
 * carries the Jth use recorded for it, and its last occurrence carries any
 * remaining uses (an AVATAR split clause uses a component's definition once
 * per renaming of the component it contains). A use holds:
 *
 *   literal(L)        the literal acted on
 *   term($fot(t))     the term acted on within that literal
 *   bind(X, $fot(t))  the unifier's image of premise variable X, a term over
 *                     the conclusion's variables
 *   rewrites_whole_premise   the term was rewritten throughout the premise
 *   virtual(epsilon|plus_infinity|minus_infinity)  VIRAS's virtual term
 *   negated           the premise states the term negated
 *   other($fot(t)), factor($fot(t))   a second term acted on, and the
 *                     numeral the term was scaled by
 *   placed([E, ...])  where each premise literal went in the conclusion: its
 *                     index, `turned(E)` if the equation's sides were swapped,
 *                     `rewritten(E)` if the inference rewrote it rather than
 *                     carried it over, `none` if it was dropped. For a
 *                     literal-wise simplification, the recorded image of each
 *                     literal.
 *
 * A placement without a recorded use stands alone, `placed([...])`.
 *
 * Propositional clauses, from the problem AVATAR passes to its SAT solver:
 *
 *   cnf(sN, plain, (spl0_1 | ~spl0_2), inference(rat, [], [sM, ...])).
 *   cnf(sN, plain, (spl0_1 | spl0_2), inference(sat_conversion, [order([K, ...])], [fN])).
 *
 * The first is derived by the solver from premises listed in the order used;
 * each premise has all literals but one falsified by the preceding ones. The
 * second is the propositional abstraction of a first-order clause; since the
 * abstraction sorts its literals, `order` gives for each clause literal the
 * index of the propositional literal it became.
 *
 * New clausifier steps. NewCNF works on generalised clauses (disjunctions of
 * signed subformulas, plus bindings for the variables they quantify), rewriting
 * one subformula at a time; these are not vampire units. Each is written as a
 * step `gN` just before the first step that uses it:
 *
 *   tff(gN, plain, ! [X0: s, ...] : (X2 != t | F1 | ~ (F2) | ...),
 *       inference(clausification_step, [How, position(K), bound([X2, ...]),
 *       replacement([pos(F) | neg(F), ...]), placed([P, ...])], [gM])).
 *
 * The statement starts with a guard `X != t` for each bound variable, in the
 * order of `bound`, followed by the signed subformulas: a negative one is
 * written `~ (F)`, a positive one is never a negation. It is always a single
 * parenthesised disjunction with one disjunct per guard and per subformula; a
 * subformula that is itself a disjunction has its own parentheses, so
 * `((a | b))` is the single subformula `a | b` and `(a | b)` two subformulas.
 * `How` is `introduced` for the initial clause, `extended` when a position was
 * replaced by the replacement, `replaced` when it was rewritten in place and
 * `named` when it was rewritten in place by a name. `position` is the position
 * replaced in the parent. Each placement is where a literal pushed by the step
 * went, `turned(K)` if `~f` was stored as `f` with the opposite sign.
 * An initial clause is inferred from the formula being clausified, which is
 * its single subformula, or else is a definition introduced by the
 * clausifier, `introduced(definition, [clausification_step, ...], [])`.
 * A clause produced by the clausifier refers to its last state with
 * `gen_clause(gN)`.
 */

#ifndef __TPTPProofExtra__
#define __TPTPProofExtra__

#include <ostream>

#include "Forwards.hpp"

namespace Kernel {

/** Print the proof of @b refutation in the format described above. */
void outputTPTPProofExtra(std::ostream& out, Unit* refutation);

}

#endif
