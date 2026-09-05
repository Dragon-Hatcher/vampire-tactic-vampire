% A non-theorem, and one the twee goal transformation must not turn into a theorem.
%
% `-tgt full` makes a definition for a non-ground subterm of the goal. Here that subterm
% is f(X,X), and the definition has to be `f(X,X) = sF(X)`: a definition of arity one,
% because the term has a variable in it. Introduced with arity zero it says instead that
% f(X,X) is the *same* for every X, which is false, and enough on its own to derive
% p(f(a,a)) and ~p(f(a,a)) from two consistent axioms -- Vampire then reports
% ContradictoryAxioms for a set of axioms that has a two-element model.
%
% q occurs positively as well, or the goal clause is removed as a pure predicate before
% the transformation ever sees it, and the check passes for the wrong reason.
fof(a1, axiom, p(f(a,a))).
fof(a2, axiom, ~p(f(b,b))).
fof(a3, axiom, q(c)).
fof(g,  conjecture, ?[X] : q(f(X,X))).
