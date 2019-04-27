% CISC 260 a5, Fall 2018

% Note:
% replace %wwrite with write to see trace
% replace write( with %wwrite( to cancel


/*
Q2: Truth Tables

In order to build a truth table for a formula, there are 4 steps:

1) Traverse the formula to find all atomic propositions (constants).

2) Assign all possible combinations of True and False
   to the set of atomic propositions in the formula.

3) Evaluate the formula for each truth value assignment obtained in (2).

4) Use the results of (1-3) to build the table.

In this question, you will implement steps (1-3).
*/

% In our simplified version of classical propositional logic, we have the following
% possible Formulas:
%
% tt                         % truth
% ff                         % falsehood
% and(Formula, Formula)      % conjunction
% implies(Formula, Formula)  % implication
% c(Constant)                % atomic proposition

% Some example constants:
% c(a)
% c(b)
% c(d)
% c(e)
% c(f)
% c(g)
%%%%%%%%%% Prolog allows c(c), but it looks strange.

% Some example formulas you can use to test your functions
formula1( implies( and(c(a), c(b)), c(d))).
formula2( implies( ff, (and( c(a), c(b)))) ).
formula3( implies( and( c(a), c(b)), tt) ).
formula4( and( implies(c(a), and(c(b), c(h))), and(c(e), c(f))) ).
formula5( and( c(a), c(b)) ).
formula6( implies( c(a), c(b) )).
formula7( implies( and(c(a),c(a)), c(b))).

% An Assignment is a list of assign/2s,
%   corresponding to a truth value (i.e. true or false) for each Constant in a formula.
% Example:
%
%   [assign(a, true), assign(b, false)]   assigns true to c(a) and false to c(b)

% A TruthTable is an enumeration of all combinations of truth value assignments
%   for a given formula, paired with the corresponding evaluation of that formula.
% Example:
%
%    truth_table( [truth([assign(a, true)], true)],
%                 [truth([assign(a, false)], false)])
%
% is a truth table for the formula c(a).

nub([],       []).
nub([X | Xs], Ys) :- member(X, Xs), nub(Xs, Ys).
nub([X | Xs], [X | Ys]) :- \+ member(X, Xs), nub(Xs, Ys).

/* Q2a: getCONSTs:
  Traverse a formula and build a list of all constants in the formula, without duplicates.

  getCONSTs(Formula, ListOfConstants)

  Hint: Consider using 'append' and 'nub' in the clauses
  for 'and' and 'implies'.
*/
getCONSTs( tt, []).
getCONSTs( ff, []).
getCONSTs( c(C), [C]).
getCONSTs( and(Q1, Q2), R) :-
    getCONSTs(Q1,R1),getCONSTs(Q2,R2), append(R1,R2,R1R2), nub(R1R2,R).
getCONSTs( implies(Q1, Q2), R) :-
    getCONSTs(Q1,R1),getCONSTs(Q2,R2), append(R1,R2,R1R2), nub(R1R2,R).


% Q2b: oneAssignment
%
is_bool(true).
is_bool(false).

oneAssignment([], []).
oneAssignment([C | Cs], [assign(C, B) | Cs_Assignment]) :-
  is_bool(B), oneAssignment(Cs,Cs_Assignment).

% getAssignments:
%  Build a list of all possible truth assignments for a set of constants
getAssignments([], [[]]).
getAssignments([C | Cs], Result) :-
  getAssignments(Cs, Cs_Assignments),
  addToFront( assign(C, true),  Cs_Assignments, True_Assignments),
  addToFront( assign(C, false), Cs_Assignments, False_Assignments),
  append( True_Assignments, False_Assignments, Result).

% addToFront x xss
% Add the element x to the start of each list in xss.
% Example:
%   addToFront( 1, [[2,3], [], [4,5,6]],  [[1,2,3], [1], [1,4,5,6]]).
% addToFront :: a -> [[a]] -> [[a]]
addToFront( _, [], []).
addToFront( X, [Xs | Xss], [[X | Xs] | RecursiveResult]) :-
    addToFront( X, Xss, RecursiveResult).


% evalF (Formula, Assignment, Value)
%  Evaluate a formula with a particular truth assignment,
%   returning the resulting boolean value
evalF( tt,              _,  true).
evalF( ff,              _,  false).
evalF( c(C),            As, Value) :- member(assign(C, Value), As).

evalF( and(Q1, Q2),     As, true)  :- evalF( Q1, As, true),
                                      evalF( Q2, As, true).
evalF( and(Q1, _),      As, false) :- evalF( Q1, As, false).
evalF( and(_, Q2),      As, false) :- evalF( Q2, As, false).

/* Q2d: Add rules for
evalF( implies(..., ...), As, ...) :- ...
*/
evalF( implies(Q1,Q2),  As, true)  :- evalF( Q1, As, true),
                                      evalF( Q2, As, true).
evalF( implies(Q1,_),   As, true)  :- evalF( Q1, As, false).


% buildTable:
%  Build a truth table for a given formula.
%  You can use this function to help check your definitions
%  of getCONSTs, getAssignments and evalF.
% buildTable :: Formula -> TruthTable
% buildTable q =
buildTable( Q, truth_table( TruthTable)) :-
  getCONSTs(Q, Consts),
  getAssignments( Consts, Assignments),
  format('formula: ~p ~n', Q),
  zip_eval( Q, Assignments, TruthTable).

format_assignment( [], '').
format_assignment( [assign(C, V) | As], ConcatenatedString) :-
  concat( C,  ' = ', S1),
  concat( S1, V,     S2),
  concat( S2, ', ',  S3),
  format_assignment( As, String),
  concat(S3, String, ConcatenatedString).

zip_eval( _, [], [] ).
zip_eval( Q, [Assignment | Rest],
              [truth(Assignment, V) | Result] ) :-
    evalF(Q, Assignment, V),
    format_assignment( Assignment, String),
    format('~p:   ~p ~n', [String, V]),
    zip_eval( Q, Rest, Result).


/*
Q3: Tiny Theorem Prover
*/

% append3( Ctx1, Formula, Ctx2, Ctx)
%
% append3 takes:
%  a list Ctx1
%  an element Formula
%  a list Ctx2
% and "returns" the result of appending all of them,
% similar to Haskell   Ctx = Ctx1 ++ (formula : Ctx2)
%                 or   Ctx = Ctx1 ++ [formula] ++ Ctx2

append3( [], Formula, Ctx2, [Formula | Ctx2]).

append3( [X | Xs], Formula, Ctx2, [X | Result]) :-
  append3( Xs, Formula, Ctx2, Result).

% We will use append3 "backwards":
% instead of taking concrete Ctx1, Formula, Ctx2
% provided by the user, we take a concrete *result* Ctx
% and use append3 to "split up" the Ctx.


% a context is a list of Formulas, representing assumptions

% prove(Ctx, P):
%   true if, assuming everything in Ctx is true,
%    the formula p is true according to the rules given in a3.pdf.

% This is the cool part:
%  *each rule in the figure from a3 becomes a Prolog clause*.
% There is no "problem solving" where someone (like the instructor)
%  figures out an algorithm that first "decomposes" the context,
%  then tries the -Right rules.
%  (That also requires figuring out how to decompose the context,
%  using an accumulator.)
% In Prolog, we can write a clause for each logical rule,
%  and it "just works".

% rule 'UseAssumption'
prove( Ctx, P) :-
  %wwrite('PREMISE/ASSUME~: '),
  %wwrite(' Proving '), write(P),
  %wwrite(' Using '), write(Ctx), write(' \n '),
  member( P, Ctx).

% rule 'TT-Right'
prove( _,   tt).

/*
Q3a.
  Write Prolog clauses that correspond to the rules
  AND-Right
  and
  IMPLIES-Right.
*/

% rule 'AND-Right'
% CONCLUSION:  Ctx |- and(Q1, Q2)
prove( Ctx, and( Q1,Q2)) :-
  %wwrite('AND_RIGHT      : '),
  %wwrite(' Proving '), write(' and( '), write(Q1),write(','),write(Q2),write(') '),
  %wwrite(' Using '), write(Ctx), write(' \n '),
  prove( Ctx, Q1), prove( Ctx, Q2).

% rule 'IMPLIES-Right'
% CONCLUSION:  Ctx |- implies(P, Q)
prove( Ctx, implies( P,Q)):-
  %wwrite('IMPLIES_RIGHT  : '),
  %wwrite(' Proving '), write(' implies( '), write(P),write(','),write(Q),write(') '),
  %wwrite(' Using '), write(Ctx), write(' \n '),
  prove( [P | Ctx], Q).

% rule 'AND-Left'
% CONCLUSION:  Ctx1 ++ [and(P1, P2)] ++ Ctx2 |- Q
prove( Ctx, Q) :-
  %wwrite('AND_LEFT       : '),
  %wwrite(' Proving '), write(Q),write(' Using '), write(Ctx), write(' \n '),
  append3( Ctx1, and(P1, P2), Ctx2, Ctx),
  append( Ctx1, [P1 | [P2 | Ctx2]], CtxP12),  % CtxP12 = Ctx1 ++ [P1, P2] ++ Ctx2
  prove( CtxP12, Q).                          % CtxP12 |- q

% rule 'IMPLIES-Left'
% CONCLUSION:  Ctx1 ++ [implies(P1, P2)] ++ Ctx2 |- Q
prove( Ctx, Q) :-
  %wwrite('IMPLIES_LEFT   : '),
  %wwrite(' Proving '), write(Q),write(' Using '), write(Ctx), write(' \n '),
  append3( Ctx1, implies(P1, P2), Ctx2, Ctx),
  append(Ctx1,Ctx2,CtxForP1),
  prove( CtxForP1, P1),
  append( Ctx1, [P2| Ctx2], CtxP2),
  prove( CtxP2, Q).

/*
  ?- prove([implies(c(b), c(h))], implies(c(b), c(h))).
  true
  ?- prove([implies(c(b), c(d))], implies(and(c(b), c(b)), c(d))).
  true
  ?- prove([implies(and(c(b), c(e)), c(d))], implies(c(b), c(h))).
  false
  ?- prove([and(and(c(a), c(b)), and(c(d), (c(e))))], c(d)).
  true
*/

/*
  Q4:
  Add clauses for 'or'.
*/
prove( Ctx, Q) :-
  %wwrite('OR_I           : '),
  %wwrite(' Proving '), write(Q),write(' Using '), write(Ctx), write(' \n '),
  append3( Ctx1, or(P1, _), Ctx2, Ctx),
  append( Ctx1, [P1 | Ctx2], CtxP12),
  prove( CtxP12, Q).

prove( Ctx, Q) :-
  %wwrite('OR_II          : '),
  %wwrite(' Proving '), write(Q),write(' Using '), write(Ctx), write(' \n '),
  append3( Ctx1, or(_, P2), Ctx2, Ctx),
  append( Ctx1, [P2 | Ctx2], CtxP12),
  prove( CtxP12, Q).

/* Bonus:
   Develop rules for 'not',
   then implement them.
*/
