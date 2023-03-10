Summary
=======

OK this is a bit bare-bones for now, but the idea is that I coded my solution
to the problem of computing the order-type of (L, ≤lex) for L ⊂ Σ\* regular
languages given by DFA.

A solution to this was given in
Stephan Heilbrunner
  An algorithm for the solution of fixed-point equations for infinite words.
    ITA, 14(2):131–141, 1980

(order-types, countable words, same deal more or less, although I guess it
would have been cleaner for me to go for countable words directly I guess)

I vaguely looked at what seems to be the arxiv version of

Markus Lohrey, Christian Mathissen
  Isomorphism of Regular Trees and Words.
    ICALP (2) 2011: 210-221

but used my vagues memories on countable linear orders to solve this myself
actually. Learnt that during my PhD, mostly through

Olivier Carton, Thomas Colcombet, Gabriele Puppis
  An Algebraic Approach to MSO-Definability on Countable linear Orderings.
    J. Symb. Log. 83(3): 1147-1189 (2018)


I am not sure I like very much the solutions in those first two papers in
terms of aesthetics and I am pleased with what I have although it is
inefficient for now.

I put a lot more comments in the source files, which I hope are organized
somewhat OK now. In particular `code/src/RCOEqns`.

Running
=======

Assuming you have `cabal`, do `cd` into `code` and try `cabal run` and
everything should work fine. Then look at `app/Main.hs` and then
`src/Examples.hs` if you are in a hurry to test your own examples I guess.

Abbreviations and notations
===========================

* DFA = Deterministic Finite Automata
* RCO = Regular Countable (linear/total) Orders (or order types)
* 0   = the order type of the empty order
* 1   = the order type of a singleton
* ω   = the order type of the positive integers (ℕ, <)
* -ω  = the order type of the positive integers (ℕ, >) with the order reversed
* η   = the order type of the rationals (ℚ, <)
* middle dot is the lexicographic product of order types
* \+   = the lexicographic sum of order types
* braces are used for finite sets
* Pη  = shuffle of the order types in the set P

TODOs
=====

* Make LSum associative on the nose
* Generalize/clean up by going to countable words directly
* Maybe having a nice web interface to draw automata and get an answer would
be sweet - but generaly a more useful Main.hs would be nice already
* Some visualisation for countable linear orders/countable words? I am not sure
if someone figured that one out...
* Some GADT boilerplate to build automata more easily in that setup
* It would be an interesting exercise to compute a representation for the
initial algebras and not only the carriers I guess
* Look further in the literature to see if this was written down in a palatable
way. In particular stuff related to iteration theories. And probably
Courcelle's papers on the topic.
* Thanks to Haskell's laziness®, evalutating MSO properties (by way of
∘-algebras as discussed in the last reference above) might be substantially
more efficient on examples than computing and displaying the order-type. I had
some boilerplate I had used to start to test this on simple properties
(e.g. "being well-ordered/scattered" or "having a minimal element"), but I lost
it in a crash :( Not very long to redo though.
But ultimately to optimize this further, it would probably be smart to actually
inline the simplification given by ∘-algebras operations while solving the
equations as well.


Questions
=========

* Is there something to be said about this approach yielding parametric initial
algebras vs only initial algebras?
* OK so this means that adding freely initial algebras combinators to the
lawvere theory of the monoid gives you something that quotient to the Lawvere
theory of the regular countable linear orders. Is that quotient trivial?
* The answer to the above question seems to be "yes" if we restrict the
saturation to "affine" functors and the target to scattered countable linear
orders I think? Is there a way of making those restricted notions categorically
respectable? (through PROPs or something?)
* Would putting hash-consing and memoization everywhere with this approach
yield an efficient algorithm for the isomorphism problem?
