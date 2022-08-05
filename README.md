# Initial semantics for substitution skew-monoids 

Compilation: make

## Dependencies

Coq is required. For the interactive mode, the following options should
be given to coqtop: `-noinit -indices-matter -type-in-type -w -notation-overridden`


The UniMath library is required with at least the following packages:
Foundations, MoreFoundations, Combinatorics, Algebra, NumberSystems, 
CategoryTheory.

This was tested with:
- Coq 8.15.1
- UniMath commit version 43dd76c4a0a011afec5e8ed43351baa621c0e482



## Summary 

A detailed summary is available at [`Summary.v`](Summary.v).

## Axioms

The formalization relies on the UniMath library.

There is one admitted result in this work: Theorem 4.7 of Fiore-Saville "List 
object with algebraic structures" (extended version), found in [`Complements.v`](Complements.v).


## Files

The definitions of skew monoidal categories and their monoids is now in UniMath.

By order of dependency:

1. [`Complements.v`](Complements.v): complements, axiomatization of Theorem 4.7
of Fiore-Saville "List object with algebraic structures" (extended version)
2. [`IModules.v`](IModules.v): category of pointed I-modules
3. [`StructuralStrengths.v`](StructuralStrengths.v)
4. [`InitialAlgebraicMonoid.v`](InitialAlgebraicMonoid.v): construction of an 
initial algebraic skew-monoid.
5. [`Summary.v`](Summary.v): a summary of the important definitions and results.



