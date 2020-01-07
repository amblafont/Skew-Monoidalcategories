# Initial semantics for substitution skew-monoids 

Compilation: make

## Dependencies

Coq is required.

The UniMath library is required with at least the following packages:
Foundations, MoreFoundations, CategoryTheory, and Tactics.

This was tested with:
- Coq 8.10
- UniMath commit version 9e1009089faa45c7cfbae3520df8bb7c5927d4ed.

## Summary 

A detailed summary is available at [`Summary.v`](Summary.v).

## Axioms

The formalization relies on the UniMath library.

There is one admitted result in this work: Theorem 4.7 of Fiore-Saville "List 
object with algebraic structures" (extended version), found in [`Complements.v`](Complements.v).


## Files

by order of dependency:

1. [`SkewMonoidalCategories.v`](SkewMonoidalCategories.v): definitions of
skew monoidal categories.
2. [`Complements.v`](Complements.v): complements, axiomatization of Theorem 4.7
of Fiore-Saville "List object with algebraic structures" (extended version)
3. [`SkewMonoids.v`](SkewMonoids.v)
4. [`IModules.v`](IModules.v): category of pointed I-modules
5. [`StructuralStrengths.v`](StructuralStrengths.v)
6. [`InitialAlgebraicMonoid.v`](InitialAlgebraicMonoid.v): construction of an 
initial algebraic skew-monoid.
7. [`Summary.v`](Summary.v): a summary of the important definitions and results.



