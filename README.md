# Initial semantics for substitution skew-monoids 

This was tested with Coq 8.9 and UniMath (commit 
9e1009089faa45c7cfbae3520df8bb7c5927d4ed)

Compilation: make

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


## Axioms

The formalization relies on the UniMath library.

There is one admitted result in this work: Theorem 4.7 of Fiore-Saville "List 
object with algebraic structures" (extended version), found in [`Complements.v`](Complements.v).

