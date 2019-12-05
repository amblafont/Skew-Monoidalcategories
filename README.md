# Initial semantics for substitution skew-monoids 

This was tested with Coq 8.9 and UniMath (commit 
9e1009089faa45c7cfbae3520df8bb7c5927d4ed)

Compilation: make

## Files
by order of dependency:

1. [`SkewMonoidalCategories.v`](SkewMonoidalCategories.v): definitions of
skew monoidal categories (adapted from the definition of monoidal categories
in UniMath).
2. [`IModules.v`](IModules.v): definition of I-modules
3. [`StructuralActions.v`](StructuralActions.v) 
4. [`StructuralStrengths.v`](StructuralStrengths.v)
5. [`Complements.v`](Complements.v)
6. [`AssumeLemma48.v`](AssumeLemma48.v): construction of an initial susbtitution
skew-monoid.
