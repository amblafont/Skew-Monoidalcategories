(** Skew Monoidal functors (based on monoidal functors) *)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import SkewMonoidalCategories.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Section Monoidal_Functor.

Context (Mon_C Mon_D : skewmonoidal_precat).

Let C := skewmonoidal_precat_precat Mon_C.
Let tensor_C := skewmonoidal_precat_tensor Mon_C.
Notation "X ⊗_C Y" := (tensor_C (X , Y)) (at level 31).
Notation "f #⊗_C g" := (# tensor_C (f #, g)) (at level 31).
Let I_C := skewmonoidal_precat_unit Mon_C.
Let α_C := skewmonoidal_precat_associator Mon_C.
Let λ_C := skewmonoidal_precat_left_unitor Mon_C.
Let ρ_C := skewmonoidal_precat_right_unitor Mon_C.

Let D := skewmonoidal_precat_precat Mon_D.
Let tensor_D := skewmonoidal_precat_tensor Mon_D.
Notation "X ⊗_D Y" := (tensor_D (X , Y)) (at level 31).
Notation "f #⊗_D g" := (# tensor_D (f #, g)) (at level 31).
Let I_D := skewmonoidal_precat_unit Mon_D.
Let α_D := skewmonoidal_precat_associator Mon_D.
Let λ_D := skewmonoidal_precat_left_unitor Mon_D.
Let ρ_D := skewmonoidal_precat_right_unitor Mon_D.

Section Monoidal_Functor_Conditions.

Context (F : C ⟶ D).

Definition monoidal_functor_map_dom : precategory_binproduct C C ⟶ D :=
  functor_composite (pair_functor F F) tensor_D.

Lemma monoidal_functor_map_dom_ok: functor_on_objects monoidal_functor_map_dom =
  λ c, F (ob1 c) ⊗_D F (ob2 c).
Proof.
  apply idpath.
Qed.

Definition monoidal_functor_map_codom : precategory_binproduct C C ⟶ D :=
  functor_composite tensor_C F.

Lemma monoidal_functor_map_codom_ok: functor_on_objects monoidal_functor_map_codom =
  λ c, F (ob1 c ⊗_C ob2 c).
Proof.
  apply idpath.
Qed.

Definition monoidal_functor_map :=
  monoidal_functor_map_dom ⟹ monoidal_functor_map_codom.

Definition monoidal_functor_associativity (μ : monoidal_functor_map) :=
  ∏ (x y z : C),
  pr1 μ (x, y) #⊗_D id F(z) · pr1 μ (x ⊗_C y, z) · #F (pr1 α_C ((x, y), z))
  =
  pr1 α_D ((F x, F y), F z) · id (F x) #⊗_D pr1 μ (y, z) · pr1 μ (x, y ⊗_C z).

Definition monoidal_functor_unitality (ϵ : I_D --> F I_C) (μ : monoidal_functor_map) :=
  ∏ (x : C),
  (pr1 λ_D (F x) = ϵ #⊗_D (id (F x)) · pr1 μ (I_C, x) · #F (pr1 λ_C x))
  ×
  (#F (pr1 ρ_C x) = pr1 ρ_D (F x) · (id (F x)) #⊗_D ϵ · pr1 μ (x, I_C)  ).

End Monoidal_Functor_Conditions.

Definition lax_monoidal_functor : UU :=
  ∑ F : C ⟶ D, ∑ ϵ : I_D --> F I_C, ∑ μ : monoidal_functor_map F,
  (monoidal_functor_associativity F μ) × (monoidal_functor_unitality F ϵ μ).

Definition mk_lax_monoidal_functor (F : C ⟶ D) (ϵ : I_D --> F I_C)
  (μ : monoidal_functor_map F) (Hass: monoidal_functor_associativity F μ)
  (Hunit: monoidal_functor_unitality F ϵ μ): lax_monoidal_functor :=
  (F,, (ϵ,, (μ,, (Hass,, Hunit)))).

Definition strong_monoidal_functor : UU :=
  ∑ L : lax_monoidal_functor,
  (is_iso (pr1 (pr2 L))) (* ϵ is an iso *)
  ×
  (is_nat_iso (pr1 (pr2 (pr2 L)))). (* μ is an iso *)

End Monoidal_Functor.

Definition strong_monoidal_functor_functor {Mon Mon' : skewmonoidal_precat} (U : strong_monoidal_functor Mon Mon') := pr1 (pr1 U).
Coercion strong_monoidal_functor_functor : strong_monoidal_functor >-> functor.
