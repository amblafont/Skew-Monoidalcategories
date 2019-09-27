(**
  Definition of tensorial strengths between actions over skew monoidal categories.

  Based on the definitions of tensorial strengths for monoidal categories
**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import SkewMonoidalCategories.
Require Import SkewActions.

Local Open Scope cat.

Section A.

Context (Mon_V : skewmonoidal_precat).

Let V := skewmonoidal_precat_precat Mon_V.
Let I := skewmonoidal_precat_unit Mon_V.
Let tensor := skewmonoidal_precat_tensor Mon_V.
Notation "X ⊗ Y" := (tensor (X , Y)).

Section Strengths_Definition.

Context (actn actn' : action Mon_V).

Let A := pr1 actn.
Let odot := pr1 (pr2 actn).
Let ϱ := pr1 (pr2 (pr2 actn)).
Let χ := pr1 (pr2 (pr2 (pr2 actn))).
Let A' := pr1 actn'.
Let odot' := pr1 (pr2 actn').
Let ϱ' := pr1 (pr2 (pr2 actn')).

Let χ' := pr1 (pr2 (pr2 (pr2 actn'))).

Section Strengths_Natural_Transformation.

Context (F : A ⟶ A').

Notation "X ⊙ Y" := (odot (X , Y)) (at level 31).
Notation "f #⊙ g" := (#odot (f #, g)) (at level 31).
Notation "X ⊙' Y" := (odot' (X , Y)) (at level 31).
Notation "f #⊙' g" := (#odot' (f #, g)) (at level 31).

Definition strength_dom : A ⊠ V ⟶ A' :=
  functor_composite (pair_functor F (functor_identity _)) odot'.

Lemma strength_dom_ok: functor_on_objects strength_dom = λ ax, F (ob1 ax) ⊙' (ob2 ax).
Proof.
  apply idpath.
Qed.

Definition strength_codom : A ⊠ V ⟶ A' :=
  functor_composite odot F.

Lemma strength_codom_ok: functor_on_objects strength_codom = λ ax, F (ob1 ax ⊙ ob2 ax).
Proof.
  apply idpath.
Qed.

Definition strength_nat : UU := nat_trans strength_dom strength_codom.

Definition strength_triangle_eq (ϛ : strength_nat) :=
  ∏ (a : A), pr1 ϱ' (F a) · (pr1 ϛ (a, I))   = (#F (pr1 ϱ a)).

Definition strength_pentagon_eq (ϛ : strength_nat): UU := ∏ (a : A), ∏ (x y : V),
  (pr1 χ' ((F a, x), y)) · pr1 ϛ (a, x ⊗ y) =
  (pr1 ϛ (a, x)) #⊙' (id y) · (pr1 ϛ (a ⊙ x, y)) · (#F (pr1 χ ((a, x), y))).

End Strengths_Natural_Transformation.

Definition strength (F : A ⟶ A'): UU := ∑ (ϛ : strength_nat F),
  (strength_triangle_eq F ϛ) × (strength_pentagon_eq F ϛ).

End Strengths_Definition.

(*
  The standard tensorial strength:
  F(A) ⊗ B --> F(A ⊗ B)
*)
Definition tensorial_strength := strength (tensorial_action Mon_V) (tensorial_action Mon_V).


End A.

Section tensorial.

Context {Mon_V : skewmonoidal_precat}.
Let V := skewmonoidal_precat_precat Mon_V.
Context {F : V ⟶ V} (st : tensorial_strength _ F).
Let I := skewmonoidal_precat_unit Mon_V.
Let tensor := skewmonoidal_precat_tensor Mon_V.
Notation "X ⊗ Y" := (tensor (X , Y)).
Definition st_pw (st : tensorial_strength _ F) :

End tensorial.
