(**
  Definition of structural tensorial strengths between actions over skew monoidal categories.

  Based on the definitions of tensorial strengths for monoidal categories
**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import SkewMonoidalCategories.
Require Import IModules.
Require Import StructuralActions.
(* Require Import SkewActions. *)



Local Open Scope cat.
Local Notation "'id' X" := (identity X) (at level 30).

Section A.

Context (Mon_V : skewmonoidal_precat).

Let V := skewmonoidal_precat_precat Mon_V.
Context (hsV : has_homsets V).
Let I := skewmonoidal_precat_unit Mon_V.
Let tensor := skewmonoidal_precat_tensor Mon_V.
Notation "X ⊗ Y" := (tensor (X , Y)).

Notation "X ⊗ Y" := (IModule_tensor_functor _ hsV (X, Y))  : module_scope.
(* Notation "f #⊗ g" := (# (IModule_tensor_functor _ hsV) (f #, g)) : module_scope. *)
Delimit Scope module_scope with M.

Let M := precategory_IModule Mon_V hsV.
Let IM := (IModule_I Mon_V : M).
Let λM := (IModule_left_unitor Mon_V).
Let αM := (IModule_associator Mon_V).

Section Strengths_Definition.

Context (actn actn' : action Mon_V hsV).

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

Definition strength_dom : A ⊠ M ⟶ A' :=
  functor_composite (pair_functor F (functor_identity _)) odot'.

Lemma strength_dom_ok: functor_on_objects strength_dom = λ ax, F (ob1 ax) ⊙' (ob2 ax).
Proof.
  apply idpath.
Qed.

Definition strength_codom : A ⊠ M ⟶ A' :=
  functor_composite odot F.

Lemma strength_codom_ok: functor_on_objects strength_codom = λ ax, F (ob1 ax ⊙ ob2 ax).
Proof.
  apply idpath.
Qed.


Definition strength_triangle_eq (ϛ : strength_dom ⟹ strength_codom) :=
  ∏ (a : A), pr1 ϱ' (F a) · (pr1 ϛ (a, IM))   = (#F (pr1 ϱ a)).

Definition strength_pentagon_eq (ϛ : strength_dom ⟹ strength_codom): UU := ∏ (a : A), ∏ (x y : M),
  (pr1 χ' ((F a, x), y)) · pr1 ϛ (a, x ⊗ y)%M =
  (pr1 ϛ (a, x)) #⊙' (id y) · (pr1 ϛ (a ⊙ x, y)) · (#F (pr1 χ ((a, x), y))).

End Strengths_Natural_Transformation.

Definition strength (F : A ⟶ A'): UU := ∑ (ϛ : strength_dom F ⟹ strength_codom F),
  (strength_triangle_eq F ϛ) × (strength_pentagon_eq F ϛ).

End Strengths_Definition.

(*
  The standard tensorial strength:
  F(A) ⊗ B --> F(A ⊗ B)
*)
Definition tensorial_strength := strength (tensorial_action Mon_V hsV) (tensorial_action Mon_V hsV).


End A.

Section tensorial.

Context {V : skewmonoidal_precat}.
Context {hsV : has_homsets V}.
Context {F : V ⟶ V} (st : tensorial_strength _ hsV F).
Notation I := (skewmonoidal_precat_unit V).
Notation tensor := (skewmonoidal_precat_tensor V).
Notation "X ⊗ Y" := (tensor (X , Y)).
Notation "X #⊗ Y" := (# tensor (X #, Y)) (at level 20).
Notation M := (precategory_IModule _ hsV).

Definition tensorial_strength_nat   : strength_dom _ hsV _ _ _ ⟹ strength_codom _ hsV _ _  _ := pr1 st.
Definition tensorial_strength_nat_pw (X : V) (Y : M) : V ⟦ F X ⊗ (IMod_carrier _ Y) , F (X ⊗ (IMod_carrier _ Y)) ⟧ :=
  (pr1 st : nat_trans _ _) (X , Y).

Notation τ := tensorial_strength_nat_pw.

Notation α := (skewmonoidal_precat_associator V).
Notation IM := (IModule_I V : M).
Notation λ_ := (skewmonoidal_precat_left_unitor V).
Notation ρ := (skewmonoidal_precat_right_unitor V).
Notation v := (IMod_carrier V).
Notation "X ⊗ Y" := (IModule_tensor_functor _ hsV (X, Y))  : module_scope.
(* Notation "f #⊗ g" := (# (IModule_tensor_functor _ hsV) (f #, g)) : module_scope. *)
Delimit Scope module_scope with M.

Definition tensorial_strength_triangle_eq : ∏ (a : V), ρ (F a) · τ a IM   = (#F (ρ a)) := pr1 (pr2 st).
Definition tensorial_strength_pentagon_eq :  ∏ (a : V), ∏ (x y : M),
  (α ((F a, v x), v y)) · τ a (x ⊗ y)%M =
  (τ a x) #⊗ (id (v y)) · ( τ (a ⊗ v x) y) · (#F ( α ((a, v x), v y)))
  := pr2 (pr2 st).

End tensorial.
