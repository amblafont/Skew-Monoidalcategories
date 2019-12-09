(**
  Generalisation of the concept of structural actions, over skew monoidal categories.

  Based on the actions over monoidal categories
**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import SkewMonoidalCategories.
Require Import IModules.
(* Require Import SkewMonoidalFunctors. *)

Local Open Scope cat.
Local Notation "'id' X" := (identity X) (at level 30).

Section A.

Context (V : skewmonoidal_precat).

Let I := (skewmonoidal_precat_unit V).
Let tensor := (skewmonoidal_precat_tensor V).
Notation "X ⊗ Y" := (tensor (X , Y)).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).
Let α' := (skewmonoidal_precat_associator V).
Let λ' := (skewmonoidal_precat_left_unitor V).
Let ρ' := (skewmonoidal_precat_right_unitor V).

Section Actions_Definition.

(* A ⊙ I --> A *)
Context (hsV : has_homsets V).
Notation "X ⊗ Y" := (IModule_tensor_functor _ hsV (X, Y))  : module_scope.
(* Notation "f #⊗ g" := (# (IModule_tensor_functor _ hsV) (f #, g)) : module_scope. *)
Delimit Scope module_scope with M.

Let M := precategory_IModule V hsV.
Let IM := (IModule_I V  ).
(* the *_data does not require hsV *)
Let λM := (IModule_left_unitor_data V).
Let αM := (IModule_associator_data V).

Section Actions_Natural_Transformations.



Context {A : precategory} (odot : functor (precategory_binproduct A M) A).

Notation "X ⊙ Y" := (odot (X , Y)) (at level 31).
Notation "f #⊙ g" := (# odot (f #, g)) (at level 31).

Definition odot_I_functor : functor A A := functor_fix_snd_arg _ _ _ odot IM.

Lemma odot_I_functor_ok: functor_on_objects odot_I_functor =
  λ a, a ⊙ (IM : ob M).
Proof.
  apply idpath.
Qed.

Definition action_right_unitor : UU := nat_trans (functor_identity A) odot_I_functor .

Definition odot_x_odot_y_functor : (A ⊠ M) ⊠ M ⟶ A :=
  functor_composite (pair_functor odot (functor_identity _)) odot.

Lemma odot_x_odot_y_functor_ok: functor_on_objects odot_x_odot_y_functor =
  λ a, (ob1 (ob1 a) ⊙ ob2 (ob1 a)) ⊙ ob2 a.
Proof.
  apply idpath.
Qed.

Definition odot_x_otimes_y_functor : (A ⊠ M) ⊠ M ⟶ A :=
  functor_composite (precategory_binproduct_unassoc _ _ _)
                    (functor_composite (pair_functor (functor_identity _) (IModule_tensor_functor _ hsV)) odot).

Lemma odot_x_otimes_y_functor_ok: functor_on_objects odot_x_otimes_y_functor =
  λ a, (ob1 (ob1 a) ⊙ (ob2 (ob1 a) ⊗ ob2 a))%M.
Proof.
  apply idpath.
Qed.

Definition action_convertor : UU := nat_trans odot_x_odot_y_functor odot_x_otimes_y_functor.

Definition action_triangle_eq (ϱ : action_right_unitor) (χ : action_convertor) :=
      ∏ (a : A), ∏ (x : M),
   id _ = (((pr1 ϱ a) #⊙ (id x)) · (pr1 χ ((a, (IM : ob M)), x)) · (# odot ( id a #,  (λM x :  M  ⟦(IModule_tensor V IM x) , x⟧)))). 

  Definition action_pentagon_eq (χ : action_convertor) : UU :=
     ∏ (a : A), ∏ (x y z : M),
  (pr1 χ ((a ⊙ x, y)%M, z)) · (pr1 χ ((a, x), (y ⊗ z)%M)) =
  (pr1 χ ((a, x), y)) #⊙ (id z) · (pr1 χ ((a, (x ⊗ y)%M), z)) ·
                                  (id a) #⊙ (αM (x : IModule _) y z : M ⟦ ((x ⊗ y) ⊗ z)%M , (x ⊗ (y ⊗ z))%M ⟧).

  (* TODO: finish the definition
 some equations are missing: the analogous of the additional equations of skew monoidal cats *)
End Actions_Natural_Transformations.

(* Action over a monoidal category. *)
Definition action : UU := ∑ A : precategory, ∑ (odot : A ⊠ M ⟶ A), ∑ (ϱ : action_right_unitor odot), ∑ (χ : action_convertor odot), (action_triangle_eq odot ϱ χ) × (action_pentagon_eq odot χ).

Definition action_struct : UU := ∑ A : precategory, ∑ (odot : A ⊠ M ⟶ A), ∑ (ϱ : action_right_unitor odot), ∑ (χ : action_convertor odot), unit.

(* The canonical tensorial action on a monoidal category. *)

Definition tensorial_action : action.
Proof.
  exists V.
  exists (pair_functor (functor_identity _) (forget_IModules _ hsV) ∙ tensor).
  exists ρ'.
  exists (pre_whisker (pair_functor (pair_functor (functor_identity _) (forget_IModules _ hsV))(forget_IModules _ hsV)) α').
  split.
  - exact (fun a b => skewmonoidal_precat_triangle_eq V a (b : IModule _)).
  - exact (fun a b c d => skewmonoidal_precat_pentagon_eq V a (b : IModule _)(c : IModule _) (d : IModule _)  ).
Defined.

End Actions_Definition.

End A.