(**
  Skew Monoidal categories

  Based on Monoidal categories

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Notation "'id' X" := (identity X) (at level 30).

Notation "C ⊠ D" := (precategory_binproduct C D) (at level 38).
Notation "( c , d )" := (make_precatbinprod c d).
Notation "( f #, g )" := (precatbinprodmor f g).

Section Skewmonoidal_precat.

Context {C : precategory} (tensor : C ⊠ C ⟶ C) (I : C).

Notation "X ⊗ Y" := (tensor (X, Y)).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

Definition tensor_id {X Y : C} : id X #⊗ id Y = id (X ⊗ Y).
Proof.
  rewrite binprod_id.
  rewrite (functor_id tensor).
  apply idpath.
Defined.

Definition tensor_comp {X Y Z X' Y' Z' : C} (f : X --> Y) (g : Y --> Z) (f' : X' --> Y') (g' : Y' --> Z') :
  (f · g) #⊗ (f' · g') = f #⊗ f' · g #⊗ g'.
Proof.
  rewrite binprod_comp.
  rewrite (functor_comp tensor).
  apply idpath.
Defined.

Definition is_iso_tensor_iso {X Y X' Y' : C} {f : X --> Y} {g : X' --> Y'}
           (f_is_iso : is_iso f) (g_is_iso : is_iso g) : is_iso (f #⊗ g).
Proof.
  exact (functor_on_is_iso_is_iso (is_iso_binprod_iso f_is_iso g_is_iso)).
Defined.

(* I ⊗ - *)
Definition I_pretensor : C ⟶ C := functor_fix_fst_arg _ _ _ tensor I.

Lemma I_pretensor_ok: functor_on_objects I_pretensor = λ c, I ⊗ c.
Proof.
  apply idpath.
Qed.

(* λ *)
Definition left_unitor : UU := nat_trans I_pretensor (functor_identity C).

(* - ⊗ I *)
Definition I_posttensor : C ⟶ C := functor_fix_snd_arg _ _ _ tensor I.

Lemma I_posttensor_ok: functor_on_objects I_posttensor = λ c, c ⊗ I.
Proof.
  apply idpath.
Qed.

(* ρ *)
Definition right_unitor : UU :=
  nat_trans (functor_identity C) I_posttensor .

(* (- ⊗ =) ⊗ ≡ *)
Definition assoc_left : (C ⊠ C) ⊠ C ⟶ C :=
  functor_composite (pair_functor tensor (functor_identity _)) tensor.

Lemma assoc_left_ok: functor_on_objects assoc_left =
  λ c, (ob1 (ob1 c) ⊗ ob2 (ob1 c)) ⊗ ob2 c.
Proof.
  apply idpath.
Qed.

(* - ⊗ (= ⊗ ≡) *)
Definition assoc_right : (C ⊠ C) ⊠ C ⟶ C :=
  functor_composite
    (precategory_binproduct_unassoc _ _ _)
    (functor_composite (pair_functor (functor_identity _) tensor) tensor).

Lemma assoc_right_ok: functor_on_objects assoc_right =
  λ c, ob1 (ob1 c) ⊗ (ob2 (ob1 c) ⊗ ob2 c).
Proof.
  apply idpath.
Qed.

(* α *)
Definition associator : UU :=
  nat_trans assoc_left assoc_right.
(* This definition goes in the opposite direction of that by Mac Lane (CWM 2nd ed., p.162)
   but conforms to the def. on Wikipedia. *)

Definition triangle_eq (λ' : left_unitor) (ρ' : right_unitor) (α' : associator) : UU :=
   ∏ (a b : C), id (a ⊗ b) = pr1 ρ' a #⊗ id b  · pr1 α' ((a, I), b) · id a #⊗ pr1 λ' b .

Definition pentagon_eq (α' : associator) : UU :=
  ∏ (a b c d : C), pr1 α' ((a ⊗ b, c), d) · pr1 α' ((a, b), c ⊗ d) =
   pr1 α' ((a, b), c) #⊗ id d · pr1 α' ((a, b ⊗ c), d) · id a #⊗ pr1 α' ((b, c), d).


End Skewmonoidal_precat.

Definition skewmonoidal_precat : UU :=
  ∑ C : precategory, ∑ tensor : C ⊠ C ⟶ C, ∑ I : C,
  ∑ λ' : left_unitor tensor I,
  ∑ ρ' : right_unitor tensor I,
  ∑ α' : associator tensor,
         (triangle_eq tensor I λ' ρ' α') × (pentagon_eq tensor α').


Definition skewmonoidal_precat_struct : UU :=
  ∑ C : precategory, ∑ tensor : C ⊠ C ⟶ C, ∑ I : C,
  ∑ λ' : left_unitor tensor I,
  ∑ ρ' : right_unitor tensor I,
  ∑ α' : associator tensor, unit.

Definition mk_skewmonoidal_precat_struct (C: precategory)(tensor: C ⊠ C ⟶ C)(I: C)
  (λ': left_unitor tensor I)(ρ': right_unitor tensor I)(α': associator tensor): skewmonoidal_precat_struct :=
  (C,, (tensor,, (I,, (λ',, (ρ',, (α',, tt)))))).

Definition mk_skewmonoidal_precat (C: precategory)(tensor: C ⊠ C ⟶ C)(I: C)
  (λ': left_unitor tensor I)(ρ': right_unitor tensor I)(α': associator tensor)
  (eq1: triangle_eq tensor I λ' ρ' α')(eq2: pentagon_eq tensor α'): skewmonoidal_precat :=
  (C,, (tensor,, (I,, (λ',, (ρ',, (α',, (eq1,, eq2))))))).

Section Skewmonoidal_precat_Accessors.

Context (M : skewmonoidal_precat).

Definition skewmonoidal_precat_precat := pr1 M.

Definition skewmonoidal_precat_tensor := pr1 (pr2 M).

Definition skewmonoidal_precat_unit := pr1 (pr2 (pr2 M)).

Definition skewmonoidal_precat_left_unitor := pr1 (pr2 (pr2 (pr2 M))).

Definition skewmonoidal_precat_right_unitor := pr1 (pr2 (pr2 (pr2 (pr2 M)))).

Definition skewmonoidal_precat_associator := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M))))).

Definition skewmonoidal_precat_eq := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M))))).

End Skewmonoidal_precat_Accessors.

(* Definition strict_skewmonoidal_precat : UU := *)
(*   ∑ M : skewmonoidal_precat, *)
(*   ∏ (eq_λ : I_pretensor (skewmonoidal_precat_tensor M) (skewmonoidal_precat_unit M) = *)
(*   functor_identity (pr1 M)), *)
(*   ∏ (eq_ρ : I_posttensor (skewmonoidal_precat_tensor M) (skewmonoidal_precat_unit M) = *)
(*   functor_identity (pr1 M)), *)
(*   ∏ (eq_α : assoc_left (skewmonoidal_precat_tensor M) = *)
(*   assoc_right (skewmonoidal_precat_tensor M)), *)
(*   is_strict (skewmonoidal_precat_tensor M) (skewmonoidal_precat_unit M) eq_λ (skewmonoidal_precat_left_unitor M) eq_ρ (skewmonoidal_precat_right_unitor M) eq_α (skewmonoidal_precat_associator M). *)
