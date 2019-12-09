(**
  Skew Monoidal categories

  (adapted from the definition of Monoidal categories in UniMath)

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

Local Notation "'id' X" := (identity X) (at level 30).

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

Identity Coercion left_unitor_nat : left_unitor >-> nat_trans.

(* - ⊗ I *)
Definition I_posttensor : C ⟶ C := functor_fix_snd_arg _ _ _ tensor I.

Lemma I_posttensor_ok: functor_on_objects I_posttensor = λ c, c ⊗ I.
Proof.
  apply idpath.
Qed.

(* ρ *)
Definition right_unitor : UU :=
  nat_trans (functor_identity C) I_posttensor .

Identity Coercion right_unitor_nat : right_unitor >-> nat_trans.

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

Identity Coercion associator_nat : associator >-> nat_trans.

(* This definition goes in the opposite direction of that by Mac Lane (CWM 2nd ed., p.162)
   but conforms to the def. on Wikipedia. *)

Definition rho_lambda_eq (λ' : left_unitor) (ρ' : right_unitor) : UU :=
  ρ' I · λ' I = id I.

Definition triangle_eq (λ' : left_unitor) (ρ' : right_unitor) (α' : associator) : UU :=
   ∏ (a b : C), id (a ⊗ b) = pr1 ρ' a #⊗ id b  · pr1 α' ((a, I), b) · id a #⊗ pr1 λ' b .

Definition alpha_lambda_eq (λ' : left_unitor) (ρ' : right_unitor) (α' : associator) : UU :=
   ∏ (a b : C), α' ((I, a), b) · λ' (a ⊗ b) = λ' a #⊗ id b.

Definition rho_alpha_eq (λ' : left_unitor) (ρ' : right_unitor) (α' : associator) : UU :=
   ∏ (a b : C), ρ' (a⊗b) · α' ((a,b),I) = id a #⊗ ρ' b.

Definition pentagon_eq (α' : associator) : UU :=
  ∏ (a b c d : C), pr1 α' ((a ⊗ b, c), d) · pr1 α' ((a, b), c ⊗ d) =
   pr1 α' ((a, b), c) #⊗ id d · pr1 α' ((a, b ⊗ c), d) · id a #⊗ pr1 α' ((b, c), d).


End Skewmonoidal_precat.

Definition skewmonoidal_precat : UU :=
  ∑ C : precategory, ∑ tensor : C ⊠ C ⟶ C, ∑ I : C,
  ∑ λ' : left_unitor tensor I,
  ∑ ρ' : right_unitor tensor I,
  ∑ α' : associator tensor,
         (rho_lambda_eq tensor I λ' ρ') × (triangle_eq tensor I λ' ρ' α') ×
      (alpha_lambda_eq tensor I λ' ρ' α') × (rho_alpha_eq tensor I λ' ρ' α') ×
                               (pentagon_eq tensor α') .


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
         (eq1 : rho_lambda_eq tensor I λ' ρ') (eq2 : triangle_eq tensor I λ' ρ' α')
      (eq3 : alpha_lambda_eq tensor I λ' ρ' α')  (eq4 : rho_alpha_eq tensor I λ' ρ' α')
                               (eq5 : pentagon_eq tensor α')
  : skewmonoidal_precat :=
  (C,, tensor,, I,, λ',, ρ',, α',, eq1,, eq2 ,, eq3 ,, eq4 ,, eq5).

Section Skewmonoidal_precat_Accessors.


Coercion skewmonoidal_precat_precat (M : skewmonoidal_precat) := pr1 M.
(* Notation V := skewmonoidal_precat_precat. *)
Context (M : skewmonoidal_precat).
Notation V := M.

Definition skewmonoidal_precat_tensor : V ⊠ V ⟶ V := pr1 (pr2 M).
Notation tensor := skewmonoidal_precat_tensor.

Definition skewmonoidal_precat_unit : V := pr1 (pr2 (pr2 M)).
Notation I := skewmonoidal_precat_unit.

Definition skewmonoidal_precat_left_unitor : left_unitor tensor I := pr1 (pr2 (pr2 (pr2 M))).
Notation λ' := skewmonoidal_precat_left_unitor.


Definition skewmonoidal_precat_right_unitor : right_unitor tensor I := pr1 (pr2 (pr2 (pr2 (pr2 M)))).
Notation ρ' := skewmonoidal_precat_right_unitor.

Definition skewmonoidal_precat_associator : associator tensor := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M))))).
Notation α' := skewmonoidal_precat_associator.

Definition skewmonoidal_precat_eq :
         (rho_lambda_eq tensor I λ' ρ') × (triangle_eq tensor I λ' ρ' α') ×
      (alpha_lambda_eq tensor I λ' ρ' α') × (rho_alpha_eq tensor I λ' ρ' α') ×
                               (pentagon_eq tensor α')
  := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M))))).
Notation eq := skewmonoidal_precat_eq.

Definition skewmonoidal_precat_rho_lambda_eq :  rho_lambda_eq tensor I λ' ρ' := pr1 eq.
Definition skewmonoidal_precat_triangle_eq : triangle_eq tensor I λ' ρ' α' := pr1 (pr2 eq).
Definition skewmonoidal_precat_alpha_lambda_eq : alpha_lambda_eq tensor I λ' ρ' α' := pr1 (pr2 (pr2 eq)).
Definition skewmonoidal_precat_rho_alpha_eq : rho_alpha_eq tensor I λ' ρ' α' := pr1 (pr2 (pr2 (pr2 eq))).
Definition skewmonoidal_precat_pentagon_eq : pentagon_eq tensor α' :=  (pr2 (pr2 (pr2 (pr2 eq)))).

Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

Lemma I_mult_laws : α' ((I,, I),, I) · identity I #⊗ λ' I · λ' I = λ' I #⊗ identity I · λ' I.
Proof.
   etrans.
    {
      etrans;[apply pathsinv0,assoc|].
      apply cancel_precomposition.
      apply (nat_trans_ax λ').
    }
    rewrite assoc.
    apply cancel_postcomposition.
    apply skewmonoidal_precat_alpha_lambda_eq.
Qed.

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
