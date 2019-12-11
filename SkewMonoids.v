(** Categories of skew monoids for skew monoidal categories
 (adapted from the definition of Monads of Unimath *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import SkewMonoidalCategories.

Local Open Scope cat.

Section Precategory_of_SkewMonoids.

Context (C : skewmonoidal_precat).

(* Let C := skewmonoidal_precat_precat Mon. *)
Let tensor := skewmonoidal_precat_tensor C.
Notation "X ⊗ Y" := (tensor (X , Y)).
Notation "f #⊗ g" := (# tensor (f #, g)) (at level 31).
Notation I := (skewmonoidal_precat_unit C).
Notation α' := (skewmonoidal_precat_associator C).
Notation λ' := (skewmonoidal_precat_left_unitor C).
Notation ρ' := (skewmonoidal_precat_right_unitor C).

Definition skewMonoid_data : UU :=
  ∑ X : C, (X ⊗ X --> X) × (I --> X).

Coercion sm_ob (X : skewMonoid_data) : C := pr1 X.

Definition sm_unit (X : skewMonoid_data) : I --> X := pr2 (pr2 X).
Definition sm_mult (X : skewMonoid_data) : X ⊗ X --> X := pr1 (pr2 X).

Local Notation η := sm_unit.
Local Notation μ := sm_mult.

Definition skewMonoid_laws (X : skewMonoid_data) : UU :=
	(μ X #⊗ identity X · μ X =  α' ((X, X), X) · identity X #⊗ μ X · μ X) × (* Pentagon diagram *)
	(  η X #⊗ identity X · μ X =  λ' X) × ( ρ' X · identity X #⊗ η X · μ X = identity _). (* Unitor diagrams *)

Definition skewMonoid : UU := ∑ (X : skewMonoid_data), skewMonoid_laws X.

Coercion skewMonoid_to_data (X : skewMonoid) : skewMonoid_data := pr1 X.

Definition skewMonoid_pentagon (X : skewMonoid) :
  μ X #⊗ identity X · μ X =  α' ((X, X), X) · identity X #⊗ μ X · μ X
                                := pr1 (pr2 X).
                               
Definition skewMonoid_unitl (X : skewMonoid) :
  (  η X #⊗ identity X · μ X =  λ' X) :=  pr1 (pr2 (pr2 X)).

Definition skewMonoid_unitr (X : skewMonoid) :
  ( ρ' X · identity X #⊗ η X · μ X = identity _)
  :=  pr2 (pr2 (pr2 X)).

Definition skewMonoid_Mor_laws  {T T' : skewMonoid_data} (α : C ⟦ T , T' ⟧)
  : UU :=
   (μ T · α  = α #⊗ α · μ T')
                × η T · α = η T'.

Lemma isaprop_skewMonoid_Mor_laws  (hs : has_homsets C)
  (T T' : skewMonoid_data ) (α : C ⟦ T , T' ⟧)
  : isaprop (skewMonoid_Mor_laws α).
Proof.
  apply isapropdirprod; apply hs.
Qed.

Definition skewMonoid_Mor  (T T' : skewMonoid_data) : UU
  := ∑ α , @skewMonoid_Mor_laws T T' α.

Coercion mor_from_monoid_mor (T T' : skewMonoid_data) (s : skewMonoid_Mor T T')
  : C ⟦ T , T' ⟧ := pr1 s.

Definition skewMonoid_Mor_η  {T T' : skewMonoid_data } (α : skewMonoid_Mor T T')
  :  η T · α  = η T' .
Proof.
  exact (pr2 (pr2 α)).
Qed.

Definition skewMonoid_Mor_μ  {T T' : skewMonoid_data } (α : skewMonoid_Mor T T')
  : μ T  · α  = α #⊗ α · μ T'.
Proof.
  exact (pr1 (pr2 α)).
Qed.

Lemma skewMonoid_identity_laws  (T : skewMonoid_data )
  : skewMonoid_Mor_laws (identity T).
Proof.
  split; simpl.
  - rewrite id_right.
    etrans;[apply pathsinv0, id_left|].
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (functor_id tensor).
  - apply id_right.
Qed.

Definition skewMonoid_identity (T : skewMonoid_data)
  : skewMonoid_Mor T T := tpair _ _ (skewMonoid_identity_laws T).

Lemma skewMonoid_composition_laws  {T T' T'' : skewMonoid_data }
      (α : skewMonoid_Mor T T') (α' : skewMonoid_Mor T' T'') : skewMonoid_Mor_laws (α · α').
Proof.
  split; intros; simpl.
  - rewrite assoc.
    set (H:=skewMonoid_Mor_μ α ); simpl in H.
    rewrite H; clear H; rewrite <- !assoc.
    set (H:=skewMonoid_Mor_μ α' ); simpl in H.
    etrans;[apply cancel_precomposition,H|].
    clear H.
    etrans;[apply assoc|].
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (functor_comp tensor (_ #, _) (_ #, _)).
  - rewrite assoc.
    eapply pathscomp0; [apply cancel_postcomposition, skewMonoid_Mor_η|].
    apply skewMonoid_Mor_η.
Qed.

Definition skewMonoid_composition  {T T' T'' : skewMonoid_data }
  (α : skewMonoid_Mor T T') (α' : skewMonoid_Mor T' T'')
  : skewMonoid_Mor T T'' := tpair _ _ (skewMonoid_composition_laws α α').

Definition skewMonoid_Mor_equiv (hs : has_homsets C)
  {T T' : skewMonoid_data } (α β : skewMonoid_Mor T T')
  : α = β ≃ (pr1 α = pr1 β).
Proof.
  apply subtypeInjectivity; intro a.
  apply isaprop_skewMonoid_Mor_laws, hs.
Defined.

Definition precategory_skewMonoid_ob_mor  : precategory_ob_mor.
Proof.
  exists skewMonoid.
  exact (λ T T' : skewMonoid , skewMonoid_Mor T T').
Defined.

Definition precategory_skewMonoid_data : precategory_data.
Proof.
  exists (precategory_skewMonoid_ob_mor).
  exists (fun (T : skewMonoid) => skewMonoid_identity T).
  exact (fun (A B C : skewMonoid) => @skewMonoid_composition A B C ).
Defined.

Lemma precategory_skewMonoid_axioms  (hs : has_homsets C)
  : is_precategory precategory_skewMonoid_data.
Proof.
  repeat split; simpl; intros.
  - apply (invmap (skewMonoid_Mor_equiv hs _ _ )).
    apply id_left.
  - apply (invmap (skewMonoid_Mor_equiv hs _ _ )).
    apply id_right.
  - apply (invmap (skewMonoid_Mor_equiv hs _ _ )).
    apply assoc.
  - apply (invmap (skewMonoid_Mor_equiv hs _ _ )).
    apply assoc'.
Qed.

Definition precategory_skewMonoid  (hs : has_homsets C) : precategory
  := tpair _ _ (precategory_skewMonoid_axioms hs).

End Precategory_of_SkewMonoids.