(**
  Definition of structural tensorial strengths between actions over skew monoidal categories.

  Based on the definitions of tensorial strengths for monoidal categories

+ def of F-monoid (here alg-monoid)
**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.SkewMonoidal.SkewMonoidalCategories.
Require Import UniMath.CategoryTheory.SkewMonoidal.CategoriesOfMonoids.
Require Import Complements.
Require Import IModules.



Local Open Scope cat.
Local Notation "'id' X" := (identity X) (at level 30).

Local Notation "( c , d )" := (make_catbinprod c d).
Local Notation "( f #, g )" := (catbinprodmor f g).
Local Notation "C ⊠ D" := (category_binproduct C D) (at level 38).
Local Notation φ₁ := (functor_fix_fst_arg _ _ _).
Local Notation φ₂ := (functor_fix_snd_arg _ _ _).
Local Infix "×" := pair_functor  : functor_scope .
Delimit Scope functor_scope with F.

Definition strength_data {V : skewmonoidal_category}(F : V ⟶ V) : UU :=
  nat_trans (C := V ⊠ category_PtIModule V)
            (C' := V)
            ((F × forget_PtIModules V )%F ∙ (skewmonoidal_tensor V))
            ((functor_identity _ × forget_PtIModules V )%F ∙ (skewmonoidal_tensor V) ∙ F).

Section A.

  Context {V : skewmonoidal_category} {F : V ⟶ V}
          (st : strength_data F) .

(* Implicit coercions do not work for reversible notations *)
Notation tensor := (skewmonoidal_tensor (data_from_skewmonoidal V)).
Notation I := (skewmonoidal_I (data_from_skewmonoidal V)).

Context (coeqsV : coequalizers.Coequalizers V).
Context  (tensorl_coeqs : preserves_colimits_of_shape (φ₂ tensor I) coequalizers.Coequalizer_graph ).
   
Notation "X ⊗ Y" := (tensor (X , Y)).
(* TODO: copy this in skew monoids *)
Notation "f #⊗ g" :=
   (functor_on_morphisms (functor_data_from_functor _ _ tensor) (f #, g))
                         (at level 31).

Notation α' := (skewmonoidal_assoc (data_from_skewmonoidal V)).
Notation λ' := (skewmonoidal_unitl (data_from_skewmonoidal V)).
Notation ρ' := (skewmonoidal_unitr (data_from_skewmonoidal V)).

Infix "⊠M" := (PtIModule_tensor V coeqsV tensorl_coeqs) (at level 31).

Let M := category_PtIModule V .
Notation PIMod := (PtIModule V).
Notation IMod := (IModule V).
Notation IM := (PtIModule_I V).
Local Notation σ := (im_action _).
Local Notation αVM := (V_IModules_assoc V coeqsV tensorl_coeqs).

Definition strength_pw (A : V)(B : PIMod) : F A ⊗ B --> F (A ⊗ B) :=
  (st : nat_trans _ _) (A , (B : M)).

Local Notation s := strength_pw.

Definition strength_ax {A A' B B'}(f : V ⟦A , A'⟧)(g : PtIModule_Mor B B') :
  # F f #⊗ g · s A' B' = s A B · # F (f #⊗ g) :=
  nat_trans_ax st _  _ (f #, (g : M ⟦ _, _⟧)).


Definition strength_laws :=
  (* triangle *)
  (∏ (a : V), ρ' (F a) · s a IM = # F (ρ' a)) ×
 (* pentagon *)
 ( ∏ (a : V), ∏ (x y : PIMod)  ,
  αVM (F a) x y · s a (x ⊠M y)
  =
  (s a x) #⊗ (id y) ·  s (a ⊗ x) y · #F (αVM a x y)).
End A.

Coercion strength_pw : strength_data >-> Funclass.
Definition strength {V : skewmonoidal_category}
 (coeqsV : coequalizers.Coequalizers V)
  (tensorl_coeqs : preserves_colimits_of_shape (φ₂ (skewmonoidal_tensor V) (skewmonoidal_I V))
      coequalizers.Coequalizer_graph)
  (F : V ⟶ V)
  : UU :=
  ∑ (s : strength_data F), strength_laws s coeqsV tensorl_coeqs.

Coercion data_from_strength {V coeqsV tensorl_coeqs F}
         (s : @strength V coeqsV tensorl_coeqs F) :
  strength_data F := pr1 s.


Section B.

  Context {V : skewmonoidal_category} 
          {coeqsV : coequalizers.Coequalizers V}
          {tensorl_coeqs : preserves_colimits_of_shape
                             (φ₂ (skewmonoidal_tensor V) (skewmonoidal_I V))
                             coequalizers.Coequalizer_graph }.

  Context {F : V ⟶ V}(s : strength  coeqsV tensorl_coeqs F).

Notation tensor := (skewmonoidal_tensor (data_from_skewmonoidal V)).
Notation I := (skewmonoidal_I (data_from_skewmonoidal V)).
Notation "X ⊗ Y" := (tensor (X , Y)).
(* TODO: copy this in skew monoids *)
Notation "f #⊗ g" :=
   (functor_on_morphisms (functor_data_from_functor _ _ tensor) (f #, g))

                         (at level 31).
Notation α' := (skewmonoidal_assoc (data_from_skewmonoidal V)).
Notation λ' := (skewmonoidal_unitl (data_from_skewmonoidal V)).
Notation ρ' := (skewmonoidal_unitr (data_from_skewmonoidal V)).

Infix "⊠M" := (PtIModule_tensor V coeqsV tensorl_coeqs) (at level 31).

Let M := category_PtIModule V.
Notation PIMod := (PtIModule V).
Notation IM := (PtIModule_I V).
Local Notation σ := (im_action _).
Local Notation π := (IModule_tensor'_proj V coeqsV tensorl_coeqs).
Local Notation αVM := (V_IModules_assoc V coeqsV tensorl_coeqs).

Definition strength_triangle_eq  :
    ∏ (a : V), ρ' (F a) · s a IM   = # F (ρ' a)  := pr1 (pr2 s).

Definition strength_pentagon_eq :
   ( ∏ (a : V), ∏ (x y : PIMod)  ,
  αVM (F a) x y · s a (x ⊠M y)
  =
  (s a x) #⊗ (id y) ·  s (a ⊗ x) y · #F (αVM a x y)) := pr2 (pr2 s).

(*
Lemma strength_pentagon_eq' 
      {x y : PIMod}{z : V}(f : x ⊗ y --> z) 
  (eqf : α' x I y · id x #⊗ λ' y · f = σ x #⊗ id y · f)
      (a : V) :
  αVM (F a) x y · s a (x ⊠M y) · # F
      (identity a #⊗ IModule_tensor'_Out_V V coeqsV tensorl_coeqs f eqf)
  =
  (s a x) #⊗ (id y) ·  s (a ⊗ x) y · #F (α' a x y · identity a #⊗ f).
Proof.
  assert (h := IModule_tensor'_Out_eq V coeqsV tensorl_coeqs f eqf).
  etrans; revgoals.
  {
    repeat rewrite assoc'.
    do 2 apply cancel_precomposition.
    (* etrans; revgoals. *)
    (* { *)
    (*   apply functor_comp. *)
    (* } *)
    etrans; revgoals.
    {
      apply maponpaths.
      etrans; revgoals.
      {
        apply cancel_precomposition.
        etrans; revgoals.
        {
          eapply (maponpaths (# (φ₁ tensor a))).
          exact h.
        }
        apply pathsinv0, (functor_comp (φ₁ tensor a)).
      }
      apply assoc'.
    }
    apply pathsinv0, functor_comp.
    

  }
  repeat rewrite assoc.
  apply cancel_postcomposition.
  apply  strength_pentagon_eq.
Qed.
*)

Local Notation η := (sm_unit _).
Local Notation μ := (sm_mult _).

(** algebraic monoids *)
Definition algMonoid_data : UU :=
  ∑ X : skewMonoid V,  F X --> X.


Coercion monoid_from_algMonoid (X : algMonoid_data) : skewMonoid V := pr1 X.
Definition am_alg (X : algMonoid_data) : F X --> X := pr2 X.

Local Notation κ := am_alg.

Definition algMonoid := ∑ (X : algMonoid_data), 
  s X (PtIModule_from_monoid  _ X ) · # F (μ X) · κ X =
           κ X #⊗ identity X · (μ X).

Coercion algMonoid_data_from_algMonoid (X : algMonoid) : algMonoid_data := pr1 X.

Definition algMonoid_algeq (X : algMonoid) : 
  s X (PtIModule_from_monoid  _ X ) · # F (μ X) · κ X =
           κ X #⊗ identity X · (μ X)
            := pr2 X.


Definition algMonoid_Mor (X Y : algMonoid_data) :=
  ∑ (f : skewMonoid_Mor _ X Y) , κ X · f = # F f · (κ Y).

Coercion mor_from_algMonoid_Mor {X Y : algMonoid_data}(f : algMonoid_Mor X Y)
         : skewMonoid_Mor _ X Y := pr1 f.

Definition algMonoid_Mor_alg {X Y : algMonoid_data} (f : algMonoid_Mor X Y) :
  κ X · f = # F f · (κ Y)
  := pr2 f.


Lemma algMonoid_identity_laws  (T : algMonoid_data )
  : κ T · identity T = # F (identity T) · (κ T).
Proof.
  rewrite functor_id, id_left, id_right.
  apply idpath.
Qed.

Definition algMonoid_identity (T : algMonoid_data)
  : algMonoid_Mor T T := tpair _ (skewMonoid_identity V T) (algMonoid_identity_laws T).

Lemma algMonoid_composition_laws  {T T' T'' : algMonoid_data }
      (α : algMonoid_Mor T T') (α' : algMonoid_Mor T' T'') 
  : κ T · (α · α') = # F (α · α') · κ T''.
Proof.
  rewrite assoc.
  rewrite algMonoid_Mor_alg.
  rewrite <- assoc.
  rewrite algMonoid_Mor_alg.
  rewrite assoc.
  apply cancel_postcomposition.
  apply pathsinv0, functor_comp.
Qed.

Definition algMonoid_composition  {T T' T'' : algMonoid_data }
  (α : algMonoid_Mor T T') (α' : algMonoid_Mor T' T'')
  : algMonoid_Mor T T''
  := tpair _ (skewMonoid_composition _ α α') (algMonoid_composition_laws α α').

Definition algMonoid_Mor_equiv 
  {T T' : algMonoid_data } (α β : algMonoid_Mor T T')
  : α = β ≃ (( α : V ⟦ T ,T'⟧) = β).
Proof.
  eapply weqcomp.
  - apply subtypeInjectivity ; intro a.
    apply homset_property.
  - apply skewMonoid_Mor_equiv.
Defined.

Definition precategory_algMonoid_ob_mor  : precategory_ob_mor :=
   make_precategory_ob_mor algMonoid (λ T T' : algMonoid , algMonoid_Mor T T').

Definition precategory_algMonoid_data : precategory_data.
Proof.
  exists (precategory_algMonoid_ob_mor).
  exists (fun (T : algMonoid) => algMonoid_identity T).
  exact (fun (A B C : algMonoid) => @algMonoid_composition A B C ).
Defined.

Lemma precategory_algMonoid_axioms  
  : is_precategory precategory_algMonoid_data.
Proof.
  repeat split; simpl; intros.
  - apply (invmap (algMonoid_Mor_equiv _  _ )).
    apply id_left.
  - apply (invmap (algMonoid_Mor_equiv  _ _ )).
    apply id_right.
  - apply (invmap (algMonoid_Mor_equiv  _ _ )).
    apply assoc.
  - apply (invmap (algMonoid_Mor_equiv  _ _ )).
    apply assoc'.
Qed.

Definition precategory_algMonoid : precategory
  := tpair _ _ precategory_algMonoid_axioms.

Lemma precategory_algMonoid_homset : has_homsets precategory_algMonoid.
  hnf.
  intros.
  apply isaset_total2.
  apply isaset_total2.
  apply homset_property.
  intros.
  apply isasetaprop.
  apply isaprop_skewMonoid_Mor_laws.
  intros.
  apply isasetaprop.
  apply homset_property.
Qed.

Definition category_algMonoid : category
  := make_category _ precategory_algMonoid_homset.

End B.
