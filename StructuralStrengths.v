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
Require Import SkewMonoidalCategories.
Require Import SkewMonoids.
Require Import IModules.



Local Open Scope cat.
Local Notation "'id' X" := (identity X) (at level 30).

Section A.

Context (V : skewmonoidal_precat).

Context (hsV : has_homsets V).
Notation I := (skewmonoidal_precat_unit V).
Notation tensor := (skewmonoidal_precat_tensor V).
Notation "X ⊗ Y" := (tensor (X , Y)).
Notation "X ⊗ Y" := (IModule_tensor_functor _ hsV (X, Y))  : module_scope.
(* Notation "f #⊗ g" := (# (IModule_tensor_functor _ hsV) (f #, g)) : module_scope. *)
Delimit Scope module_scope with M.

Let M := precategory_IModule V hsV.
Let IM := (IModule_I V : M).
Let λM := (IModule_left_unitor V).
Local Notation ρ' := (skewmonoidal_precat_right_unitor V).

Local Notation "C ⊠ D" := (precategory_binproduct C D) (at level 38).
Local Notation "( c , d )" := (make_precatbinprod c d).
Local Notation "( f #, g )" := (precatbinprodmor f g).

Local Infix "×" := pair_functor  : functor_scope .
Delimit Scope functor_scope with F.

Definition strength_data (F : V ⟶ V) : UU :=
  nat_trans (C := V ⊠ M)(C' := V) ((F × forget_IModules V hsV)%F ∙ tensor)
            ((functor_identity _ × forget_IModules V hsV)%F ∙ tensor ∙ F).

Identity Coercion strength_data_to_nat_trans : strength_data >-> nat_trans.
Notation "X #⊗ Y" := (# tensor (X #, Y)) (at level 20).
Notation α' := (skewmonoidal_precat_associator V).
Notation λ' := (skewmonoidal_precat_left_unitor V).

Definition strength_laws {F : V ⟶ V} (s : strength_data F) :=
  (* triangle *)
  (∏ (a : V), ρ' (F a) · (s (a, IM))   = # F (ρ' a)) ×
 (* pentagon *)
 ( ∏ (a : V), ∏ (x y : IModule _) (z : V)(f : V ⟦ x ⊗ y , z ⟧)
   (eqf : im_action _ x #⊗ identity y · f = α' ((x , I) , y) · identity x #⊗ λ' y · f)
  ,
  (α' ((F a,  x),  y)) · s (a , ((x : ob M) ⊗ (y : ob M))%M)
                       · # F (identity _ #⊗ f)
  =
  (s (a, (x : M))) #⊗ (id ( y)) · ( s ((a ⊗  x), (y : M))) · (#F ( α' ((a,  x),  y)))
                       · # F (identity _ #⊗ f)).

Definition strength (F : V ⟶ V) : UU := ∑ (s : strength_data F), strength_laws s.

Coercion strength_data_from_strength {F : V ⟶ V} (s : strength F)
  : strength_data F := pr1 s.


Definition strength_triangle_eq {F : V ⟶ V} (s : strength F) :
    ∏ (a : V), ρ' (F a) · (s (a, IM))   = # F (ρ' a)  := pr1 (pr2 s).

Definition strength_pentagon_eq {F : V ⟶ V} (s : strength F) :
  ∏ (a : V), ∏ (x y : IModule _) (z : V)(f : V ⟦ x ⊗ y , z ⟧)
   (eqf : im_action _ x #⊗ identity y · f = α' ((x , I) , y) · identity x #⊗ λ' y · f)
  ,
  (α' ((F a,  x),  y)) · s (a , ((x : ob M) ⊗ (y : ob M))%M)
                       · # F (identity a #⊗ f)
  =
  (s (a, (x : M))) #⊗ (id ( y)) · ( s ((a ⊗  x), (y : M))) · (#F ( α' ((a,  x),  y)))
                   · # F (identity a #⊗ f)
   := pr2 (pr2 s).

End A.



Section tensorial.

Context {V : skewmonoidal_precat}.
Context {hsV : has_homsets V}.
Context {F : V ⟶ V} (st : strength _ hsV F).
Notation I := (skewmonoidal_precat_unit V).
Notation tensor := (skewmonoidal_precat_tensor V).
Notation "X ⊗ Y" := (tensor (X , Y)).
Notation "X #⊗ Y" := (# tensor (X #, Y)) (at level 20).
Notation M := (precategory_IModule _ hsV).

(* Definition tensorial_strength_nat   : strength_dom _ hsV _ _ _ ⟹ strength_codom _ hsV _ _  _ := pr1 st. *)
Definition tensorial_strength_nat_pw (X : V) (Y : M) :
  V ⟦ F X ⊗ (Y : IModule _) , F (X ⊗ (Y : IModule _)) ⟧ :=
  st (X , Y).

Notation τ := tensorial_strength_nat_pw.

Notation α := (skewmonoidal_precat_associator V).
Notation IM := (IModule_I V : M).
Notation λ_ := (skewmonoidal_precat_left_unitor V).
Notation ρ := (skewmonoidal_precat_right_unitor V).
Notation "X ⊗ Y" := (IModule_tensor_functor _ hsV (X, Y))  : module_scope.
(* Notation "f #⊗ g" := (# (IModule_tensor_functor _ hsV) (f #, g)) : module_scope. *)
Delimit Scope module_scope with M.

(* Definition tensorial_strength_triangle_eq : ∏ (a : V), ρ (F a) · τ a IM   = (#F (ρ a)) := pr1 (pr2 st). *)
(* Definition tensorial_strength_pentagon_eq :  ∏ (a : V), ∏ (x y : IModule _), *)
(*   (α ((F a,  x),  y)) · τ a ((x : ob M) ⊗ (y : ob M))%M = *)
(*   (τ a x) #⊗ (id ( y)) · ( τ (a ⊗  x) y) · (#F ( α ((a,  x),  y))) *)
(*   := pr2 (pr2 st). *)

Local Notation η := (sm_unit _).
Local Notation μ := (sm_mult _).

(** algebraic monoids *)
Definition algMonoid_data : UU :=
  ∑ X : skewMonoid V,  F X --> X.


Coercion monoid_from_algMonoid (X : algMonoid_data) : skewMonoid V := pr1 X.
Definition am_alg (X : algMonoid_data) : F X --> X := pr2 X.

Local Notation κ := am_alg.

Definition algMonoid := ∑ (X : algMonoid_data), 
  (pr1 st : nat_trans _ _) (X , (IModule_from_monoid _ X : M)) · # F (μ X) · κ X =
           κ X #⊗ identity X · (μ X).

Coercion algMonoid_data_from_algMonoid (X : algMonoid) : algMonoid_data := pr1 X.
Definition algMonoid_algeq (X : algMonoid) : 
  (pr1 st : nat_trans _ _) (X , (IModule_from_monoid _ X : M)) · # F (μ X) · κ X =
           κ X #⊗ identity X · (μ X) := pr2 X.


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

Definition algMonoid_Mor_equiv (hs : has_homsets V)
  {T T' : algMonoid_data } (α β : algMonoid_Mor T T')
  : α = β ≃ (( α : V ⟦ T ,T'⟧) = β).
Proof.
  eapply weqcomp.
  - apply subtypeInjectivity ; intro a.
    apply hs.
  - apply skewMonoid_Mor_equiv.
    exact hs.
Defined.

Definition precategory_algMonoid_ob_mor  : precategory_ob_mor.
Proof.
  exists algMonoid.
  exact (λ T T' : algMonoid , algMonoid_Mor T T').
Defined.

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
  - apply (invmap (algMonoid_Mor_equiv hsV _ _ )).
    apply id_left.
  - apply (invmap (algMonoid_Mor_equiv hsV _ _ )).
    apply id_right.
  - apply (invmap (algMonoid_Mor_equiv hsV _ _ )).
    apply assoc.
  - apply (invmap (algMonoid_Mor_equiv hsV _ _ )).
    apply assoc'.
Qed.

Definition precategory_algMonoid : precategory
  := tpair _ _ precategory_algMonoid_axioms.

End tensorial.
