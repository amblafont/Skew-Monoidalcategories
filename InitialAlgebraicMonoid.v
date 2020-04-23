(**
Construction of an initial F-monoid, for F a strengthened endofunctor
(in the skew-monoidal setting): [algMonoid_Initial]
**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Adamek.
Require Import UniMath.CategoryTheory.Chains.OmegaCocontFunctors.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.graphs.eqdiag.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import SkewMonoidalCategories.
Require Import StructuralStrengths.
Require Import IModules.
Require Import Complements.
Require Import SkewMonoids.

Local Open Scope cat.


Local Infix "×" := pair_functor  : functor_scope .
Local Infix ",," := bindelta_pair_functor  : functor_scope .
Local Notation "'π₁'" := (pr1_functor _ _) : functor_scope.
Local Notation "'π₂'" := (pr2_functor _ _) : functor_scope.
Delimit Scope functor_scope with F.

Local Infix "+" := (BinCoproductOfArrows _ _ _) : morphism_scope.

Local Notation ι₁ := (BinCoproductIn1 _ _).
Local Notation ι₂ := (BinCoproductIn2 _ _).

Local Notation carrier := (alg_carrier _ ).


Local Notation φ₁ := (functor_fix_fst_arg _ _ _).
Local Notation φ₂ := (functor_fix_snd_arg _ _ _).



Section A.
Context (V : skewmonoidal).
(* homsets *)
Context (hsV : has_homsets V).

Let Vcat : category := make_category V hsV.


Declare Scope object_scope.
Delimit Scope morphism_scope with m.
Delimit Scope object_scope with o.
Open Scope object_scope.

Notation tensor := (skewmonoidal_tensor (data_from_skewmonoidal V)).
Notation I := (skewmonoidal_I (data_from_skewmonoidal V)).
Notation "X ⊗ Y" := (tensor (X , Y)).
(* TODO: copy this in skew monoids *)
Notation "f #⊗ g" :=
   (functor_on_morphisms (functor_data_from_functor _ _ tensor) (f #, g))

                         (at level 31).
Notation α' := (skewmonoidal_assoc (data_from_skewmonoidal V)).
Notation λ' := (skewmonoidal_unitl (data_from_skewmonoidal V)).
Notation ρ := (skewmonoidal_unitr (data_from_skewmonoidal V)).

Notation M := (precategory_PtIModule V hsV).

Notation IMod := (IModule V hsV).
Notation PIMod := (PtIModule V hsV).

(* Notation M := (precategory_IModule V hsV). *)
(* Notation tensorM := (IModule_tensor_functor V hsV). *)
(* Notation "X ⊗ Y" := (tensorM ((X : M) , (Y : M)))  : module_scope. *)
(* Delimit Scope module_scope with M. *)

(** as modules *)
Notation IM := (PtIModule_I V hsV).
Infix "⊗M" := (IModule_tensor V) (at level 31).
Local Notation σ := (im_action _).
(* Let λM := (IModule_left_unitor_data V). *)
(* Let αM := (IModule_associator_data V). *)

(* V co-complete *)
Context (Vch : Colims_of_shape nat_graph V).
Context (O : Initial  V).
Context (bc : BinCoproducts  V).
Context (coeqsV : coequalizers.Coequalizers V).

Infix "+" := bc : object_scope.


(* Infix ";" := (nat_trans_comp _ _ _) (at level 5). *)
Infix "×" := pair_functor  : functor_scope .
Delimit Scope functor_scope with F.

(* Notation "'v' X" := (X : IModule _) (at level 3). *)
Notation M_V := (forget_IModules _ hsV).
Notation pM_V := (forget_PtIModules _ hsV).


(** _ ⊗ X is omega cocontinuous *)
Context (ltensor_cc : ∏ (X : V) , is_cocont (φ₂ tensor X)).

Lemma tensorl_coeqs : preserves_colimit_of_shape (φ₂ tensor I)
                                                 coequalizers.Coequalizer_graph.
Proof.
  red.
  intros.
  eapply ltensor_cc.
  apply isColimCocone_from_ColimCocone.
Qed.



Definition tensor_isInitial {o : V}(Io : isInitial _ o)(X : V) :
  isInitial _ (o ⊗ X) :=
  cocont_preserves_isInitial  (C := Vcat)(D := Vcat) (ltensor_cc X) Io.


Local Definition O_tensor_X_isInitial (X : V) : isInitial _ (O ⊗ X) :=
  tensor_isInitial (pr2 _) X.

Local Definition O_tensor_X_Initial (X : V) : Initial V :=
  make_Initial _ (O_tensor_X_isInitial X).

Local Definition tensor_left_isBinCoproduct {A B : V} (ccAB : BinCoproduct _ A B) (C : V) :
  isBinCoproduct _ (A ⊗ C) (B ⊗ C) (ccAB ⊗ C)
                 (# (φ₂ tensor C) (BinCoproductIn1 _ _))
                  (# (φ₂ tensor C) (BinCoproductIn2 _ _)) :=
   cocont_preserves_isBinCoproduct (C := Vcat)(D := Vcat)
                                         (ltensor_cc C) ccAB.


Definition tensor_left_bp_gen {A B : V} (ccAB : BinCoproduct _ A B)(C : V) : BinCoproduct _ (A ⊗ C) (B ⊗ C) :=
  make_BinCoproduct _ _ _ _ _ _ (tensor_left_isBinCoproduct ccAB C).

Definition tensor_left_bp (A B : V) (C : V) : BinCoproduct _ (A ⊗ C) (B ⊗ C) := tensor_left_bp_gen (A + B) C.

Lemma BinCoproductArrow_tensor {w x y z1 z2 : V}(ccxy : BinCoproduct _ w x)
      (f : V ⟦ w , y ⟧)(g : V ⟦ x , y ⟧)(u : V ⟦ z1 , z2 ⟧) :
  (BinCoproductArrow _ ccxy f g ) #⊗ u = BinCoproductArrow _ (tensor_left_bp_gen ccxy z1)
                                                                    (f #⊗ u)(g #⊗ u).
Proof.
  use (BinCoproductArrowUnique _ _ _ (tensor_left_bp_gen _ _));
  (etrans ; [apply pathsinv0,(functor_comp ( tensor ))|]) ; cbn ; rewrite id_left;
  apply (maponpaths (fun z => z #⊗ _)).
  - apply BinCoproductIn1Commutes .
  - apply BinCoproductIn2Commutes .
Qed.

Lemma BinCoproductOfArrows_tensor {w x y1 y2 z1 z2 : V}(ccxy : BinCoproduct _ w x) (ccys : BinCoproduct _ y1 y2)
      (f : V ⟦ w , y1 ⟧)(g : V ⟦ x , y2 ⟧)(u : V ⟦ z1 , z2 ⟧) :
  (BinCoproductOfArrows _ ccxy ccys f g ) #⊗ u = BinCoproductOfArrows _ (tensor_left_bp_gen ccxy z1)
                                                                               (tensor_left_bp_gen ccys z2)
                                                                    (f #⊗ u)(g #⊗ u).
Proof.
  etrans.
  use BinCoproductArrow_tensor.
  use map_on_two_paths;  (etrans;[|apply (functor_comp tensor)]); cbn;
    apply (maponpaths (fun z => _ #⊗ z)), pathsinv0 , id_right.
Qed.

Lemma bc_id_tensor {a b c d : V} (ccab : BinCoproduct _ a b) (f : V ⟦ c , d ⟧) :
  identity ccab #⊗ f = BinCoproductOfArrows  _ (tensor_left_bp_gen ccab _)
                                             (tensor_left_bp_gen ccab _) (identity _ #⊗ f)(identity _ #⊗ f).
Proof.
  etrans;[eapply (maponpaths (fun z => z #⊗ _)), BinCoproductOfIdentities|].
  apply BinCoproductOfArrows_tensor.
Qed.

Lemma usual_eq1 {X a b c A : V}   (v' : V ⟦ c ⊗ X , A ⟧)
      (u : V ⟦ a + b , c ⟧)
  {vv1 : V ⟦ a ⊗ X, A ⟧}
  {vv2 : V ⟦ b ⊗ X, A ⟧}
  (veq : (u #⊗ identity (X)) · v' =
         BinCoproductArrow V (tensor_left_bp _ _ _) vv1 vv2) :
  ((ι₁ · u) #⊗ identity  X) · v' = vv1.
Proof.
  etrans.
  {
    apply cancel_postcomposition.
    apply (functor_comp (φ₂ tensor _)).
  }
  rewrite <- assoc.
  etrans;[apply cancel_precomposition,veq|].
  apply (BinCoproductIn1Commutes _ _ _ (tensor_left_bp_gen _ _)) .
Qed.

Lemma usual_eq2 {X a b c A : V}   (v' : V ⟦ c ⊗ X , A ⟧)
      (u : V ⟦ a + b , c ⟧)
  {vv1 : V ⟦ a ⊗ X, A ⟧}
  {vv2 : V ⟦ b ⊗ X, A ⟧}
  (veq : (u #⊗ identity (X)) · v' =
         BinCoproductArrow V (tensor_left_bp _ _ _) vv1 vv2) :
  ((ι₂ · u) #⊗ identity  X) · v' = vv2.
Proof.
  etrans.
  {
    apply cancel_postcomposition.
    apply (functor_comp (φ₂ tensor _)).
  }
  rewrite <- assoc.
  etrans;[apply cancel_precomposition,veq|].
  apply (BinCoproductIn2Commutes _ _ _ (tensor_left_bp_gen _ _)) .
Qed.

Lemma rho_bincoproduct_eq {X : V}{Y : V}
  : ρ (X + Y) = BinCoproductOfArrows _ (bc _ _) (tensor_left_bp _ _ _) (ρ X)(ρ Y).
Proof.
  use BinCoproductArrowUnique; apply skewmonoidal_unitr_ax.
Qed.

Lemma rho_bincoproduct_postcomp_eq {X : V}{Y : V}{Z : V}
      (f : V ⟦ X ⊗ I, Z ⟧)(g : V ⟦ Y ⊗ I , Z⟧)
  : ρ (X + Y) · (BinCoproductArrow _ (tensor_left_bp _ _ _) f g) =
        BinCoproductArrow _ (bc _ _) (ρ X · f)(ρ Y · g).
Proof.
  rewrite rho_bincoproduct_eq.
  apply (precompWithBinCoproductArrow _ (bc _ _)(tensor_left_bp _ _ _)  ).
Qed.

Lemma rho_bincoproductofarrows_postcomp_eq {X : V}{Y : V}{Z1 Z2 : V}
      (f : V ⟦ X ⊗ I, Z1 ⟧)(g : V ⟦ Y ⊗ I , Z2⟧)
  : ρ (X + Y) · (BinCoproductOfArrows _ (tensor_left_bp _ _ _) (bc _ _) f g) =
        BinCoproductOfArrows _ (bc _ _) (bc _ _) (ρ X · f)(ρ Y · g).
Proof.
  etrans; [use (rho_bincoproduct_postcomp_eq ) |].
  now repeat rewrite assoc.
Qed.

Lemma alpha_bincoproduct_eq (X : V)(Y : V) a b
  : α' (X + Y) a b =
    BinCoproductOfArrows _ (tensor_left_bp_gen (tensor_left_bp _ _ _)  _)
                         (tensor_left_bp_gen _  _)
                      (α' X a b )
                      (α' Y a b ).
Proof.
  use (BinCoproductArrowUnique _ _ _ (tensor_left_bp_gen (tensor_left_bp _ _ _)  _));
  (etrans; [use (skewmonoidal_assoc_ax)|]);
  cbn;
  apply cancel_precomposition;
  eapply (maponpaths (fun z =>  (_ #⊗ z)));
  apply (functor_id tensor).
Qed.

(* F has a strength *)
Definition spec_st2 (H : V ⊠ V ⟶ V) : UU :=
  (H × pM_V)%F ∙ tensor ⟹ ((π₁ × pM_V) ∙ tensor,, (π₂ × pM_V) ∙ tensor)%F ∙ H.

Identity Coercion spec_st2_to_nat : spec_st2 >-> nat_trans.


Definition st2_pw {F : V ⊠ V ⟶ V}(st : spec_st2 F) (C D : V)(E : PIMod) :
  V ⟦ (F (C , D)) ⊗ E , F (C ⊗ E , D ⊗ E) ⟧ := st ((C , D) , (E : M)).





(* Parameterized initiality *)
Definition isPInitial {F }(st : spec_st2 F) {Z : V}{A : V}(a : V ⟦ F (Z ,, A) , A ⟧) : UU :=
  ∏ (P : PIMod) (C : V) (c : V ⟦ F (Z ⊗ P, C), C ⟧),
  ∃! u : V ⟦ A ⊗ P, C ⟧, st2_pw st Z A P · # F ( (identity _ ) #, u) · c = # (φ₂ tensor (P)) a · u.

Definition PInitial_mor
  {F }{st : spec_st2 F} {Z : V}{A : V}{a : V ⟦ F (Z ,, A) , A ⟧}
  (p : isPInitial st a)
  {P : PIMod} {C : V} (c : V ⟦ F (Z ⊗ P, C), C ⟧) : V ⟦ A ⊗ P, C ⟧ :=
  pr1 (pr1 (p _ _ c)).

Definition PInitial_mor_commutes
  {F }{st : spec_st2 F} {Z : V}{A : V}{a : V ⟦ F (Z ,, A) , A ⟧}
  (p : isPInitial st a)
  {P : PIMod} {C : V} (c : V ⟦ F (Z ⊗ P, C), C ⟧) :
    st2_pw st Z A P · # F ( identity _ #, (PInitial_mor p c)) · c = # (φ₂ tensor P) a · (PInitial_mor p c) :=
  pr2 (pr1 (p _ _ c)).

Definition PInitial_mor_unique
  {F }{st : spec_st2 F} {Z : V}{A : V}{a : V ⟦ F (Z ,, A) , A ⟧}
  (p : isPInitial st a)
  {P : PIMod} {C : V} (c : V ⟦ F (Z ⊗ P, C), C ⟧)
  (u : V ⟦ A ⊗ P, C ⟧) 
    (eq : st2_pw st Z A P · # F ( identity _ #, u) · c = # (φ₂ tensor P) a · u) 
  : u = PInitial_mor p c :=
   base_paths _ _ (iscontr_uniqueness (p _ _ c) (u ,, eq)).

Lemma lemma48_nat_trans_aux
           F P b (J :=  φ₂ tensor P)
  : is_nat_trans (C := V)(C' := V) (φ₁ (F) (J b)) (φ₁ ((J × functor_identity V)%F ∙ F) b) (fun z => identity _).
Proof.
  intros x y f.
  cbn.
  unfold functor_fix_fst_arg_mor,functor_fix_snd_arg_mor,functor_fix_fst_arg_ob,functor_fix_snd_arg_ob,make_dirprod.
  cbn.
  rewrite (functor_id tensor).
  apply is_nat_trans_id.
Qed.
Definition lemma48_iso_aux 
           F P b
  (J :=  φ₂ tensor P) :
    nat_iso (C := V)(D := V) (φ₁ (F) (J b))(φ₁ ((J × functor_identity V)%F ∙ F) b).
Proof.
  use make_nat_iso.
  -  eapply make_nat_trans.
     use lemma48_nat_trans_aux.
  - intro.
    apply identity_is_iso.
Defined.


(* We only need that F is right omega cocontinuous actually, and the strength can be only a natural transformation
of the conference paper
 *)
Lemma  lemma48 :
           ∏ F (st : spec_st2 F)
             (Fromega : ∏ X, is_omega_cocont (φ₁ F X) )(Z : V) ,
           isPInitial st
                      (alg_map _ (InitialObject (colimAlgInitial hsV O (Fromega Z) (Vch (initChain O _))))).
Proof.
  intros F st Fromega Z P C c.
  set (J := φ₂ tensor P).
  (* eset (st' := ?st'). *)
  set (st' := ( (nat_trans_fix_snd_arg _ _ _ _ _ st P)): F ∙ J ⟹
                                                           (functor_identity V × J)%F ∙ ((J × functor_identity V)%F ∙ F)).
  (* (J × J)%F ∙ F *)
  
  unshelve eset (h := Thm47_mor hsV O Vch hsV Vch (J := J) _ _ (F := F) _
                       (G := (J × functor_identity _)%F ∙ F ) _ (K := functor_identity _) st' c); revgoals.
  {
    use unique_exists.
    + exact h.
    + cbn.
      etrans; [| use (Thm47_commutes hsV O Vch hsV Vch (J := J) _ _ (F := F) _ _ st' c)].
      cbn.
      unfold st2_pw,nat_trans_fix_snd_arg_data,functor_fix_snd_arg_mor; cbn.
      apply cancel_postcomposition.
      (* Don't know what is happening with the following commands but it works *)
      apply maponpaths.
      apply maponpaths.
      apply dirprod_paths; [|apply idpath].
      cbn.
      apply pathsinv0, (functor_id tensor (Z , P)).
    + intro y. apply hsV.
    + cbn.
      intros y eq.
      use (Thm47_unique hsV O Vch hsV Vch (J := J) _ _ (F := F) _ _ st' c).
      etrans;[|apply eq].
      cbn.
      unfold st2_pw,nat_trans_fix_snd_arg_data,functor_fix_snd_arg_mor; cbn.
      apply cancel_postcomposition.
      cbn.
      (* Don't know what is happening with the following commands but it works *)
      apply maponpaths.
      apply maponpaths.
      apply dirprod_paths; [|apply idpath].
      cbn.
      apply (functor_id tensor (Z , P)).
  }
  - intro b.
    eapply (is_omega_cocont_iso hsV );[|apply Fromega].
    use (nat_iso_to_iso (C := Vcat) (D := Vcat)).
    apply lemma48_iso_aux.
  - use (ltensor_cc P).
  - use O_tensor_X_isInitial.
Qed.


Context (F : V ⟶ V) (st : strength hsV F coeqsV tensorl_coeqs) (Fomega: is_omega_cocont F).

Infix "⊠M" := (PtIModule_tensor V hsV coeqsV tensorl_coeqs) (at level 31).
Infix "⊗M'" := (IModule_tensor' V hsV coeqsV tensorl_coeqs) (at level 31).
Infix "#⊗M'" := (IModule_tensor'_on_mor V hsV coeqsV tensorl_coeqs) (at level 31).
Notation π := (IModule_tensor'_proj V hsV coeqsV tensorl_coeqs).
Local Notation αVM := (V_IModules_assoc V hsV coeqsV tensorl_coeqs).
Local Notation λP := (PtIModule_unitl V hsV coeqsV tensorl_coeqs).
Notation IP := (PtIModule_I V hsV).
Notation σ' := (PtIModule_action V hsV coeqsV tensorl_coeqs).
Notation ϵ := (im_unit V hsV).
Notation ϵPt := (PtIModule_unit_Mor V hsV).
(* Let stF_nat :=  (st : nat_trans _ _ ). *)
(* Local Definition st (X : V) (Y : M) : V ⟦ F X ⊗ (v Y) , F (X ⊗ (v Y)) ⟧ := *)
(*   stF_nat (X ,, Y). *)


Lemma alphaVM_bincoproduct_eq (X : V)(Y : V) a b
  : αVM (X + Y) a b =
    BinCoproductOfArrows _ (tensor_left_bp_gen (tensor_left_bp _ _ _)  _)
                         (tensor_left_bp_gen _  _)
                      (αVM X a b )
                      (αVM Y a b ).
Proof.
  use (BinCoproductArrowUnique _ _ _ (tensor_left_bp_gen (tensor_left_bp _ _ _)  _)) ;
  (etrans; [ apply  V_IModules_assoc_ax with
                (g := IModule_identity _ _)
                (h := IModule_identity _ _)|]);
  apply cancel_precomposition;
  eapply (maponpaths (fun z =>  (_ #⊗ z)));
  apply IModule_tensor'_id.
Qed.

Definition H : V ⊠ V ⟶ V := BinCoproduct_of_functors _ _ bc (pr1_functor _ _)
                                                     (pr2_functor _ _ ∙ F).


Definition stH_data :
  nat_trans_data ((H × pM_V)%F ∙ tensor)
    (((π₁ × pM_V) ∙ tensor,, (π₂ × pM_V) ∙ tensor)%F ∙ H)
  :=
    fun X => BinCoproductOfArrows _ (tensor_left_bp _ _ _) _ (identity _) (st _ _).

Lemma  stH_is_nat : is_nat_trans _ _ stH_data.
Proof.

  intros [[X1 X2] X3] [[Y1 Y2] Y3] [[f1 f2] f3].
  unfold stH_data.
  cbn.
  (* unfold BinCoproduct_of_functors_ob, pr1_functor,pr2_functor, BinCoproduct_of_functors_mor,stH_data; cbn. *)
  etrans;[apply cancel_postcomposition,BinCoproductOfArrows_tensor|].
  etrans;[apply (BinCoproductOfArrows_comp' (tensor_left_bp _ _ _) (tensor_left_bp _ _ _)  )|].
  etrans; revgoals.
  {
    apply pathsinv0.
    apply (BinCoproductOfArrows_comp' (tensor_left_bp _ _ _)  ).
  }
  apply map_on_two_paths.
  - rewrite id_left,id_right.
    apply idpath.
  - apply (strength_ax st).
Qed.

Definition stH : spec_st2 H := make_nat_trans _ _ stH_data stH_is_nat.

Definition G := φ₁ H I.

Definition sumFI :=
  BinCoproduct_of_functors _ _ bc (constant_functor _ _ I) F.


(** Sanity check *)
Lemma G_is_sumFI :
  G = sumFI.
Proof.
  apply functor_eq; [exact hsV |].
  apply idpath.
Qed.

Definition Homega  : is_omega_cocont H.
Proof.
  use (is_omega_cocont_BinCoproduct_of_functors _ hsV).
  - use (is_cocont_pr1_functor hsV).
  - use (is_omega_cocont_functor_composite hsV).
    + use (is_cocont_pr2_functor hsV).
    + exact Fomega.
Qed.


Definition Homega2 (X : V) : is_omega_cocont (φ₁ H X) :=
  is_omega_cocont_fix_fst_arg hsV hsV hsV Homega X.

Definition Gomega : is_omega_cocont G := Homega2 I.

(* Our candidate: the initial algebra of G = I + F *)
Definition Ai := colimAlgInitial hsV O Gomega (Vch (initChain O G)).

Definition A := alg_carrier _ (InitialObject Ai).


Lemma A_is_InitialAlg_sumFI :
  A = alg_carrier sumFI
                  (InitialObject (colimAlgInitial hsV O
                                   (transportf is_omega_cocont G_is_sumFI Gomega)
                                   (Vch (initChain O sumFI)))).
Proof.
  induction G_is_sumFI.
  apply idpath.
Qed.


(* The algebra structure *)
Definition A_Galg : V ⟦ G A , A ⟧ := alg_map _ _.
(* which is parametric initial *)
Definition A_Galg_PInitial : isPInitial stH A_Galg := lemma48 H stH Homega2 I.


Lemma A_Galg_mor_eq_aux (P : PIMod) {C : V}  (u : V ⟦ A ⊗ P , C ⟧) :
  BinCoproductOfArrows  _ (tensor_left_bp I (F A) _) (bc _ _)
                        (identity _)
                        (st A P · # F u) 
  = st2_pw stH I A P · # H (identity (I ⊗ P) #, u).
Proof.
  cbn -[A].
  unfold stH_data,BinCoproduct_of_functors_mor.
  cbn -[A].
  apply pathsinv0.
  etrans;[apply (BinCoproductOfArrows_comp' (tensor_left_bp _ _ _))|].
  cbn.
  now rewrite id_right.
Qed.


(* TODO: faire le cas où c est un coproduit ?
maybe this one is useless then
 *)
Definition A_Galg_mor_commutes (P : PIMod) {C : V} (c : V ⟦ I ⊗ P + F C, C ⟧) :
  BinCoproductOfArrows  _ (tensor_left_bp I (F A) _) (bc _ _)
                        (identity _)
                        (st A P · # F (PInitial_mor A_Galg_PInitial c)) · c
  =
        (A_Galg #⊗ identity _) · PInitial_mor A_Galg_PInitial c.
Proof.
  etrans;[| apply (PInitial_mor_commutes A_Galg_PInitial)].
  apply cancel_postcomposition.
  apply A_Galg_mor_eq_aux.
Qed.

Definition A_Galg_mor_coprod_commutes (P : PIMod) {C : V}  u 
           (c1 : V ⟦ I ⊗ P , C ⟧)(c2 : V ⟦ F C, C ⟧)
  (c := BinCoproductArrow _ (bc _ _) c1 c2) :
  (BinCoproductArrow  _ (tensor_left_bp I (F A) _) 
                        c1
                        (st A P · # F u · c2)
                        =
  (BinCoproductOfArrows  _ (tensor_left_bp I (F A) _) (bc _ _)
                        (identity _)
                        (st A P · # F u) · c)).
Proof.
  etrans; revgoals.
  apply pathsinv0.
  apply (postcompWithBinCoproductArrow _ (tensor_left_bp _ _ _)).
  apply map_on_two_paths.
  - rewrite id_left.
    apply pathsinv0, BinCoproductIn1Commutes.
  - repeat rewrite <- assoc.
    repeat apply cancel_precomposition.
    apply pathsinv0, BinCoproductIn2Commutes.
Qed.

Definition A_Galg_mor_unique (P : PIMod) {C : V} (c : V ⟦ I ⊗ P + F C, C ⟧) u :
  (BinCoproductOfArrows  _ (tensor_left_bp I (F A) _) (bc _ _)
                        (identity _)
                        (st A P · # F u) · c
  =
        (A_Galg #⊗ identity _) · u) -> u = PInitial_mor A_Galg_PInitial c.
Proof.
  intro h.
  use (PInitial_mor_unique A_Galg_PInitial).
  use (pathscomp0 _ h).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply A_Galg_mor_eq_aux.
Qed.

Definition A_Galg_mor_unique' (P : PIMod) {C : V}  u 
           (c1 : V ⟦ I ⊗ P , C ⟧)(c2 : V ⟦ F C, C ⟧)
  (c := BinCoproductArrow _ (bc _ _) c1 c2) :
  (BinCoproductArrow  _ (tensor_left_bp I (F A) _) 
                        c1
                        (st A P · # F u · c2)
  =
        (A_Galg #⊗ identity _) · u) -> u = PInitial_mor A_Galg_PInitial c.
Proof.
  intro h.
  eapply A_Galg_mor_unique.
  etrans;[|exact h].
  apply pathsinv0.
  apply (A_Galg_mor_coprod_commutes P u).
Qed.


Definition A_Galg_mor_eq (P : PIMod) {C : V} (c1 : V ⟦ P , C ⟧)(c2 : V ⟦ F C , C ⟧) u w :
  (BinCoproductArrow  _ (tensor_left_bp I (F A) _) 
                        (λ'  _ · c1) 
                        (st A P · # F u · c2)
  =
  (A_Galg #⊗ identity _) · u) ->
  (BinCoproductArrow  _ (tensor_left_bp I (F A) _) 
                        (λ'  _ · c1)
                        (st A P · # F w · c2)
  =
  (A_Galg #⊗ identity _) · w) ->
  u = w.
Proof.
  intros hu hw.
  etrans; [|apply pathsinv0]; eapply A_Galg_mor_unique'.
  - exact hu.
  - exact hw.
Qed.


(* TODO: utiliser ca pour prouver l'associativité et le fait que m est un morphisme
de module
reflechir s'il vaut mieux faire la version bis
 *)
Definition A_Galg_mor2_equation {P Q : PIMod}{C : V} (γ1 : V ⟦ (I ⊗ P) ⊗ Q , C ⟧)
  (γ2 : V ⟦ F C , C ⟧) (u : V ⟦ (A ⊗ P) ⊗ Q  , C ⟧)
    : UU :=
   ((A_Galg #⊗ identity _) #⊗ identity _) · u =
          BinCoproductArrow _ (tensor_left_bp_gen (tensor_left_bp_gen _ _) _) 
                               γ1 ((st _ P #⊗ identity _) · st _ Q · # F u · γ2) .

Hint Unfold functor_fix_snd_arg_mor BinCoproduct_of_functors_ob bincoproduct_functor BinCoproduct_of_functors_mor stH_data: functor.

Lemma A_Galg_mor2_eq_aux  {P Q : PIMod}{C : V} (γ₁ : V ⟦ (I ⊗ P) ⊗ Q , C ⟧)
  (γ₂ : V ⟦ F C , C ⟧)
  (u1 : V ⟦ (A ⊗ P) ⊗ Q  , C ⟧) :
             ((BinCoproductOfArrows _ (tensor_left_bp_gen _ _) (bc _ _) (identity _) (st A P)  )
          #⊗ identity _) ·
      (BinCoproductOfArrows _ (tensor_left_bp_gen _ _) (bc _ _) (identity _) (st _ Q)  )
      ·
      (BinCoproductOfArrows _ (bc _ _) (bc _ _) (((identity I) #⊗ (identity (P))) #⊗ identity Q) (# F u1))
           · BinCoproductArrow _ (bc _ _) γ₁ γ₂ 
   =
  BinCoproductArrow V (tensor_left_bp_gen (tensor_left_bp_gen (π₁%F (I,, A) + (π₂%F ∙ F) (I,, A)) (P)) Q) γ₁
                    (st A P #⊗ identity Q · st (A ⊗ P) Q · # F u1 · γ₂) .
Proof.
  etrans.
  {
    apply cancel_postcomposition.
    etrans.
    {
      apply cancel_postcomposition.
      etrans.
      {
        apply cancel_postcomposition.
        apply BinCoproductOfArrows_tensor.
      }
      eapply   (BinCoproductOfArrows_comp' (tensor_left_bp_gen (tensor_left_bp_gen _ _) _) (tensor_left_bp_gen _ _)).
    }
    eapply   (BinCoproductOfArrows_comp' (tensor_left_bp_gen (tensor_left_bp_gen _ _) _) ).
  }
  etrans;[apply (precompWithBinCoproductArrow _ (tensor_left_bp_gen (tensor_left_bp_gen _ _) _))|].
  eapply map_on_two_paths; [|apply idpath].
  cbn.
  rewrite id_right.
  etrans;[|apply id_left].
  apply cancel_postcomposition.
  etrans;[|apply id_left].
  now repeat (rewrite <- (functor_id tensor); cbn).
Qed.

Lemma A_Galg_mor2_unique {P Q : PIMod}{C : V} (γ₁ : V ⟦ (I ⊗ P) ⊗ Q , C ⟧)
  (γ₂ : V ⟦ F C , C ⟧)
  (u1 : V ⟦ (A ⊗ P) ⊗ Q  , C ⟧)
  (u2 : V ⟦ (A ⊗ P) ⊗ Q  , C ⟧)
  (eq1 : A_Galg_mor2_equation γ₁ γ₂ u1)
  (eq2 : A_Galg_mor2_equation γ₁ γ₂ u2)
  : u1  = u2.
Proof.
  set (T := fun (Z : PIMod) => φ₂ tensor Z).
  set (J := T P ∙ T Q).
  assert (Jomega :   is_omega_cocont J).
  { apply (is_omega_cocont_functor_composite hsV); use ltensor_cc. }

  set (stT := fun Z => ( (nat_trans_fix_snd_arg _ _ _ _ _ stH (Z : M) )): H ∙ T _ ⟹
                                                           (functor_identity V × T Z)%F ∙ ((T Z × functor_identity V)%F ∙ H)).
  transparent assert (st' : (H ∙ J ⟹ (functor_identity V × J)%F ∙ ((J × functor_identity V)%F ∙ H))).
  {
    eapply nat_trans_comp.
    {
      exact (post_whisker (G := H ∙ T _) (stT _) (T Q)).
    }
    exact  (pre_whisker (T _ × T _)%F (stT _)).
  }
  set (c := BinCoproductArrow _ (bc _ _) γ₁ γ₂) .
  (* A_Falg: V ⟦ (I ⊗ A) ⊗ A + F A , A ⟧ ). *)

  use ( Thm47_eq hsV O Vch hsV Vch (J := J) _ _ (F := H) _
                       (G := (J × functor_identity _)%F ∙ H ) _ (K := functor_identity _) st' c).
  - apply tensor_isInitial.
    apply tensor_isInitial.
    apply pr2.
  - exact Jomega.
  - exact Homega2.
  - use (is_omega_cocont_fix_fst_arg hsV hsV hsV).
    apply (is_omega_cocont_functor_composite hsV).
    + use (is_omega_cocont_pair_functor _ _ hsV hsV hsV hsV).
      * exact Jomega.
      * apply (is_omega_cocont_functor_identity hsV).
    + exact Homega.
  - etrans;[|exact (! eq1)].
    cbn.
    apply A_Galg_mor2_eq_aux.
  - etrans;[|exact (! eq2)].
    cbn.
    apply A_Galg_mor2_eq_aux.
Qed.
  

Definition A_Falg : V ⟦ F A , A ⟧ := ι₂ · A_Galg.


(* Very useful lemma *)
Lemma general_lemma
      {X Y : PIMod}
      (* u is a morphism of PtIModule *)
      (u : PtIModule_Mor (X ⊠M Y)  X)
      (v' : V ⟦ A ⊗ X , A ⟧)
      (w : V ⟦ A ⊗ Y , A ⟧)
  {vv1 : V ⟦ X, A ⟧}
  (veq : (A_Galg #⊗ identity X) · v' =
         BinCoproductArrow V (tensor_left_bp _ _ _) (λ'  _ · vv1)
       (st A X · # F v' · A_Falg))
  (* (eqw' :   A_Falg #⊗ identity (v Y) · w = st A Y · # F w · A_Falg) *)
  {w1 : V ⟦ Y, A ⟧}
  (* Actually, I only need the ι₂ e1 = ι₂ e2 of the following equation e1 = e2 *)
  (eqw' :   A_Galg #⊗ identity Y · w = 
         BinCoproductArrow V (tensor_left_bp _ _ _) (λ'  _ · w1)
       (st A Y · # F w · A_Falg))
  (eqw : (vv1 #⊗ identity Y · w = π X Y · u · vv1))
  :
   αVM A X Y · (identity A #⊗ u) · v' =   (v' #⊗ identity Y) · w.
Proof.
    use (A_Galg_mor2_unique (P := X) (Q := Y) (αVM I X Y · (identity I #⊗ u · (λ'  _ · vv1))) A_Falg).
    - etrans.
      {
        repeat rewrite assoc.
        apply cancel_postcomposition.
        apply cancel_postcomposition.
        apply (V_IModules_assoc_ax _ _ _ _ _ (IModule_identity _ _)(IModule_identity _ _)).
      }
      etrans.
      {
        apply cancel_postcomposition.
        rewrite <- assoc.
        apply cancel_precomposition.
        rewrite IModule_tensor'_id.
        apply (binprod_functor_swap_morphisms tensor).
      }
      etrans.
      {
        apply cancel_postcomposition.
        apply cancel_postcomposition.
        apply  alphaVM_bincoproduct_eq.
      }
      cbn -[A A_Galg].
(* A_action_ax : (λ'  I + st A IM · # F A_action)%m · A_Galg = A_Galg #⊗ identity I · A_action *)
(* m_ax : BinCoproductArrow V (tensor_left_bp I (F A) A) (λ'  A) (st A AM · # F m · ι₂ · A_Galg) = A_Galg #⊗ identity A · m *)
      etrans.
      {
        repeat rewrite <- assoc.
        apply cancel_precomposition.
        apply cancel_precomposition.
        exact veq.
      }
      etrans.
      {
        apply cancel_precomposition.
        etrans.
        {
          apply cancel_postcomposition.
          apply bc_id_tensor.
        }
        apply (precompWithBinCoproductArrow _ (tensor_left_bp_gen _ _)(tensor_left_bp_gen _ _)).
      }
      etrans ; [apply (precompWithBinCoproductArrow _ (tensor_left_bp_gen (tensor_left_bp_gen _ _) _)(tensor_left_bp_gen _ _))|].
    apply maponpaths.
    apply pathsinv0.
    etrans.
    {
      apply cancel_postcomposition.
      rewrite functor_comp, assoc.
      apply cancel_postcomposition.
      apply pathsinv0.
      rewrite functor_comp.
      rewrite assoc.
      apply cancel_postcomposition.
      apply (strength_pentagon_eq st).
    }
    do 3 (etrans;[apply assoc'|]).
    apply cancel_precomposition.
    do 2 (etrans;[apply assoc|]).
    etrans;[|apply assoc'].
    apply cancel_postcomposition.
    etrans;[|apply assoc'].
    apply cancel_postcomposition.
    apply pathsinv0.
    etrans; [|apply (strength_ax st _ u)].
    apply cancel_postcomposition.
    rewrite functor_id.
    apply idpath.
  -   red.
      etrans;[apply assoc|].
      etrans.
      {
        apply cancel_postcomposition.
        etrans;[apply pathsinv0, (functor_comp (φ₂ tensor Y))|].
        exact (maponpaths (fun z => z #⊗ _) veq).
      }
      etrans.
      {
        apply cancel_postcomposition.
        (* etrans; [eapply (maponpaths (fun z => z #⊗ _)), BinCoproductOfIdentities|]. *)
        apply (BinCoproductArrow_tensor (tensor_left_bp _ _ _)).
      }
      etrans ; [apply (postcompWithBinCoproductArrow _ (tensor_left_bp_gen (tensor_left_bp_gen _ _) _))|].
      apply map_on_two_paths.
      + repeat rewrite assoc.
        etrans.
        {
          apply cancel_postcomposition.
          apply (functor_comp (φ₂ tensor (Y))).
        }
        etrans; revgoals.
        {
          apply cancel_postcomposition.
          etrans; revgoals.
          {
            etrans;[|apply  assoc].
            apply cancel_precomposition.
            apply pathsinv0.
            apply (skewmonoidal_unitl_ax).
          }
          apply pathsinv0.
          etrans;[apply assoc|].
          apply cancel_postcomposition.
          apply alphaVM_lambda_eq.
        }
        repeat rewrite <- assoc.
        apply cancel_precomposition.
        etrans;[|apply assoc'].
        exact eqw.
      + etrans.
        {
          apply cancel_postcomposition.
          etrans;[apply (functor_comp (φ₂ tensor _))|].
          apply cancel_postcomposition.
          apply (functor_comp (φ₂ tensor _)).
        }
        repeat rewrite <- assoc.
        apply cancel_precomposition.
        etrans; revgoals.
        {
          etrans;[|apply pathsinv0,assoc].
          apply cancel_postcomposition.
          etrans;[|apply cancel_precomposition, pathsinv0, (functor_comp F)].
          etrans;[|apply pathsinv0,assoc].
          apply cancel_postcomposition.
          apply (strength_ax st v' (identity (C := M) _)).
        }
        repeat rewrite <- assoc.
        apply cancel_precomposition.
        change ( (( A_Falg #⊗ identity Y) · w) = st A Y · (# F w · A_Falg)).
        rewrite assoc.
        change (pr1 (pr1 (Vch (initChain O G)))) with A.
        cbn -[A A_Falg].
        eapply usual_eq2.
        exact eqw'.
Qed.

(* Very useful lemma (the symmetric of the previous one)
TODO: merge the two general_lemmas into a single one
 *)
Lemma general_lemma'
      {X Y : PIMod}
      (* u is a morphism of PtIModule *)
      (u : PtIModule_Mor (Y ⊠M X)  X)
      (v' : V ⟦ A ⊗ X , A ⟧)
      (w : V ⟦ A ⊗ Y , A ⟧)
  {vv1 : V ⟦ X, A ⟧}
  (veq : (A_Galg #⊗ identity X) · v' =
         BinCoproductArrow V (tensor_left_bp _ _ _) (λ'  _ · vv1)
       (st A X · # F v' · A_Falg))
  {w1 : V ⟦ Y, A ⟧}
  (* Actually, I only need the ι₂ e1 = ι₂ e2 of the following equation e1 = e2 *)
  (eqw' :   A_Galg #⊗ identity Y · w = 
         BinCoproductArrow V (tensor_left_bp _ _ _) (λ'  _ · w1)
       (st A Y · # F w · A_Falg))
  (eqw :   w1 #⊗ identity X · v' = π Y X · u · vv1)

  : 
   αVM A Y X · (identity A #⊗ u) · v' =   (w #⊗ identity X) · v'.
Proof.
    use (A_Galg_mor2_unique (P := Y) (Q := X) (αVM I Y X · (identity I #⊗ u · (λ'  _ · vv1))) A_Falg).
    - etrans.
      {
        repeat rewrite assoc.
        apply cancel_postcomposition.
        apply cancel_postcomposition.
        apply (V_IModules_assoc_ax _ _ _ _ _ (IModule_identity _ _)(IModule_identity _ _)).
      }
      etrans.
      {
        apply cancel_postcomposition.
        rewrite <- assoc.
        apply cancel_precomposition.
        rewrite IModule_tensor'_id.
        apply (binprod_functor_swap_morphisms tensor).
      }
      etrans.
      {
        apply cancel_postcomposition.
        apply cancel_postcomposition.
        apply  alphaVM_bincoproduct_eq.
      }
      cbn -[A A_Galg].
(* A_action_ax : (λ'  I + st A IM · # F A_action)%m · A_Galg = A_Galg #⊗ identity I · A_action *)
(* m_ax : BinCoproductArrow V (tensor_left_bp I (F A) A) (λ'  A) (st A AM · # F m · ι₂ · A_Galg) = A_Galg #⊗ identity A · m *)
      etrans.
      {
        repeat rewrite <- assoc.
        apply cancel_precomposition.
        apply cancel_precomposition.
        exact veq.
      }
      etrans.
      {
        apply cancel_precomposition.
        etrans.
        {
          apply cancel_postcomposition.
          apply bc_id_tensor.
        }
        apply (precompWithBinCoproductArrow _ (tensor_left_bp_gen _ _)(tensor_left_bp_gen _ _)).
      }
      etrans ; [apply (precompWithBinCoproductArrow _ (tensor_left_bp_gen (tensor_left_bp_gen _ _) _)(tensor_left_bp_gen _ _))|].
    apply maponpaths.
    apply pathsinv0.
    etrans.
    {
      apply cancel_postcomposition.
      rewrite functor_comp, assoc.
      apply cancel_postcomposition.
      apply pathsinv0.
      rewrite functor_comp.
      rewrite assoc.
      apply cancel_postcomposition.
      apply (strength_pentagon_eq st).
    }
    do 3 (etrans;[apply assoc'|]).
    apply cancel_precomposition.
    do 2 (etrans;[apply assoc|]).
    etrans;[|apply assoc'].
    apply cancel_postcomposition.
    etrans;[|apply assoc'].
    apply cancel_postcomposition.
    apply pathsinv0.
    etrans; [|apply (strength_ax st _ u)].
    apply cancel_postcomposition.
    rewrite functor_id.
    apply idpath.
  - red.
    etrans;[apply assoc|].
    etrans.
    {
      apply cancel_postcomposition.
      etrans;[apply pathsinv0, (functor_comp (φ₂ tensor X))|].
      exact (maponpaths (fun z => z #⊗ _) eqw').
    }
    etrans.
    {
      apply cancel_postcomposition.
      (* etrans; [eapply (maponpaths (fun z => z #⊗ _)), BinCoproductOfIdentities|]. *)
      apply (BinCoproductArrow_tensor (tensor_left_bp _ _ _)).
    }
    etrans ; [apply (postcompWithBinCoproductArrow _ (tensor_left_bp_gen (tensor_left_bp_gen _ _) _))|].
    apply map_on_two_paths.
    + repeat rewrite assoc.
      etrans.
      {
        apply cancel_postcomposition.
        apply (functor_comp (φ₂ tensor _)).
      }
      etrans; revgoals.
      {
        apply cancel_postcomposition.
        etrans; revgoals.
        {
          etrans;[|apply  assoc].
          apply cancel_precomposition.
          apply pathsinv0.
          apply (skewmonoidal_unitl_ax).
        }
        apply pathsinv0.
        etrans;[apply assoc|].
        apply cancel_postcomposition.
        apply alphaVM_lambda_eq.
      }
      repeat rewrite <- assoc.
      apply cancel_precomposition.
      etrans;[|apply assoc'].
      exact eqw.
    + etrans.
      {
        apply cancel_postcomposition.
        etrans;[apply (functor_comp (φ₂ tensor _))|].
        apply cancel_postcomposition.
        apply (functor_comp (φ₂ tensor _)).
      }
      repeat rewrite <- assoc.
      apply cancel_precomposition.
      etrans; revgoals.
      {
        etrans;[|apply pathsinv0,assoc].
        apply cancel_postcomposition.
        etrans;[|apply cancel_precomposition, pathsinv0, (functor_comp F)].
        etrans;[|apply pathsinv0,assoc].
        apply cancel_postcomposition.
        apply (strength_ax st _ (identity (C := M) _)).
      }
      
      repeat rewrite <- assoc.
      apply cancel_precomposition.
      (* change ( (( A_Falg #⊗ identity (v Y)) · w) = st A Y · (# F w · A_Falg)). *)
      change ( (( A_Falg #⊗ identity X) · v') = st A X · (# F v' · A_Falg)).
      rewrite assoc.
      cbn -[A A_Falg].
      eapply usual_eq2.
      exact veq.
Qed.



(* The unit *)
Definition ηA : V ⟦ I , A ⟧ := ι₁ · A_Galg.

(* The I-module structure *)

Definition A_action_aux : V ⟦ I ⊗ I + F A, A ⟧ := (λ'  _ + identity _)%m · A_Galg.
  (* BinCoproductArrow  _ (bc _ _) (λ'  _ · ι₁ · A_Galg) (ι₂ · A_Galg). *)


(*
satisfies:
<<<

                 st
  (I + F(A)) ⊗ I --->  I ⊗ I + F (A ⊗ I) -----> I ⊗ I + F(A)
         |                                            |
         |                                            |
         |                                            |
         |                                            |
         V                                            V
     A ⊗ I  ------------------------------------>     A


>>>
where A = A
 *)
Definition A_action : V ⟦ A ⊗ I , A ⟧ :=
  PInitial_mor A_Galg_PInitial (P := IM) A_action_aux.


Lemma A_action_eq_aux u :
  BinCoproductOfArrows _ (tensor_left_bp I (F A) I) (bc _ _)
                       (identity (I ⊗ I))
                       (st A IM · # F u) · A_action_aux = (λ'  I + st A IM · # F u)%m · A_Galg.
Proof.
  unfold A_action_aux.
  rewrite assoc.
  apply cancel_postcomposition.
  etrans;[use   (BinCoproductOfArrows_comp' (tensor_left_bp _ _ _))|].
  now rewrite id_right,id_left.
Qed.

(* TODO: factor A_action and A_action_ax *)
Lemma A_action_unique u :
  BinCoproductOfArrows  _ (tensor_left_bp I (F A) I) (bc _ _)
                        (λ'  _)
                     (st A IM · # F u) · A_Galg
  =
        (A_Galg #⊗ identity I) · u -> u = A_action.
Proof.
  intro eq.
  use (A_Galg_mor_unique IM A_action_aux ).
  etrans;[|use eq].
  apply A_action_eq_aux.
Qed.

Lemma A_action_ax :
  BinCoproductOfArrows  _ (tensor_left_bp I (F A) I) (bc _ _)
                        (λ'  _)
                     (st A IM · # F A_action) · A_Galg
  =
        (A_Galg #⊗ identity I) · A_action.
Proof.
  etrans;[|use (A_Galg_mor_commutes IM A_action_aux )].
  apply pathsinv0.
  apply A_action_eq_aux.
Qed.
Lemma A_action_ax' :
  BinCoproductArrow  _ (tensor_left_bp I (F A) I) 
                        (λ'  _ · ηA)
                     (st A IM · # F A_action · A_Falg)
  =
        (A_Galg #⊗ identity I) · A_action.
Proof.
  etrans;[|exact A_action_ax].
  cbn -[A A_Galg].
  etrans;[|apply pathsinv0, (postcompWithBinCoproductArrow _ (tensor_left_bp _ _ _))].
  apply map_on_two_paths; apply assoc.
Qed.

Lemma ηA_action :   ηA #⊗ identity I · A_action = λ' I · ηA.
Proof.
  eapply usual_eq1.
  exact (! A_action_ax').
Qed.

Lemma identityA_Thm47_mor_eq :
  identity A = (Thm47_mor hsV O Vch hsV Vch (J := functor_identity _) (pr2 O)
                (is_omega_cocont_functor_identity hsV) (F := H)
                Homega2
          (G := H) Homega2 (K := functor_identity _) (nat_trans_id _ ) A_Galg).
Proof.
  use 
      (Thm47_unique hsV O Vch hsV Vch (J := functor_identity _) (pr2 O)
                (is_omega_cocont_functor_identity hsV) (F := H)
                Homega2
          (G := H) Homega2 (K := functor_identity _) (nat_trans_id _ ) A_Galg).
    change (carrier _) with A.
    change (alg_map _ _) with A_Galg.
    cbn -[A A_Galg].
    autounfold with functor; cbn -[A A_Galg].
    rewrite id_left,id_right.
    etrans.
    {
      apply cancel_postcomposition.
      apply (functor_id H (I , A)).
    }
    apply id_left.
Qed.

Lemma identityA_eq u :  (identity I + # F u)%m · A_Galg = A_Galg · u -> u = identity A.
Proof.
  intro eq.
  etrans;[|exact (! identityA_Thm47_mor_eq)].
  use (Thm47_unique hsV O Vch hsV Vch (J := functor_identity _) (pr2 O)
                (is_omega_cocont_functor_identity hsV) (F := H)
                Homega2
          (G := H) Homega2 (K := functor_identity _) (nat_trans_id _ ) A_Galg).
  rewrite id_left.
  exact eq.
Qed.

Definition A_IModule_data : IModule_data V :=
  make_IModule_data _ A A_action.

Lemma A_action_is_retraction :   ρ A · A_action = identity  A.
Proof.
  apply identityA_eq.
    etrans; revgoals.
    {
      apply pathsinv0.
      etrans;[apply assoc|].
      etrans;[apply cancel_postcomposition, skewmonoidal_unitr_ax|].
      etrans;[apply pathsinv0,assoc|].
      apply cancel_precomposition.
      apply pathsinv0.
      exact A_action_ax.
    }
    rewrite assoc.
    apply cancel_postcomposition.
    apply pathsinv0.
    etrans;[apply rho_bincoproductofarrows_postcomp_eq|].
    cbn -[A A_Galg].
    use BinCoproductOfArrows_eq.
    - apply skewmonoidal_rho_lambda_eq.
    - repeat rewrite assoc.
      etrans.
      {
      apply cancel_postcomposition.
      apply strength_triangle_eq.
      }
      apply pathsinv0, functor_comp.
Qed.


Lemma A_action_law2' :
  αVM A IM IM · (identity A #⊗ λP  IP) · A_action =
   A_action #⊗ identity I · A_action.
Proof.
  eapply ( general_lemma (λP _)).
  - exact (! A_action_ax').
  - exact (! A_action_ax').
  - etrans;[apply ηA_action|].
    apply cancel_postcomposition.
    apply pathsinv0.
    apply IModule_tensor'_Out_eq.
Qed.
  (* - cbn. *)
  (*   apply pathsinv0. *)
  (*   apply I_mult_laws. *)

(*
Lemma A_action_law2 :
  α' A I I · (identity A #⊗ λ'  I) · A_action =
   A_action #⊗ identity I · A_action.
Proof.
  eapply ( general_lemma (λM _)).
  - exact (! A_action_ax').
  - exact (! A_action_ax').
  - exact ηA_action.
  - cbn.
    apply pathsinv0.
    apply I_mult_laws.
Qed.


Lemma A_IModule_laws : IModule_laws _ A_IModule_data.
Proof.
  split.
  - exact A_action_is_retraction.
  - exact A_action_law2.
Qed.
*)




Definition AM : PIMod :=
   make_IModule' V hsV coeqsV tensorl_coeqs _ A_action_is_retraction
                        A_action_law2' ,, (ηA ,, ! ηA_action).


Definition ηAM : PtIModule_Mor IM  AM := ϵPt AM.

(* The multiplication

We use Lemma 4.8
 *)
Definition μA_aux : V ⟦ I ⊗ A + F A, A ⟧.
  use BinCoproductArrow.
  - apply λ' .
  - apply A_Falg.
Defined.
Definition μA : V ⟦ A ⊗ A , A ⟧ :=  PInitial_mor A_Galg_PInitial (P := AM) μA_aux.


Lemma μA_eq_aux u :
  BinCoproductArrow V (tensor_left_bp I (F A) A) (λ'  A) (st A AM · # F u · ι₂ · A_Galg) =
  (identity (I ⊗ AM) + st A AM · # F u)%m · μA_aux.
Proof.
  apply pathsinv0.
  etrans.
  {
    cbn -[A A_Galg].
    unfold stH_data,μA_aux.
    use (precompWithBinCoproductArrow _ (tensor_left_bp _ _ _)).
  }
  unfold A_Falg.
  now rewrite assoc, id_left.
Qed.



Lemma μA_ax : 
  BinCoproductArrow
    _ (tensor_left_bp I (F A) A)  (λ'  _) (st A AM · # F μA · ι₂  · A_Galg)
  = (A_Galg #⊗ identity _) · μA.
Proof.
  etrans;[|use (A_Galg_mor_commutes AM) ].
  apply μA_eq_aux.
Qed.

Lemma μA_ax2 : 
  BinCoproductArrow  _ (tensor_left_bp I (F A) A)
                     (λ'  _ · identity _) (st A AM · # F μA · A_Falg)
  = (A_Galg #⊗ identity _) · μA.
Proof.
  etrans;[|exact μA_ax].
  unfold A_Falg.
  now rewrite assoc, id_right.
Qed.



(* Lemme A2 : e is a left unit for m *)
Lemma Aunitl :   (ηA #⊗ identity _ ) · μA = λ' A .
Proof.
  eapply usual_eq1.
  exact (! μA_ax).
Qed.



Lemma Aunitr_aux : (identity _ #⊗ ηA) · μA = A_action.  
Proof.
  use A_action_unique.
  apply pathsinv0.
  etrans.
  {
    etrans;[apply assoc|].
    etrans.
    {
      apply cancel_postcomposition.
      apply (binprod_functor_swap_morphisms tensor A_Galg ηA).
    }
    etrans;[apply pathsinv0,assoc|].
    apply cancel_precomposition.
    exact (! μA_ax).
  }
  etrans.
  {
    apply cancel_postcomposition.
    apply bc_id_tensor.
  }
  etrans; [apply (precompWithBinCoproductArrow _ (tensor_left_bp_gen _ _)(tensor_left_bp_gen _ _))|].
  apply pathsinv0.
  etrans;[use postcompWithBinCoproductArrow|].
  apply map_on_two_paths.
  - apply pathsinv0.
    etrans;[eapply skewmonoidal_unitl_ax|].
    apply assoc.
  - repeat rewrite assoc.
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    rewrite (functor_comp F).
    etrans;[apply assoc|].
    apply cancel_postcomposition.
    apply pathsinv0.
    rewrite <- (functor_id F).
    apply (strength_ax st (identity A) (ηAM : M ⟦ _ , _ ⟧)).
Qed.

(*

Genre de lemme a factoriser
action module mor
  α' ((A, I), I) · (identity A #⊗ λ'  I) · A_action =
     (A_action #⊗, identity I) · A_action

multiplication module mor
  α' ((A, A), I) · (identity A #⊗ A_action) · m =
     (m #⊗ identity I) · A_action 

associativité
  α' ((A , A), A) · (identity A #⊗ m) · m =
    (m #⊗ identity A) · m.

On a le pattern suivant avec u v w X Y:
 α' (A , X , Y) · (id ⊗ u) · v =
    (v ⊗ id Y) · w

Soit r l'action de A
1. X = I    Y = I     u = λ : I ⊗ I → I    v = r : A ⊗ I → A     w = r : A ⊗ I → A
2. X = A    Y = I     u = r : A ⊗ I → A    v = m : A ⊗ A → A     w = r       "
3. X = A    Y = A     u = m : A ⊗ A → A    v = m      "          w = m : A ⊗ A → A

1)

eqw
  e ⊗ id · r = λ · e

Résolu par le fait que e ⊗ I · r fait quelque chose , et naturalité de λ


2)
eqw
  id ⊗ id · r = r

3)
  id ⊗ id · m = m

*)


Lemma A_action_is_IModule_mor  :
  αVM AM IP (IModule_I V) · identity AM #⊗ σ' IP · A_action = A_action #⊗ identity I · σ AM.
Proof.
    eapply (general_lemma (X := IM) (Y := IM) ( σ' IP )).
    + exact (! A_action_ax').
    + exact (! A_action_ax').
    + etrans; [exact ηA_action|].
      apply cancel_postcomposition.
      apply pathsinv0.
      apply IModule_tensor'_Out_eq.
Qed.

(* Lemma A_action_is_IModule_mor : IModule_Mor V (AM ⊗M IM) AM. *)
(*   Proof. *)
(*     eapply (make_IModule_Mor' V hsV coeqsV tensorl_coeqs) with (f := A_action). *)



  


Definition A_actionM : IModule_Mor V (AM ⊗M IM) AM :=
  make_IModule_Mor' V hsV coeqsV tensorl_coeqs (Y := IM)(Z := AM) A_action A_action_is_IModule_mor.


(* Nécessite de montrer que r est un morphisme de IModule *)
(* TODO: reflechir a factoriser cette preuve avec celle de l'associativité) *)
Lemma μA_is_IModule_mor :
  αVM AM AM IM · identity AM #⊗ σ' AM · μA =
  μA #⊗ identity I · σ AM.
Proof.
    eapply (general_lemma (X := AM) (Y := IM) (σ' AM)).
    +  exact (! μA_ax2).
    + exact (! A_action_ax').
    +  rewrite id_right.
       rewrite (functor_id tensor).
       etrans;[apply id_left|].
       apply pathsinv0.
       apply IModule_tensor'_Out_eq.
Qed.
Lemma μA_unit : ρ I · ηA #⊗ ηA · μA = ηA.
Proof.
  etrans.
  {
    etrans;[apply pathsinv0,assoc|].
    apply cancel_precomposition.

    etrans.
    {
      apply cancel_postcomposition.
      etrans; [apply pathsinv0, (binprod_functor_combine_morphisms _ ηA ηA)|].
      apply binprod_functor_swap_morphisms.
    }
    etrans.
    {
      etrans;[apply pathsinv0,assoc|].
      apply cancel_precomposition.
      apply Aunitl.
    }
    apply skewmonoidal_unitl_ax.
  }
  etrans;[apply assoc|].
  etrans;[|apply id_left].
  apply cancel_postcomposition.
  apply skewmonoidal_rho_lambda_eq.
Qed.

Definition μAM : IModule_Mor V (AM ⊗M AM) AM :=
     (* :=  μA ,, μA_is_IModule_mor. *)
   (make_IModule_Mor' V hsV coeqsV tensorl_coeqs (X := AM)(Y := AM)(Z := AM) μA μA_is_IModule_mor).

(* Lemme A3 *)
Lemma Aunitr : ρ A · (identity _ #⊗ ηA) · μA = identity A.
Proof.
  etrans; [| exact A_action_is_retraction].
  rewrite <- assoc.
  apply cancel_precomposition.
  apply  Aunitr_aux.
Qed.




(*
Lemma I_mult_laws' A : α' I I A · identity I #⊗ λ' A · λ' A = λ' I #⊗ identity A · λ' A.
Proof.
   etrans.
    {
      etrans;[apply pathsinv0,assoc|].
      apply cancel_precomposition.
      apply skewmonoidal_unitl_ax.
    }
    rewrite assoc.
    apply cancel_postcomposition.
    apply skewmonoidal_alpha_lambda_eq.
Qed.
*)

Lemma μA_aux_assoc' :
  αVM A IM AM · identity A #⊗ λP AM · μA = A_action #⊗ identity A · μA.
Proof.
  eapply (general_lemma' (X := AM)(Y := IM)  ( λP AM  )).
   - exact (!μA_ax2).
   - exact (!A_action_ax').
   - etrans;[exact Aunitl|].
     rewrite id_right.
     apply pathsinv0, IModule_tensor'_Out_eq.
Qed.
Lemma μA_aux_assoc :
  α' A I A · identity A #⊗ λ' A · μA = A_action #⊗ identity A · μA.
Proof.
  etrans;[| exact μA_aux_assoc'].
  apply cancel_postcomposition.
  eapply (@V_IModules_assoc_postcomp _ _ _ _  IM AM).
Qed.
(*
  eapply (general_lemma' (X := IM) (Y := AM) ( λM _  )).
   - exact (!μA_ax2).
   - exact (!A_action_ax').
   - cbn -[A].
     etrans;[exact Aunitl|].
     apply pathsinv0, id_right.
   - cbn -[A].
     apply pathsinv0, I_mult_laws'.
Qed.
*)

Definition μAM' : PtIModule_Mor (AM ⊠M AM) AM :=
   IModule_tensor'_Out_PtM V hsV coeqsV tensorl_coeqs μAM μA_aux_assoc μA_unit.

Lemma μA_associativity' :   αVM A AM AM · (identity A #⊗ μAM') · μA
  = (μA #⊗ identity _) · μA.
Proof.
  eapply (general_lemma (X := AM) (Y := AM) ( μAM'  )).
  - exact (! μA_ax2).
  - exact (! μA_ax2).
  - rewrite id_right.
    etrans;[|apply id_left].
    etrans;[apply cancel_postcomposition, (functor_id tensor)|].
    apply cancel_precomposition.
    apply pathsinv0.
    apply IModule_tensor'_Out_eq.
Qed.

Lemma μA_associativity :   α' A A A · (identity A #⊗ μA) · μA
  = (μA #⊗ identity _) · μA.
Proof.
  etrans; [|exact μA_associativity'].
  apply cancel_postcomposition.
  eapply (@V_IModules_assoc_postcomp V hsV coeqsV tensorl_coeqs AM AM).
Qed.



Definition A_monoid : skewMonoid V :=
  (A ,, μA ,, ηA) ,, (! μA_associativity ,, Aunitl ,, Aunitr).

Definition AM' := PtIModule_from_monoid V hsV A_monoid.

(* More useful for path induction *)
Lemma AM_eq' :
  tpair  (T := A ⊗ I --> A) (fun dt => IModule_laws _ (make_IModule_data _ A dt))
  (σ AM)  (pr2 (AM : IModule V))
  (* (pr2 (pr1 AM))  (pr2 AM)  *)
  =
  tpair  (T := A ⊗ I --> A) (fun dt => IModule_laws _ (make_IModule_data _ A dt))
               (σ  AM')  (pr2 (AM' : IModule V)) .
Proof.
  apply subtypePairEquality'.
  - exact (! Aunitr_aux).
  - apply isaprop_IModule_laws.
    exact hsV.
Qed.

Definition maponpaths_AM (P : V -> UU)(Q : ∏ (x : IModule V) , P x) : Q AM = Q AM'
   := transportb
         (X := ∑ (dt : A ⊗ I --> A) , IModule_laws _ (make_IModule_data _ A dt))
      (fun z => Q ((make_IModule_data _ A (pr1 z)) ,, pr2 z) = Q AM') AM_eq' (idpath _).

Definition AM_eq : (AM : IModule V) = (AM' : IModule V) :=
     maponpaths_AM (fun z => _) (fun z => z).

Local Notation η := (sm_unit _).
Local Notation μ := (sm_mult _).



Local Notation κ := am_alg .

Axiom myadmit : forall A, A.

Lemma Fmonoid_equation_Galg
      (X : algMonoid st)
    :  BinCoproductArrow _ (tensor_left_bp_gen _ _) 
                             (λ'  X)
                             (st X (PtIModule_from_monoid _ _ X) · # F (μ X) · κ X)  =
       BinCoproductArrow _ (bc _ _) (η X) (κ X) #⊗ identity X · (μ X).
Proof.
  apply pathsinv0.
  etrans.
  {
    etrans.
    {
      apply cancel_postcomposition.
      apply (BinCoproductArrow_tensor).
    }
    apply (postcompWithBinCoproductArrow _ (tensor_left_bp_gen _ _)).
  }
  apply map_on_two_paths.
  - apply skewMonoid_unitl.
  - apply pathsinv0, ( algMonoid_algeq st).
Qed.

Lemma A_Fmonoid_equation :
    st A (PtIModule_from_monoid _ _ A_monoid) · # F μA · A_Falg =
           A_Falg #⊗ identity A · μA .
Proof.
  etrans; revgoals.
  {
    apply pathsinv0.
    eapply usual_eq2.
    exact (! μA_ax2).
  }
  assert (heq : st A AM = st A AM').
  {
    apply myadmit.
    (* exact (maponpaths_AM (fun Y => V ⟦ F _ ⊗  Y, F (_ ⊗  Y) ⟧) (st A)). *)
  }
  rewrite heq.
  apply idpath.
Qed.

Definition A_Fmonoid : algMonoid st := (A_monoid ,, A_Falg) ,, A_Fmonoid_equation.

Definition Fmonoid_as_Galg (X : algMonoid st) : algebra_ob G :=
  tpair (fun Z => V ⟦ G (Z : V) , (Z : V) ⟧) X
        (BinCoproductArrow _ (bc _ _) (η X) (κ X)).


(** initial morphism *)
Definition iniMor (X : algMonoid st) : V ⟦ A , X ⟧
  := InitialArrow Ai (Fmonoid_as_Galg X) : algebra_mor _ _ _.


(** True for any source, but we make the point for the A only
 *)
Lemma algMonoid_Mor_is_Galg_mor {X  : algMonoid st}
      (m : algMonoid_Mor A_Fmonoid X) :
  is_algebra_mor G (InitialObject Ai) (Fmonoid_as_Galg X) m.
Proof.
  red.
  cbn -[Ai].
  unfold BinCoproduct_of_functors_mor.
  cbn -[Ai].
  etrans;[|apply pathsinv0, precompWithBinCoproductArrow].
  apply BinCoproductArrowUnique; rewrite assoc.
  - etrans;[apply (skewMonoid_Mor_η _ m)|].
    apply pathsinv0, id_left.
  - apply (algMonoid_Mor_alg m).
Qed.

Definition algMor_from_algMonoid_Mor {X : algMonoid st}
           (m : algMonoid_Mor A_Fmonoid X)
  : algebra_mor G (InitialObject Ai) (Fmonoid_as_Galg X) :=
  _ ,, algMonoid_Mor_is_Galg_mor m.

(* it commutes with unit and algebras: ok
And then uniqueness is trivial
 *)
Definition iniMor_commutes_G
           (X : algMonoid st) (i := iniMor X) :
  A_Galg · i = # G i · (BinCoproductArrow _ (bc _ _) (η X) (κ X))
  := algebra_mor_commutes G _ (Fmonoid_as_Galg X) (InitialArrow Ai _ ).

Lemma iniMor_commutes_F 
           (X : algMonoid st) (i := iniMor X) :
  A_Falg · i = # F i · (κ X).
Proof.
  etrans.
  {
    etrans;[apply pathsinv0, assoc|].
    apply cancel_precomposition.
    apply iniMor_commutes_G.
  }
  etrans.
  {
    apply cancel_precomposition.
    apply precompWithBinCoproductArrow.
  }
  eapply BinCoproductIn2Commutes.
Qed.

Lemma iniMor_commutes_η
           (X : algMonoid st) (i := iniMor X) :
  ηA · i = η X.
Proof.
  etrans.
  {
    etrans;[apply pathsinv0, assoc|].
    apply cancel_precomposition.
    apply iniMor_commutes_G.
  }
  etrans.
  {
    apply cancel_precomposition.
    apply precompWithBinCoproductArrow.
  }
  etrans;[eapply BinCoproductIn1Commutes|].
  cbn.
  apply id_left.
Qed.

Lemma useful_lemma_for_i 
      {P : PIMod}
      (X : algMonoid st)
       (i := iniMor X  )
      (XM := PtIModule_from_monoid _ hsV X)
      {j : V ⟦ P , X ⟧} (j_is_IModule_mor : IModule_Mor_laws _ (P : IModule _) (XM : IModule _) j)
      (jM := j ,, j_is_IModule_mor : IModule_Mor V P XM)
      (* (j_unit : ((ϵ P : IModule_Mor _ _ _) : precategory_IModule V hsV ⟦_ , _⟧) · (jM : precategory_IModule V hsV  ⟦ _, (XM : IModule _) ⟧) = (ϵ XM : IModule_Mor _ _ _)) *)
      (j_unit : ϵ P · jM = ϵ XM)
       :
   A_Galg #⊗ identity (P) · i #⊗ j · (μ X) =
   (* la aussi il y a un choix *)
   BinCoproductArrow  _ (tensor_left_bp _ _ _)  (λ'  P · j)
          (* ici il y a un choix *)
                      (st _ _ · (# F (i #⊗ j))  · # F (μ X) · κ X).
Proof.
  set (j' := make_PtIModule_Mor _ _ jM j_unit).
  etrans.
  {
    apply cancel_postcomposition.
    etrans.
    {
      apply pathsinv0,(functor_comp tensor).
    }
    cbn -[A_Galg i].
    rewrite id_left.
    unfold i.
    rewrite iniMor_commutes_G.
    fold i.
    etrans;
      [| exact (functor_comp tensor (# G i #, j)
                             (BinCoproductArrow _ _ (η X) (κ X) #, identity _
                                                ))].
    apply maponpaths.
    apply dirprod_paths.
    * apply idpath.
    * cbn.
      apply pathsinv0, id_right.
  }
  etrans.
  {
    etrans;[apply pathsinv0, assoc|].
    apply cancel_precomposition.
    apply pathsinv0.
    use (Fmonoid_equation_Galg X).
  }
  etrans.
  {
    apply cancel_postcomposition.
    apply BinCoproductOfArrows_tensor.
  }
  etrans.
  {
    apply (precompWithBinCoproductArrow _ (tensor_left_bp_gen _ _)(tensor_left_bp_gen _ _)).
  }
  apply map_on_two_paths.
  - cbn -[i].
    apply skewmonoidal_unitl_ax.
  - cbn -[i].
    repeat rewrite assoc.
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    apply (strength_ax st _ j').
Qed.

Lemma iniMor_IModule_laws
      (X : algMonoid st)
      (i := iniMor X  )
      (XM := IModule_from_monoid _ X) 
      : IModule_Mor_laws V AM XM i.
Proof.
  (*
  split.
  - apply  iniMor_commutes_η.
*)
  - cbn-[A i].
    use (A_Galg_mor_eq IM (η X) (κ X)).
    + etrans;[|rewrite assoc; apply cancel_postcomposition, A_action_ax'].
      etrans;[|apply pathsinv0, (postcompWithBinCoproductArrow _ (tensor_left_bp _ _ _))].
      apply map_on_two_paths.
      * rewrite <- assoc.
        apply cancel_precomposition.
        apply pathsinv0.
        apply iniMor_commutes_η.
      * repeat rewrite <- assoc.
        apply cancel_precomposition.
        rewrite (functor_comp F).
        rewrite <- assoc.
        apply cancel_precomposition.
        apply pathsinv0.
        apply iniMor_commutes_F.
    + apply pathsinv0.
      etrans.
      {
        apply cancel_precomposition.
        etrans; [apply assoc |].
        apply cancel_postcomposition.
        apply binprod_functor_combine_morphisms.
      }
      rewrite assoc.
      etrans.
      {
        use (useful_lemma_for_i (P := IM) ).
        - apply (unit_IModule_Mor_laws _ X).
        - apply id_left.
      }
      apply maponpaths.
      apply cancel_postcomposition.
      repeat rewrite <- assoc.
      apply cancel_precomposition.
      fold i.
      etrans;[apply pathsinv0,functor_comp|].
      apply maponpaths.
      etrans;[|apply assoc'].
      apply cancel_postcomposition.
      apply pathsinv0.
      apply binprod_functor_combine_morphisms.
    Qed.


(* does it commute with the multiplication ? *)
Lemma iniMor_commutes_μ
      (X : algMonoid st)
       (i := iniMor  X)
      (XM := IModule_from_monoid _ X)
      
  :
  i #⊗ i · μ X = μA · i.
Proof.
  use (A_Galg_mor_eq AM i (κ X)); revgoals.
  - rewrite assoc.
    etrans;[| apply cancel_postcomposition, μA_ax2].
    apply pathsinv0.
    etrans;[ apply (postcompWithBinCoproductArrow _ (tensor_left_bp_gen _ _))|].
    apply map_on_two_paths.
    + now rewrite id_right.
    + repeat rewrite <- assoc.
      apply cancel_precomposition.
      etrans;[|apply pathsinv0,cancel_postcomposition,functor_comp].
      rewrite <- assoc.
      apply cancel_precomposition.
      apply iniMor_commutes_F.
  - apply pathsinv0.
    rewrite assoc.
    etrans.
    {
      use useful_lemma_for_i.
      - apply iniMor_IModule_laws.
      - apply iniMor_commutes_η.
    }
    apply maponpaths.
    apply cancel_postcomposition.
    rewrite functor_comp.
    now rewrite assoc.
Qed.

Definition iniMor_Monoid_laws
      (X : algMonoid st)
      (i := iniMor X) : @skewMonoid_Mor_laws _ A_monoid X (iniMor X) :=
   ! (iniMor_commutes_μ X) ,, iniMor_commutes_η X.

Definition iniMor_Monoid (X : algMonoid st) : skewMonoid_Mor _ A_monoid X :=
  iniMor X ,, iniMor_Monoid_laws X.

Definition iniMor_algMonoid (X : algMonoid st) : algMonoid_Mor A_Fmonoid X :=
  iniMor_Monoid X ,, (iniMor_commutes_F X).


Lemma iniMor_unique (X : algMonoid st) (m : algMonoid_Mor A_Fmonoid X) :
  m = iniMor_algMonoid X.
Proof.
  apply (algMonoid_Mor_equiv hsV).
  set (m' := algMor_from_algMonoid_Mor m).
  assert (h' := InitialArrowUnique  Ai (Fmonoid_as_Galg X) m').
  apply (maponpaths (fun z => pr1 z)) in h'.
  exact h'.
Qed.

Definition A_isInitial : isInitial (precategory_algMonoid st) A_Fmonoid :=
    make_isInitial (C := precategory_algMonoid st) A_Fmonoid
                   (fun (X : algMonoid st) =>
                        make_iscontr (iniMor_algMonoid X) (iniMor_unique X)).

Definition algMonoid_Initial : Initial (precategory_algMonoid st) :=
  make_Initial _ A_isInitial.

End A.
