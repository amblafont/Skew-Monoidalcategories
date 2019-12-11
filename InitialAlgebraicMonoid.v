(**
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
Require Import StructuralActions.
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
Context (V : skewmonoidal_precat).


Delimit Scope morphism_scope with m.
Delimit Scope object_scope with o.
Open Scope object_scope.

Notation I :=  (skewmonoidal_precat_unit V).
Notation tensor := (skewmonoidal_precat_tensor V).
Notation "X ⊗ Y" := (tensor (X , Y )).
Let tensor_on_mor {a b c d}
    (f : V ⟦a , b ⟧)(g : V ⟦ c , d ⟧) : V ⟦ a ⊗ c , b ⊗ d ⟧ := # tensor (f #, g).
Infix "#⊗" := (tensor_on_mor) (at level 31).
Notation α' :=  ( skewmonoidal_precat_associator V).
Notation λ'  :=  (skewmonoidal_precat_left_unitor  V).
Notation ρ := (skewmonoidal_precat_right_unitor V).

(* homsets *)
Context (hsV : has_homsets V).

Let Vcat : category := make_category V hsV.

Notation M := (precategory_IModule V hsV).
Notation tensorM := (IModule_tensor_functor V hsV).
Notation "X ⊗ Y" := (tensorM ((X : M) , (Y : M)))  : module_scope.
Delimit Scope module_scope with M.

(** as modules *)
Let IM := (IModule_I V : M).
Let λM := (IModule_left_unitor_data V).
Let αM := (IModule_associator_data V).

(* V co-complete *)
Context (Vch : Colims_of_shape nat_graph V).
Context (O : Initial  V).
Context (bc : BinCoproducts  V).
Infix "+" := bc : object_scope.


(* Infix ";" := (nat_trans_comp _ _ _) (at level 5). *)
Infix "×" := pair_functor  : functor_scope .
Delimit Scope functor_scope with F.

Notation "'v' X" := (X : IModule _) (at level 3).
Notation M_V := (forget_IModules _ hsV).


(** _ ⊗ X is omega cocontinuous *)
Context (ltensor_cc : forall (X : V) , is_cocont (φ₂ tensor X)).



Local Lemma tensor_isInitial {o : V}(Io : isInitial _ o)(X : V) :
  isInitial _ (o ⊗ X).
Proof.
  transparent assert (h : (initial.Initial V)).
  {
    eapply (eq_diag_liftcolimcocone (C := Vcat)).
    - eapply (eq_diag_empty_graph (D := Vcat)).
    - eapply make_ColimCocone.
      apply initial.equiv_isInitial1 in Io.
      eapply (ltensor_cc X) in Io.
      exact Io.
  }
  apply initial.equiv_isInitial2.
  exact (initial.isInitial_Initial h).
Qed.


Local Definition O_tensor_X_isInitial (X : V) : isInitial _ (O ⊗ X) := tensor_isInitial (pr2 _) X.

Local Definition O_tensor_X_Initial (X : V) : Initial V := make_Initial _ (O_tensor_X_isInitial X).

(* la aussi on s'en fout de la def *)
(* (TODO: généralier sur le coproduit) *)
Context ( tensor_left_isBinCoproduct' : ∏ {A B : V} (ccAB : BinCoproduct _ A B) (C : V),
  isBinCoproduct _ (A ⊗ C) (B ⊗ C) (ccAB ⊗ C)
                 (# (φ₂ tensor C) (BinCoproductIn1 _ _))
                  (# (φ₂ tensor C) (BinCoproductIn2 _ _))).
Local Definition tensor_left_isBinCoproduct {A B : V} (ccAB : BinCoproduct _ A B) (C : V) :
  isBinCoproduct _ (A ⊗ C) (B ⊗ C) (ccAB ⊗ C)
                 (# (φ₂ tensor C) (BinCoproductIn1 _ _))
                  (# (φ₂ tensor C) (BinCoproductIn2 _ _)).
Proof.
  apply tensor_left_isBinCoproduct'.
Defined.


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
  use BinCoproductArrowUnique; apply (nat_trans_ax ρ).
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
  : α' (((X + Y), a) , b) =
    BinCoproductOfArrows _ (tensor_left_bp_gen (tensor_left_bp _ _ _)  _)
                         (tensor_left_bp_gen _  _)
                      (α' ((X , a) , b) )
                      (α' ((Y , a) , b) ).
Proof.
  use (BinCoproductArrowUnique _ _ _ (tensor_left_bp_gen (tensor_left_bp _ _ _)  _));
  (etrans; [use (nat_trans_ax α' _ _ ((_ #, _) #, _))|]);
  cbn;
  apply cancel_precomposition;
  eapply (maponpaths (fun z =>  (_ #⊗ z)));
  apply (functor_id tensor).
Qed.
(* F has a strength *)
Definition spec_st2 (F : V ⊠ V ⟶ V) : UU :=
  (F × M_V)%F ∙ tensor ⟹
                            bindelta_pair_functor
                            ((π₁  × M_V)%F ∙ tensor)
                            ( (π₂ × M_V)%F ∙ tensor)
                            ∙ F .

Identity Coercion spec_st2_to_nat : spec_st2 >-> nat_trans.


Definition st2_pw {F : V ⊠ V ⟶ V}(st : spec_st2 F) (C D : V)(E : M) :
  V ⟦ (F (C , D)) ⊗ v E , F (C ⊗ v E , D ⊗ v E) ⟧ := st ((C , D) , E).




(* Parameterized initiality *)
Definition isPInitial {F }(st : spec_st2 F) {Z : V}{A : V}(a : V ⟦ F (Z ,, A) , A ⟧) : UU :=
  ∏ (P : M) (C : V) (c : V ⟦ F (Z ⊗ v P, C), C ⟧),
  ∃! u : V ⟦ A ⊗ v P, C ⟧, st2_pw st Z A P · # F ( (identity _ ) #, u) · c = # (φ₂ tensor (v P)) a · u.

Definition PInitial_mor
  {F }{st : spec_st2 F} {Z : V}{A : V}{a : V ⟦ F (Z ,, A) , A ⟧}
  (p : isPInitial st a)
  {P : M} {C : V} (c : V ⟦ F (Z ⊗ v P, C), C ⟧) : V ⟦ A ⊗ v P, C ⟧ :=
  pr1 (pr1 (p _ _ c)).

Definition PInitial_mor_commutes
  {F }{st : spec_st2 F} {Z : V}{A : V}{a : V ⟦ F (Z ,, A) , A ⟧}
  (p : isPInitial st a)
  {P : M} {C : V} (c : V ⟦ F (Z ⊗ v P, C), C ⟧) :
    st2_pw st Z A P · # F ( identity _ #, (PInitial_mor p c)) · c = # (φ₂ tensor (v P)) a · (PInitial_mor p c) :=
  pr2 (pr1 (p _ _ c)).

Definition PInitial_mor_unique
  {F }{st : spec_st2 F} {Z : V}{A : V}{a : V ⟦ F (Z ,, A) , A ⟧}
  (p : isPInitial st a)
  {P : M} {C : V} (c : V ⟦ F (Z ⊗ v P, C), C ⟧)
  (u : V ⟦ A ⊗ v P, C ⟧) 
    (eq : st2_pw st Z A P · # F ( identity _ #, u) · c = # (φ₂ tensor (v P)) a · u) 
  : u = PInitial_mor p c :=
   base_paths _ _ (iscontr_uniqueness (p _ _ c) (u ,, eq)).

Lemma lemma48_nat_trans_aux
           F P b (J :=  φ₂ tensor (v P))
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
  (J :=  φ₂ tensor (v P)) :
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
  set (J := φ₂ tensor (v P)).
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
      apply pathsinv0, (functor_id tensor (Z , v P)).
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
      apply (functor_id tensor (Z , v P)).
  }
  - intro b.
    eapply (is_omega_cocont_iso hsV );[|apply Fromega].
    use (nat_iso_to_iso (C := Vcat) (D := Vcat)).
    apply lemma48_iso_aux.
  - use (ltensor_cc (v P)).
  - use O_tensor_X_isInitial.
Qed.


Context (F : V ⟶ V) (st : tensorial_strength _ hsV F) (Fomega: is_omega_cocont F).

Let stF_nat :=  (pr1 st : nat_trans _ _ ).
Local Definition stF_pw (X : V) (Y : M) : V ⟦ F X ⊗ (v Y) , F (X ⊗ (v Y)) ⟧ := stF_nat (X ,, Y).



Definition H : V ⊠ V ⟶ V := BinCoproduct_of_functors _ _ bc (pr1_functor _ _) (pr2_functor _ _ ∙ F).


Definition stH_data :
  nat_trans_data ((H × M_V)%F ∙ tensor)
    (((π₁ × M_V) ∙ tensor,, (π₂ × M_V) ∙ tensor)%F ∙ H).
Proof.
  Proof.
  intro X.
  destruct X as [[X1 X2] X3].
  cbn.
  unfold BinCoproduct_of_functors_ob, pr1_functor,pr2_functor; cbn.
  use (BinCoproductOfArrows _ (tensor_left_bp _ _ _) ).
  - exact (identity _).
  - apply stF_pw.
Defined.

Lemma  stH_is_nat : is_nat_trans _ _ stH_data.
Proof.
  intros [[X1 X2] X3] [[Y1 Y2] Y3] [[f1 f2] f3].
  unfold stH_data.
  cbn.
  unfold BinCoproduct_of_functors_ob, pr1_functor,pr2_functor, BinCoproduct_of_functors_mor,stH_data; cbn.
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
  - apply (nat_trans_ax stF_nat _ _ (_ #, _)).
Qed.

Definition stH : spec_st2 H := make_nat_trans _ _ stH_data stH_is_nat.

Definition G := φ₁ H I.

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


(* The algebra structure *)
Definition A_Galg : V ⟦ G A , A ⟧ := alg_map _ _.
(* which is parametric initial *)
Definition A_Galg_PInitial : isPInitial stH A_Galg := lemma48 H stH Homega2 I.


Lemma A_Galg_mor_eq_aux (P : M) {C : V}  (u : V ⟦ A ⊗ v P , C ⟧) :
  BinCoproductOfArrows  _ (tensor_left_bp I (F A) _) (bc _ _)
                        (identity _)
                        (stF_pw A P · # F u) 
  = st2_pw stH I A P · # H (identity (I ⊗ v P) #, u).
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
Definition A_Galg_mor_commutes (P : M) {C : V} (c : V ⟦ I ⊗ v P + F C, C ⟧) :
  BinCoproductOfArrows  _ (tensor_left_bp I (F A) _) (bc _ _)
                        (identity _)
                        (stF_pw A P · # F (PInitial_mor A_Galg_PInitial c)) · c
  =
        (A_Galg #⊗ identity _) · PInitial_mor A_Galg_PInitial c.
Proof.
  etrans;[| apply (PInitial_mor_commutes A_Galg_PInitial)].
  apply cancel_postcomposition.
  apply A_Galg_mor_eq_aux.
Qed.

Definition A_Galg_mor_coprod_commutes (P : M) {C : V}  u 
           (c1 : V ⟦ I ⊗ v P , C ⟧)(c2 : V ⟦ F C, C ⟧)
  (c := BinCoproductArrow _ (bc _ _) c1 c2) :
  (BinCoproductArrow  _ (tensor_left_bp I (F A) _) 
                        c1
                        (stF_pw A P · # F u · c2)
                        =
  (BinCoproductOfArrows  _ (tensor_left_bp I (F A) _) (bc _ _)
                        (identity _)
                        (stF_pw A P · # F u) · c)).
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

Definition A_Galg_mor_unique (P : M) {C : V} (c : V ⟦ I ⊗ v P + F C, C ⟧) u :
  (BinCoproductOfArrows  _ (tensor_left_bp I (F A) _) (bc _ _)
                        (identity _)
                        (stF_pw A P · # F u) · c
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

Definition A_Galg_mor_unique' (P : M) {C : V}  u 
           (c1 : V ⟦ I ⊗ v P , C ⟧)(c2 : V ⟦ F C, C ⟧)
  (c := BinCoproductArrow _ (bc _ _) c1 c2) :
  (BinCoproductArrow  _ (tensor_left_bp I (F A) _) 
                        c1
                        (stF_pw A P · # F u · c2)
  =
        (A_Galg #⊗ identity _) · u) -> u = PInitial_mor A_Galg_PInitial c.
Proof.
  intro h.
  eapply A_Galg_mor_unique.
  etrans;[|exact h].
  apply pathsinv0.
  apply (A_Galg_mor_coprod_commutes P u).
Qed.


Definition A_Galg_mor_eq (P : M) {C : V} (c1 : V ⟦ v P , C ⟧)(c2 : V ⟦ F C , C ⟧) u w :
  (BinCoproductArrow  _ (tensor_left_bp I (F A) _) 
                        (λ'  _ · c1) 
                        (stF_pw A P · # F u · c2)
  =
  (A_Galg #⊗ identity _) · u) ->
  (BinCoproductArrow  _ (tensor_left_bp I (F A) _) 
                        (λ'  _ · c1)
                        (stF_pw A P · # F w · c2)
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
Definition A_Galg_mor2_equation {P Q : M}{C : V} (γ1 : V ⟦ (I ⊗ v P) ⊗ v Q , C ⟧)
  (γ2 : V ⟦ F C , C ⟧) (u : V ⟦ (A ⊗ v P) ⊗ (v Q)  , C ⟧)
    : UU :=
   ((A_Galg #⊗ identity _) #⊗ identity _) · u =
          BinCoproductArrow _ (tensor_left_bp_gen (tensor_left_bp_gen _ _) _) 
                               γ1 ((stF_pw _ P #⊗ identity _) · stF_pw _ Q · # F u · γ2) .

Hint Unfold functor_fix_snd_arg_mor BinCoproduct_of_functors_ob bincoproduct_functor BinCoproduct_of_functors_mor stH_data: functor.

Lemma A_Galg_mor2_eq_aux  {P Q : M}{C : V} (γ₁ : V ⟦ (I ⊗ v P) ⊗ v Q , C ⟧)
  (γ₂ : V ⟦ F C , C ⟧)
  (u1 : V ⟦ (A ⊗ v P) ⊗ (v Q)  , C ⟧) :
             ((BinCoproductOfArrows _ (tensor_left_bp_gen _ _) (bc _ _) (identity _) (stF_pw A P)  )
          #⊗ identity _) ·
      (BinCoproductOfArrows _ (tensor_left_bp_gen _ _) (bc _ _) (identity _) (stF_pw _ Q)  )
      ·
      (BinCoproductOfArrows _ (bc _ _) (bc _ _) (((identity I) #⊗ (identity (v P))) #⊗ identity (v Q)) (# F u1))
           · BinCoproductArrow _ (bc _ _) γ₁ γ₂ 
   =
  BinCoproductArrow V (tensor_left_bp_gen (tensor_left_bp_gen (π₁%F (I,, A) + (π₂%F ∙ F) (I,, A)) (v P)) (v Q)) γ₁
                    (stF_pw A P #⊗ identity (v Q) · stF_pw (A ⊗ v P) Q · # F u1 · γ₂) .
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

Lemma A_Galg_mor2_unique {P Q : M}{C : V} (γ₁ : V ⟦ (I ⊗ v P) ⊗ v Q , C ⟧)
  (γ₂ : V ⟦ F C , C ⟧)
  (u1 : V ⟦ (A ⊗ v P) ⊗ (v Q)  , C ⟧)
  (u2 : V ⟦ (A ⊗ v P) ⊗ (v Q)  , C ⟧)
  (eq1 : A_Galg_mor2_equation γ₁ γ₂ u1)
  (eq2 : A_Galg_mor2_equation γ₁ γ₂ u2)
  : u1  = u2.
Proof.
  set (T := fun Z => φ₂ tensor (v Z)).
  set (J := T P ∙ T Q).
  assert (Jomega :   is_omega_cocont J).
  { apply (is_omega_cocont_functor_composite hsV); use ltensor_cc. }

  set (stT := fun Z => ( (nat_trans_fix_snd_arg _ _ _ _ _ stH Z)): H ∙ T _ ⟹
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
Lemma general_lemma {X Y : M} (u : IModule_Mor V    (X ⊗  Y : IModule _)%M   (X : IModule _) )(v' : V ⟦ A ⊗ v X , A ⟧)
      (w : V ⟦ A ⊗ v Y , A ⟧)
  {vv1 : V ⟦ v X, A ⟧}
  (veq : (A_Galg #⊗ identity (v X)) · v' =
         BinCoproductArrow V (tensor_left_bp _ _ _) (λ'  _ · vv1)
       (stF_pw A X · # F v' · A_Falg))
  (* (eqw' :   A_Falg #⊗ identity (v Y) · w = stF_pw A Y · # F w · A_Falg) *)
  {w1 : V ⟦ v Y, A ⟧}
  (* Actually, I only need the ι₂ e1 = ι₂ e2 of the following equation e1 = e2 *)
  (eqw' :   A_Galg #⊗ identity (v Y) · w = 
         BinCoproductArrow V (tensor_left_bp _ _ _) (λ'  _ · w1)
       (stF_pw A Y · # F w · A_Falg))
  (eqw : (vv1 #⊗ identity (v Y) · w = u · vv1))
  :
   α' ((A , v X) , v Y) · (identity A #⊗ u) · v' =   (v' #⊗ identity (v Y)) · w.
Proof.
    use (A_Galg_mor2_unique (P := X) (Q := Y) (α' ((I, v X), v Y) · (identity I #⊗ u · (λ'  _ · vv1))) A_Falg).
    - etrans.
      {
        repeat rewrite assoc.
        apply cancel_postcomposition.
        apply cancel_postcomposition.
        apply (nat_trans_ax α' _ _ ((_ #, _) #, _)).
      }
      etrans.
      {
        apply cancel_postcomposition.
        rewrite <- assoc.
        apply cancel_precomposition.
        etrans.
        {
          apply cancel_postcomposition.
          cbn -[A A_Galg].
          eapply (maponpaths (fun z => (A_Galg #⊗ z))).
          apply (functor_id tensor).
        }
        apply (binprod_functor_swap_morphisms tensor).
      }
      etrans.
      {
        apply cancel_postcomposition.
        apply cancel_postcomposition.
        apply  alpha_bincoproduct_eq.
      }
      cbn -[A A_Galg].
(* A_action_ax : (λ'  I + stF_pw A IM · # F A_action)%m · A_Galg = A_Galg #⊗ identity I · A_action *)
(* m_ax : BinCoproductArrow V (tensor_left_bp I (F A) A) (λ'  A) (stF_pw A AM · # F m · ι₂ · A_Galg) = A_Galg #⊗ identity A · m *)
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
      do 2 rewrite (functor_comp F), assoc.
      do 2 apply cancel_postcomposition.
      apply pathsinv0.
      use (tensorial_strength_pentagon_eq st).
    }
    change (tensorial_strength_nat_pw st)  with stF_pw.
    repeat rewrite <- assoc.
    apply cancel_precomposition.
    cbn -[A A_Galg].
    repeat rewrite assoc.
    do 2 apply cancel_postcomposition.
    apply pathsinv0.
    rewrite <- (functor_id F).
    apply (nat_trans_ax stF_nat _ _ (_ #, (u : M ⟦_ , _⟧))).
  -   red.
      etrans;[apply assoc|].
      etrans.
      {
        apply cancel_postcomposition.
        etrans;[apply pathsinv0, (functor_comp (φ₂ tensor (v Y)))|].
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
          apply (functor_comp (φ₂ tensor (v Y))).
        }
        etrans; revgoals.
        {
          apply cancel_postcomposition.
          etrans; revgoals.
          {
            etrans;[|apply  assoc].
            apply cancel_precomposition.
            apply pathsinv0.
            apply (nat_trans_ax λ' ).
          }
          apply pathsinv0.
          etrans;[apply assoc|].
          apply cancel_postcomposition.
          apply skewmonoidal_precat_alpha_lambda_eq.
        }
        repeat rewrite <- assoc.
        apply cancel_precomposition.
        change (vv1 #⊗ identity (v Y) · w = u · vv1).
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
          use (nat_trans_ax stF_nat _ _ (_ #, identity _)).
        }
        repeat rewrite <- assoc.
        apply cancel_precomposition.
        change ( (( A_Falg #⊗ identity (v Y)) · w) = stF_pw A Y · (# F w · A_Falg)).
        rewrite assoc.
        change (pr1 (pr1 (Vch (initChain O G)))) with A.
        cbn -[A A_Falg].
        eapply usual_eq2.
        exact eqw'.
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
                       (stF_pw A IM · # F u) · A_action_aux = (λ'  I + stF_pw A IM · # F u)%m · A_Galg.
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
                     (stF_pw A IM · # F u) · A_Galg
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
                     (stF_pw A IM · # F A_action) · A_Galg
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
                     (stF_pw A IM · # F A_action · A_Falg)
  =
        (A_Galg #⊗ identity I) · A_action.
Proof.
  etrans;[|exact A_action_ax].
  cbn -[A A_Galg].
  etrans;[|apply pathsinv0, (postcompWithBinCoproductArrow _ (tensor_left_bp _ _ _))].
  apply map_on_two_paths; apply assoc.
Qed.

Lemma ηA_action :   ηA #⊗ identity (v IM) · A_action = λM (pr2 (IM, IM)) · ηA.
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
  A ,, (A_action ,, ηA).

Lemma A_action_is_retraction :   ρ A · A_action = identity  A.
Proof.
  apply identityA_eq.
    etrans; revgoals.
    {
      apply pathsinv0.
      etrans;[apply assoc|].
      etrans;[apply cancel_postcomposition, (nat_trans_ax ρ _ _ A_Galg)|].
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
    - apply skewmonoidal_precat_rho_lambda_eq.
    - repeat rewrite assoc.
      etrans.
      {
      apply cancel_postcomposition.
      apply tensorial_strength_triangle_eq.
      }
      apply pathsinv0, functor_comp.
Qed.



Lemma A_action_law2 :
  α' ((A,, I),, I) · # tensor (identity A #, λ'  I) · A_action =
  # tensor (A_action #, identity I) · A_action.
Proof.
  eapply ( general_lemma (λM _)).
  - exact (! A_action_ax').
  - exact (! A_action_ax').
  - exact ηA_action.
Qed.


Lemma A_IModule_laws : IModule_laws _ A_IModule_data.
Proof.
  split.
  - exact A_action_is_retraction.
  - exact A_action_law2.
Qed.




Definition AM : IModule V := A_IModule_data ,, A_IModule_laws.

Lemma ηA_is_Imodule_mor : IModule_Mor_laws _ (IM : IModule _) AM ηA.
Proof.
  split.
  - apply id_left.
  - apply pathsinv0, ηA_action.
Qed.

Definition ηAM : IModule_Mor V (IM : IModule _) AM :=  ηA ,, ηA_is_Imodule_mor.

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
  BinCoproductArrow V (tensor_left_bp I (F A) A) (λ'  A) (stF_pw A AM · # F u · ι₂ · A_Galg) =
  (identity (I ⊗ v AM) + stF_pw A AM · # F u)%m · μA_aux.
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
    _ (tensor_left_bp I (F A) A)  (λ'  _) (stF_pw A AM · # F μA · ι₂  · A_Galg)
  = (A_Galg #⊗ identity _) · μA.
Proof.
  etrans;[|use (A_Galg_mor_commutes AM) ].
  apply μA_eq_aux.
Qed.

Lemma μA_ax2 : 
  BinCoproductArrow  _ (tensor_left_bp I (F A) A)
                     (λ'  _ · identity _) (stF_pw A AM · # F μA · A_Falg)
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
    etrans;[eapply (nat_trans_ax λ'  _ _ ηA)|].
    apply assoc.
  - repeat rewrite assoc.
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    rewrite (functor_comp F).
    etrans;[apply assoc|].
    apply cancel_postcomposition.
    apply pathsinv0.
    rewrite <- (functor_id F).
    exact (nat_trans_ax stF_nat _ _ (identity A #, (ηAM : M ⟦ _ , _ ⟧))).
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



  (* (v' #⊗ identity Y) *)
    (* (v' #⊗ identity Y) · w). *)


Lemma A_action_is_IModule_mor : IModule_Mor_laws V (AM ⊗ IM : IModule _)%M AM A_action.
Proof.
  split.
  - cbn.
    etrans;[|apply id_left].
    etrans;[|apply cancel_postcomposition, skewmonoidal_precat_rho_lambda_eq]. 
    repeat rewrite <- assoc.
    apply cancel_precomposition.
    exact ηA_action.
  - cbn -[A].
    eapply (general_lemma (X := IM) (Y := IM) ( λM _ )).
    + exact (! A_action_ax').
    + exact (! A_action_ax').
    + exact ηA_action.
Qed.


Definition A_actionM : IModule_Mor V (AM ⊗ IM : IModule _)%M AM :=
  A_action ,, A_action_is_IModule_mor.

(* Nécessite de montrer que r est un morphisme de IModule *)
(* TODO: reflechir a factoriser cette preuve avec celle de l'associativité) *)
Lemma μA_is_IModule_mor : IModule_Mor_laws V (AM ⊗ AM : IModule _)%M AM μA.
Proof.
  split.
  - cbn.
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
      apply (nat_trans_ax λ' ).
    }
    etrans;[apply assoc|].
    etrans;[|apply id_left].
    apply cancel_postcomposition.
    apply skewmonoidal_precat_rho_lambda_eq.
  - cbn -[A].
    eapply (general_lemma (X := AM) (Y := IM) A_actionM).
    +  exact (! μA_ax2).
    + exact (! A_action_ax').
    +  rewrite id_right.
       etrans;[|apply id_left].
       apply cancel_postcomposition.
       apply (functor_id tensor).

Qed.





Definition μAM : IModule_Mor V (AM ⊗ AM : IModule _)%M AM :=  μA ,, μA_is_IModule_mor.
(* Lemme A3 *)
Lemma Aunitr : ρ A · (identity _ #⊗ ηA) · μA = identity A.
Proof.
  etrans; [| exact A_action_is_retraction].
  rewrite <- assoc.
  apply cancel_precomposition.
  apply  Aunitr_aux.
Qed.








Lemma μA_associativity :   α' ((A , A), A) · (identity A #⊗ μA) · μA
  = (μA #⊗ identity _) · μA.
Proof.

  eapply (general_lemma (X := AM) (Y := AM) ( μAM  )).
  - exact (! μA_ax2).
  - exact (! μA_ax2).
  - rewrite id_right.
    etrans;[|apply id_left].
    apply cancel_postcomposition.
    apply (functor_id tensor).
Qed.


Definition A_monoid : skewMonoid V :=
  (A ,, μA ,, ηA) ,, (! μA_associativity ,, Aunitl ,, Aunitr).

Definition AM' := IModule_from_monoid V A_monoid.

(* More useful for path induction *)
Lemma AM_eq' : ((pr2 (pr1 AM) ,, pr2 AM) : ∑ (dt : A ⊗ I --> A × I --> A) , IModule_laws _ (A ,, dt)) = 
               ((pr2 (pr1 AM') ,, pr2 AM') : ∑ (dt : A ⊗ I --> A × I --> A) , IModule_laws _ (A ,, dt)).
Proof.
  apply subtypePairEquality'.
  - apply dirprodeq.
    + exact (! Aunitr_aux).
    + apply idpath.
  - apply isaprop_IModule_laws.
    exact hsV.
Qed.

Definition maponpaths_AM (P : V -> UU)(Q : ∏ (x : IModule V) , P x) : Q AM = Q AM'
   := transportb
         (X := ∑ (dt : A ⊗ I --> A × I --> A) , IModule_laws _ (A ,, dt))
      (fun z => Q ((A ,, pr1 z) ,, pr2 z) = Q AM') AM_eq' (idpath _).

Definition AM_eq : AM = AM' := maponpaths_AM
                                 (fun z => _) ( fun z => z) .
  

Local Notation η := (sm_unit _).
Local Notation μ := (sm_mult _).


(* Equation that a F-monoid X should satisfy *)
(* Definition Fmonoid_equation (X : skewMonoid V) *)
(*            (algX : V ⟦ F X , X⟧) *)
(*   : UU := *)
(*   stF_pw X (IModule_from_monoid _ X) · # F (μ X) · algX = *)
(*            algX #⊗ identity X · (μ X). *)

Local Notation κ := am_alg .

Lemma Fmonoid_equation_Galg
      (X : algMonoid st)
      (* (X : skewMonoid V) *)
      (* (algX : V ⟦ F X , X⟧) *)
      (*      (eqx : Fmonoid_equation X algX) *)
    :  BinCoproductArrow _ (tensor_left_bp_gen _ _) 
                             (λ'  X)
                             (stF_pw X (IModule_from_monoid _ X) · # F (μ X) · κ X)  =
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
    stF_pw A (IModule_from_monoid _ A_monoid) · # F μA · A_Falg =
           A_Falg #⊗ identity A · μA .
Proof.
  etrans; revgoals.
  {
    apply pathsinv0.
    eapply usual_eq2.
    exact (! μA_ax2).
  }
  assert (heq : stF_pw A AM = stF_pw A AM').
  {
    exact (maponpaths_AM (fun Y => V ⟦ F _ ⊗  Y, F (_ ⊗  Y) ⟧) (stF_pw A)).
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
  (*
  etrans;[apply postcompWithBinCoproductArrow|].
  apply map_on_two_paths.
  - etrans;[apply skewMonoid_Mor_η|].
    apply pathsinv0, id_left.
  - apply algMonoid_Mor_alg.
*)
Qed.

Definition algMor_from_algMonoid_Mor {X : algMonoid st}
           (m : algMonoid_Mor A_Fmonoid X)
  : algebra_mor G (InitialObject Ai) (Fmonoid_as_Galg X) :=
  _ ,, algMonoid_Mor_is_Galg_mor m.

(* Definition algMor_from_algMonoid_Mor {X Y : algMonoid st} *)
(*            (m : algMonoid_Mor X Y) *)
(*   : algebra_mor G (Fmonoid_as_Galg X)(Fmonoid_as_Galg Y) := *)
(*   _ ,, algMonoid_Mor_is_Galg_mor m. *)

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
      {P : M}
      (X : algMonoid st)
       (i := iniMor X  )
      (XM := IModule_from_monoid _ X)
      {j : V ⟦ v P , X ⟧} (j_is_IModule_mor : IModule_Mor_laws _ (P : IModule _) (XM : IModule _) j)
       :
   A_Galg #⊗ identity (v P) · i #⊗ j · (μ X) =
   (* la aussi il y a un choix *)
   BinCoproductArrow  _ (tensor_left_bp _ _ _)  (λ'  (v  P) · j)
          (* ici il y a un choix *)
                      (stF_pw _ _ · (# F (i #⊗ j))  · # F (μ X) · κ X).
                      (* ((# F i #⊗ j) · stF_pw X (X ,, eX ,, rX) · # F mX · algX). *)
                      (* ((# F i #⊗ j) · algX #⊗ identity _ · mX). *)
                      (* ((# F i · algX) #⊗ j · mX). *)
Proof.
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
    apply (nat_trans_ax λ' ).
  - cbn -[i].
    repeat rewrite assoc.
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    apply (nat_trans_ax stF_nat _ _ (i #, (j ,, j_is_IModule_mor : M ⟦ _ , XM ⟧))).
Qed.

Lemma iniMor_IModule_laws
      (* {X : V} (eX : V ⟦ I , X⟧) (mX : V ⟦X ⊗ X , X⟧) *)
      (X : algMonoid st)
      (i := iniMor X  )
      (* (left_unitX:   eX #⊗ identity X · mX = λ'  X) *)
      (* (right_unitX : ρ X · identity X #⊗ eX · mX = identity X  ) *)
      (* (pentagon : mX #⊗ identity X · mX = pr1 α' ((X, X), X) · identity X #⊗ mX · mX) *)
      (XM := IModule_from_monoid _ X) 
      (* (rX := (retract_from_partial_monoid  right_unitX)) *)
      : IModule_Mor_laws V AM XM i.
Proof.
  split.
  - apply  iniMor_commutes_η.
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
        rewrite assoc.
        apply cancel_postcomposition.
        apply binprod_functor_combine_morphisms.
      }
      rewrite assoc.
      etrans.
      {
        use (useful_lemma_for_i (P := IM) ).
        apply (unit_IModule_Mor_laws _ X).
      }
      apply maponpaths.
      apply cancel_postcomposition.
      repeat rewrite <- assoc.
      apply cancel_precomposition.
      fold i.
      etrans;[apply pathsinv0,functor_comp|].
      apply maponpaths.
      rewrite assoc.
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
      apply iniMor_IModule_laws.
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

End A.