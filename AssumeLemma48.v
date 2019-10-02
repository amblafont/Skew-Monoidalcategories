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
(* Require Import SkewMonoidalFunctors. *)

Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Adamek.
Require Import UniMath.CategoryTheory.Chains.OmegaCocontFunctors.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.graphs.eqdiag.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.FunctorCategory.
(* nat_trans_fix_snd_arg *)

Require Import SkewMonoidalCategories.
Require Import StructuralActions.
Require Import StructuralStrengths.
Require Import IModules.
Require Import Complements.
(* Require Import UniMath.Foundations.NaturalNumbers. *)

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

(* Fix some argument of a bifunctor.
We don't use the original functor_fix_snd_arg because it is better to reuse other definition
 *)
(* Definition functor_fix_fst_arg  (C D E : precategory) (F : C ⊠ D ⟶ E) (c : C) : D ⟶ E := *)
(*   ((constant_functor _ _ c ,, functor_identity _ )%F ∙ F). *)
(* Definition functor_fix_snd_arg  (C D E : precategory) (F : C ⊠ D ⟶ E) (d : D) : C ⟶ E := *)
(*   ((functor_identity _  ,, constant_functor _ _ d  )%F ∙ F). *)

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
Notation "X #⊗ Y" := (# tensor (X #, Y)) (at level 20).
Notation α :=  ( skewmonoidal_precat_associator V).
Notation λ_ :=  (skewmonoidal_precat_left_unitor  V).
Notation ρ := (skewmonoidal_precat_right_unitor V).

(* homsets *)
Context (hsV : has_homsets V).

Let Vcat : category := make_category V hsV.

Notation M := (precategory_IModule V hsV).
Let tensorM := (IModule_tensor_functor V hsV).
Let IM := (IModule_I V : M).
Let λM := (IModule_left_unitor_data V).
Let αM := (IModule_associator_data V).
(* V co complete *)
Context (Vch : Colims_of_shape nat_graph V).
Context (O : Initial  V).
Context (bc : BinCoproducts  V).
Infix "+" := bc : object_scope.



(* _ ⊗ X is omega cocontinuous *)
Context (ltensor_cc : forall (X : V) , is_cocont (φ₂ tensor X)).

(* en fait on s'en fout de la déf *)
Local Definition O_tensor_X_isInitial (X : V) : isInitial _ (O ⊗ X).
Proof.
Admitted.
(*
  set (h := (limits.graphs.initial.equiv_isInitial1 O (pr2 O))).
  set (h' := (ltensor_cc X _ _ _ _ h)).
  eapply (eq_diag_iscolimcocone _ (map_initDiagram_eq hsV _)) in h'.
  set (h'' := make_ColimCocone _ _ _ h').
  use make_isInitial.
  intro b.
  use make_iscontr.
  - eapply (colimArrow h'').
    apply initial.initCocone.
  - intro f.
    eapply (colimArrowUnique h'').
    use empty_rect.
Defined.
*)

Local Definition O_tensor_X_Initial (X : V) : Initial V := make_Initial _ (O_tensor_X_isInitial X).

(* la aussi on s'en fout de la def *)
Local Definition tensor_left_isBinCoproduct (A B : V) (C : V) :
  isBinCoproduct _ (A ⊗ C) (B ⊗ C) ((A + B) ⊗ C)
                 (# (φ₂ tensor C) (BinCoproductIn1 _ _))
                  (# (φ₂ tensor C) (BinCoproductIn2 _ _)).
Proof.
Admitted.


Definition tensor_left_bp (A B : V) (C : V) : BinCoproduct _ (A ⊗ C) (B ⊗ C) :=
  make_BinCoproduct _ _ _ _ _ _ (tensor_left_isBinCoproduct A B C).

(* Infix ";" := (nat_trans_comp _ _ _) (at level 5). *)
Infix "×" := pair_functor  : functor_scope .
Delimit Scope functor_scope with F.

Notation v := (IMod_carrier V).
Notation M_V := (forget_IModules _ hsV).

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
    st2_pw st Z A P · # F ( (id _ ) #, (PInitial_mor p c)) · c = # (φ₂ tensor (v P)) a · (PInitial_mor p c) :=
  pr2 (pr1 (p _ _ c)).

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
   set (st' := ( (nat_trans_fix_snd_arg _ _ _ _ _ st P)): F ∙ J ⟹ (functor_identity V × J)%F ∙ ((J × functor_identity V)%F ∙ F)).
  
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
Local Definition stF_pw (X : V) (Y : M) : V ⟦ F X ⊗ (IMod_carrier _ Y) , F (X ⊗ (IMod_carrier _ Y)) ⟧ := stF_nat (X ,, Y).



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
  (* TODO *)
Admitted.


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


Definition Homega2 (X : V) : is_omega_cocont (φ₁ H X) := is_omega_cocont_fix_fst_arg hsV hsV hsV Homega X.

Definition Gomega : is_omega_cocont G := Homega2 I.

(* Our candidate: the initial algebra of G = I + F *)
Definition Ai := colimAlgInitial hsV O Gomega (Vch (initChain O G)).

Definition A := alg_carrier _ (InitialObject Ai).

(* prevent cbn from unfolding A *)
(* Opaque A. *)
(* Let FHC' : isColimCocone FFchain (F L) Fa := *)
(*   HF Fchain L (colimCocone CC) (isColimCocone_from_ColimCocone CC). *)

(* The algebra structure *)
Definition A_Galg : V ⟦ G A , A ⟧ := alg_map _ _.
(* which is parametric initial *)
Definition A_Galg_PInitial : isPInitial stH A_Galg := lemma48 H stH Homega2 I.
(* Opaque A_Galg. *)

Definition A_Falg : V ⟦ F A , A ⟧ := ι₂ · A_Galg.

(* The unit *)
Definition e : V ⟦ I , A ⟧ := ι₁ · A_Galg.

(* The I-module structure *)

Definition A_action_aux : V ⟦ I ⊗ I + F A, A ⟧ := (λ_ _ + identity _)%m · A_Galg.


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
Definition A_action_data : V ⟦ A ⊗ I , A ⟧ :=
  PInitial_mor A_Galg_PInitial (P := IM) A_action_aux.

Hint Unfold functor_fix_snd_arg_mor BinCoproduct_of_functors_ob bincoproduct_functor BinCoproduct_of_functors_mor: functor.

(* Lemma A_action_eq_aux : UU. *)
(*   refine (ρ (G A) · st2_pw stH I A IM = _). # H (identity _ #, ρ _). *)
Lemma A_action_is_retraction : is_retraction (ρ A) A_action_data.
Proof.
  (* eassert (h : H ∙ functor_identity V ⟹ (functor_identity V × functor_identity V)%F ∙ H). *)
  (* { *)
  (*   apply nat_trans_id. *)
  (*   } *)
  use (Thm47_eq hsV O Vch hsV Vch (J := functor_identity _) (pr2 O)
                (is_omega_cocont_functor_identity hsV) (F := H)
                Homega2
          (G := H) Homega2 (K := functor_identity _) (nat_trans_id _ ) A_Galg).
  - change (carrier _) with A.
    change (alg_map _ _) with A_Galg.
    cbn -[A A_Galg].
    unfold BinCoproduct_of_functors_ob,BinCoproduct_of_functors_mor; cbn -[A A_Galg].
    etrans; revgoals.
    {
      apply pathsinv0.
      etrans;[apply assoc|].
      etrans;[apply cancel_postcomposition, (nat_trans_ax ρ _ _ A_Galg)|].
      etrans;[apply pathsinv0,assoc|].
      apply cancel_precomposition.
      apply pathsinv0.
      apply (PInitial_mor_commutes A_Galg_PInitial (P := IM)).
    }
    fold A_action_data.
    unfold A_action_aux.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans; revgoals.
    {
      repeat rewrite <- assoc.
      apply cancel_precomposition.
      apply cancel_precomposition.
      use (binprod_functor_swap_morphisms (bincoproduct_functor bc)).
    }
    etrans; [apply id_left|].
    etrans; [apply (functor_comp G)|].
    repeat rewrite assoc.
    apply cancel_postcomposition.
    autounfold with functor;  cbn -[A A_Galg].
    autounfold with functor;  cbn -[A A_Galg].
    unfold stH_data;  cbn -[A A_Galg].
    apply pathsinv0.
    etrans.
    {
      rewrite <- assoc.
      apply cancel_precomposition.
      use (precompWithBinCoproductArrow _ (tensor_left_bp _ _ _) ).
    }
    (* use (precompWithBinCoproductArrow _ (tensor_left_bp _ _ _) ). *)
    apply BinCoproductArrowUnique.
    + repeat rewrite assoc.
      etrans.
      {
        apply cancel_postcomposition.
        apply (nat_trans_ax ρ).
      }
      etrans.
      {
        repeat rewrite <- assoc.
        apply cancel_precomposition.
        use (BinCoproductIn1Commutes _ _ _ (tensor_left_bp I (F A) I)).
      }
      etrans;[apply cancel_precomposition, id_left|].
      etrans;[apply assoc|].
      apply cancel_postcomposition.
      use skewmonoidal_precat_rho_lambda_eq.
    + repeat rewrite assoc.
      etrans.
      {
        apply cancel_postcomposition.
        apply (nat_trans_ax ρ).
      }
      etrans.
      {
        repeat rewrite <- assoc.
        apply cancel_precomposition.
        use (BinCoproductIn2Commutes _ _ _ (tensor_left_bp I (F A) I)).
      }
      repeat rewrite assoc.
      apply cancel_postcomposition.
      etrans;[apply id_right|].
      apply tensorial_strength_triangle_eq.
  - change (carrier _) with A.
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


Definition A_action_retract : retract (ρ A) := _ ,, A_action_is_retraction.

Definition AM : IModule_ob V := A ,, e ,, A_action_retract.

(* The multiplication

We use Lemma 4.8
 *)
Definition m_aux : V ⟦ I ⊗ A + F A, A ⟧.
  use BinCoproductArrow.
  - apply λ_.
  - apply A_Falg.
Defined.
Definition m : V ⟦ A ⊗ A , A ⟧ :=  PInitial_mor A_Galg_PInitial (P := AM) m_aux.

Lemma m_ax :
  stH ((I ,  A) , (AM : M))
                  · ( identity _ +  # F m)%m · m_aux = (A_Galg #⊗ identity _) · m.
Proof.
  use (PInitial_mor_commutes A_Galg_PInitial).
Qed.



(* Lemme A2 : e is a left unit for m *)
Lemma e_left_unit_m :   (e #⊗ identity _ ) · m = λ_  A .
Proof.
  cbn -[A].
  etrans.
  {
    unfold e.
    apply cancel_postcomposition.
    apply (functor_comp (φ₂ tensor A)).
  }
  rewrite <- assoc.
  etrans.
  {
    apply cancel_precomposition.
    exact (! m_ax).
  }
  unfold BinCoproduct_of_functors_ob, pr1_functor,pr2_functor, stH, stH_data; cbn-[A].
Admitted.


End A.
