(**
  Definition of the category of I-modules

  Based on the definitions of the category of algebras of an endofunctor
**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import SkewMonoidalCategories.

Local Open Scope cat.


(* Definition of a retract *)
Definition retract {C : precategory}{x y : C}(f : C ⟦ x , y ⟧) : UU :=
  ∑ (g : C ⟦ y , x ⟧), f · g = id _.

Coercion morphism_from_rectract {C : precategory}{x y : C}{f : C ⟦ x , y ⟧}(r : retract f) : C ⟦ y , x ⟧ :=
  pr1 r.

Definition retract_isRetract {C : precategory}{x y : C}{f : C ⟦ x , y ⟧}
           (r : retract f) : f · r = id _ := pr2 r.

(** ** Category of algebras of an endofunctor *)

Section IModule_Definition.

Delimit Scope morphism_scope with m.
Delimit Scope object_scope with o.
Open Scope object_scope.

Context (Mon_V : skewmonoidal_precat).

Let V := skewmonoidal_precat_precat Mon_V.
Let I := skewmonoidal_precat_unit Mon_V.
Let tensor := skewmonoidal_precat_tensor Mon_V.
Notation "X ⊗ Y" := (tensor (X , Y)) : object_scope.
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).
Let α := skewmonoidal_precat_associator Mon_V.
Let λ_ := skewmonoidal_precat_left_unitor Mon_V.
Let ρ := skewmonoidal_precat_right_unitor Mon_V.


Definition IModule_ob : UU := ∑ X : V, I --> X × retract (ρ X).



(* this coercion causes confusion, and it is not inserted when parsing most of the time
   thus removing coercion globally
*)
Definition IMod_carrier (X : IModule_ob) : V := pr1 X.
Local Coercion IMod_carrier : IModule_ob >-> ob.

Definition IMod_unit (X : IModule_ob) : I --> X := pr1 (pr2 X).
Definition IMod_action (X : IModule_ob) : retract (ρ X) :=  (pr2 (pr2 X)).

(** A morphism of an F-algebras (F X, g : F X --> X) and (F Y, h : F Y --> Y)
    is a morphism f : X --> Y such that the following diagram commutes:

    <<
         F f
    F x ----> F y
    |         |
    | g       | h
    V         V
    x ------> y
         f
    >>
 *)
Definition is_IModule_mor (X Y : IModule_ob) (f : IMod_carrier X --> IMod_carrier Y) : UU
  := IMod_unit X · f = IMod_unit Y × IMod_action X · f =  (f #⊗ id _) · IMod_action Y.

Lemma isaprop_is_IModule_mor (hs : has_homsets V){X Y : IModule_ob} (f : IMod_carrier X --> IMod_carrier Y)
  : isaprop (is_IModule_mor X Y f).
Proof.
    apply isapropdirprod; apply hs.
Qed.

Definition IModule_mor (X Y : IModule_ob) : UU :=
  ∑ f : X --> Y, is_IModule_mor X Y f.

Coercion mor_from_IModule_mor (X Y : IModule_ob) (f : IModule_mor X Y) : X --> Y := pr1 f.

Definition isaset_IModule_mor (hs : has_homsets V) (X Y : IModule_ob) : isaset (IModule_mor X Y).
Proof.
  apply (isofhleveltotal2 2).
  - apply hs.
  - intro f.
    apply isasetaprop.
    apply isaprop_is_IModule_mor,hs.
Qed.

Definition IModule_mor_eq (hs : has_homsets V) {X Y : IModule_ob} {f g : IModule_mor X Y}
  : (f : X --> Y) = g ≃ f = g.
Proof.
  apply invweq.
  apply subtypeInjectivity.
  intro a. apply isaprop_is_IModule_mor,hs.
Defined.

Lemma IModule_mor_unit_commutes (X Y : IModule_ob) (f : IModule_mor X Y)
  : IMod_unit X · f = IMod_unit Y.
Proof.
  exact (pr1 (pr2 f)).
Qed.

Lemma IModule_mor_action_commutes (X Y : IModule_ob) (f : IModule_mor X Y)
  : IMod_action X · f =  (f #⊗ id _) · IMod_action Y.
Proof.
  exact (pr2 (pr2 f)).
Qed.

Lemma is_IModule_mor_id X : is_IModule_mor X X (id X).
Proof.
  split.
  - apply id_right.
  - etrans;[apply id_right|].
    apply pathsinv0.
    etrans;[|apply id_left].
    apply cancel_postcomposition.
    eapply (functor_id tensor (_ ,, _) ).
Qed.

Definition IModule_mor_id (X : IModule_ob) : IModule_mor X X := id _ ,, is_IModule_mor_id X.

Lemma is_IModule_mor_comp (X Y Z : IModule_ob) (f : IModule_mor X Y) (g : IModule_mor Y Z)  :
  is_IModule_mor X Z (f · g).
Proof.
  red.
  repeat rewrite assoc.
  rewrite IModule_mor_unit_commutes.
  rewrite IModule_mor_action_commutes.
  repeat rewrite <- assoc.
  rewrite IModule_mor_unit_commutes.
  split.
  - apply idpath.
  - etrans.
    {
       apply cancel_precomposition.
       apply (IModule_mor_action_commutes _ _ g).
    }
    etrans;[apply assoc|].
    apply cancel_postcomposition.
    apply pathsinv0.
    etrans;[|eapply (functor_comp tensor (f #, _) (g #, _))].
    cbn.
    rewrite id_right.
    apply idpath.
Qed.



Definition IModule_mor_comp (X Y Z : IModule_ob) (f : IModule_mor X Y) (g : IModule_mor Y Z)
  : IModule_mor X Z := f · g ,, is_IModule_mor_comp X Y Z f g.

Definition precategory_IMod_ob_mor : precategory_ob_mor := IModule_ob ,, IModule_mor.

Definition precategory_IMod_data : precategory_data.
Proof.
  exists precategory_IMod_ob_mor.
  exists IModule_mor_id.
  exact IModule_mor_comp.
Defined.

Lemma is_precategory_precategory_IMod_data (hs : has_homsets V)
  : is_precategory precategory_IMod_data.
Proof.
  repeat split; intros; simpl.
  - apply IModule_mor_eq.
    + apply hs.
    + apply id_left.
  - apply IModule_mor_eq.
    + apply hs.
    + apply id_right.
  - apply IModule_mor_eq.
    + apply hs.
    + apply assoc.
  - apply IModule_mor_eq.
    + apply hs.
    + apply assoc'.
Qed.

Definition precategory_IModule (hs : has_homsets V)
  : precategory := tpair _ _ (is_precategory_precategory_IMod_data hs).

Local Notation IModule := precategory_IModule.

Lemma has_homsets_IModule (hs : has_homsets V)
  : has_homsets (IModule hs).
Proof.
  intros f g.
  apply isaset_IModule_mor.
  assumption.
Qed.


(** forgetful functor from IModule to its underlying category *)

(* first step of definition *)
Definition forget_algebras_data (hsC: has_homsets V): functor_data (IModule hsC) V.
Proof.
  set (onobs := fun alg : IModule hsC => IMod_carrier alg).
  apply (make_functor_data onobs).
  intros alg1 alg2 m.
  simpl in m.
  exact (mor_from_IModule_mor _ _ m).
Defined.

(* the forgetful functor *)
Definition forget_algebras (hsC: has_homsets V): functor (IModule hsC) V.
Proof.
  apply (make_functor (forget_algebras_data hsC)).
  abstract ( split; [intro alg; apply idpath | intros alg1 alg2 alg3 m n; apply idpath] ).
Defined.




Lemma idtomor_FunctorIMod_commutes (hsC: has_homsets V)(X Y: IModule hsC)(e: X = Y): mor_from_IModule_mor _ _ (idtomor _ _ e) = idtomor _ _ (maponpaths IMod_carrier e).
Proof.
  induction e.
  apply idpath.
Qed.

(* Corollary idtoiso_FunctorIMod_commutes (hsC: has_homsets V)(X Y: IModule hsC)(e: X = Y): mor_from_IModule_mor _ _ (morphism_from_iso (idtoiso e)) = idtoiso (maponpaths IMod_carrier e). *)
(* Proof. *)
(*   unfold morphism_from_iso. *)
(*   do 2 rewrite eq_idtoiso_idtomor. *)
(*   apply idtomor_FunctorIMod_commutes. *)
(* Qed. *)

(* I is a I-module *)
Definition IModule_I : precategory_IMod_ob_mor :=
  (I ,, (id I ,, (λ_ I ,, skewmonoidal_precat_rho_lambda_eq _))).

(* On utilise que l'action de B *)
Lemma IMod_tensor_isRetract (A : IModule_ob)(B : IModule_ob)
   : ρ (A ⊗ B) · (α ((A, B), I) · # tensor (id A #, IMod_action B)) = id (A ⊗ B).
Proof.
    rewrite assoc.
    etrans.
    {
      apply cancel_postcomposition.
      apply skewmonoidal_precat_rho_alpha_eq.
    }
    etrans.
    {
      apply pathsinv0.
      apply (functor_comp tensor).
    }
    etrans;revgoals.
    {
      apply (functor_id tensor).
    }
    apply maponpaths.
    apply dirprod_paths.
    + apply id_left.
    + apply retract_isRetract.
Qed.
Definition IMod_tensor_retract(A : IModule_ob) (B : IModule_ob) : retract (ρ (A ⊗ B)) :=
  (α ((A , B) , I) · (id A #⊗ IMod_action B)) ,, IMod_tensor_isRetract A B.

(* The tensor product of I-modules is a I-module *)
Definition IModule_tensor (A : IModule_ob) (B : IModule_ob) : IModule_ob :=
  (A ⊗ B ,, ρ I · (IMod_unit A #⊗ IMod_unit B) ,, IMod_tensor_retract A B ).

(* left unitor for IModules *)

Lemma IModule_left_unitor_isIModule_mor x :
   is_IModule_mor (IModule_tensor IModule_I x) x ( λ_ x).
Proof.
  red; cbn; split.
  - etrans.
    {
      rewrite <- assoc.
      apply cancel_precomposition.
      apply (nat_trans_ax λ_).
    }
    etrans;[apply assoc|].
    etrans.
    {
      apply cancel_postcomposition.
      apply skewmonoidal_precat_rho_lambda_eq.
    }
    apply id_left.
  - etrans.
    {
      rewrite <- assoc.
      apply cancel_precomposition.
      apply (nat_trans_ax λ_).
    }
    etrans;[apply assoc|].
    apply cancel_postcomposition.
    unfold functor_fix_snd_arg_ob.
    apply skewmonoidal_precat_alpha_lambda_eq.
Qed.

Definition IModule_left_unitor x : IModule_mor (IModule_tensor (IModule_I) x) x :=
  (λ_ x ,, IModule_left_unitor_isIModule_mor x).

Lemma IModule_associator_isIModule_mor x y z :
  is_IModule_mor (IModule_tensor (IModule_tensor x y) z) (IModule_tensor x (IModule_tensor y z)) (α ((x, y), z)).
Proof.
  red; cbn; split.
  - rewrite <- assoc.
    eapply (pathscomp0 (b := _ · ((ρ I #⊗ id _) · (((IMod_unit x #⊗ IMod_unit y) #⊗ (IMod_unit z)) ·
                                            α ((_ , _),_))))).
    {
      apply cancel_precomposition.
      rewrite assoc.
      apply cancel_postcomposition.
      etrans;[| apply functor_comp].
      apply maponpaths.
      apply dirprod_paths.
      + apply idpath.
      + apply pathsinv0, id_left.
    }
    etrans.
    {
      apply cancel_precomposition.
      apply cancel_precomposition.
      apply (nat_trans_ax α _ _ (( IMod_unit x #, IMod_unit y) #, IMod_unit z) ).
    }
    apply pathsinv0.
    eapply (pathscomp0 (b := _ · ((id _ #⊗ ρ I ) · ((IMod_unit x #⊗ (IMod_unit y #⊗ IMod_unit z))
                                             )))).
    {
      apply cancel_precomposition.
      etrans;[| apply functor_comp].
      eapply (maponpaths (fun f => # tensor (f #, _)) ).
      apply pathsinv0,id_left.
    }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans;[|apply assoc].
    apply pathsinv0.
    etrans;[| apply cancel_precomposition, (skewmonoidal_precat_rho_alpha_eq Mon_V)].
    repeat rewrite assoc.
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (nat_trans_ax ρ).
  - etrans; revgoals.
    {
      etrans; revgoals.
      {
        apply cancel_precomposition.
        apply cancel_precomposition.
        apply (pathscomp0 (b := (id x #⊗ α ((_ , _) , _)) · (id x #⊗ (id y #⊗ IMod_action z)))); revgoals.
        {
          etrans.
          {
            apply pathsinv0.
            apply functor_comp.
          }
          apply maponpaths.
          apply dirprod_paths.
          + apply id_left.
          + apply idpath.
        }
        apply idpath.
      }
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply  (skewmonoidal_precat_pentagon_eq Mon_V x y z I).
    }
    repeat rewrite <- assoc.
    apply cancel_precomposition.
    etrans;[| apply (nat_trans_ax α _ _ ((id x #, id y) #, IMod_action z))].
    apply cancel_postcomposition.
    apply (maponpaths (# tensor)).
    apply dirprod_paths.
    + apply pathsinv0, (functor_id tensor (x , y)).
    + apply idpath.
Qed.
Definition IModule_associator x y z : IModule_mor (IModule_tensor (IModule_tensor x y) z)
                                                  (IModule_tensor x (IModule_tensor y z)) :=
  (α ((x , y) , z)) ,, IModule_associator_isIModule_mor x y z.
(* Notation "X ⊗ Y" := ( *)
(* (@functor_on_morphisms *)
(*        (precategory_ob_mor_from_precategory_data *)
(*           (precategory_data_from_precategory (precategory_binproduct (@pr1 _ _ Mon_V) (@pr1 _ _ Mon_V)))) *)
(*        (precategory_ob_mor_from_precategory_data (precategory_data_from_precategory (@pr1 _ _ Mon_V))) *)
(*        (functor_data_from_functor *)
(*           (precategory_data_from_precategory (precategory_binproduct (@pr1 _ _ Mon_V) (@pr1 _ _ Mon_V))) *)
(*           (precategory_data_from_precategory (@pr1 _ _ Mon_V)) tensor) *)
(*        _ *)
(*        _ *)
(*        (@tpair *)
(*           (@precategory_morphisms (precategory_ob_mor_from_precategory_data (precategory_data_from_precategory V)) *)
(*              (IMod_carrier _) (IMod_carrier _)) *)
(*           (fun *)
(*              _ : @precategory_morphisms *)
(*                    (precategory_ob_mor_from_precategory_data (precategory_data_from_precategory V))  *)
(*                    (IMod_carrier _) (IMod_carrier _) => *)
(*            @pr2 _ _ (precategory_ob_mor_from_precategory_data (precategory_data_from_precategory V)) *)
(*              (IMod_carrier _) (IMod_carrier _)) (mor_from_IModule_mor _ _ X) (mor_from_IModule_mor _ _ Y)) *)
(*     (* ((((X : V ⟦ _ , _ ⟧) ,, (Y : V ⟦ _ , _ ⟧)) : _ × _ ) : V ⊠ V ⟦ (_ ,, _), (_ ,,_) ⟧) *) *)
(*        )). *)

                        (* ((((X : V ⟦ _ , _ ⟧) ,, (Y : V ⟦ _ , _ ⟧)) : _ × _ ) : V ⊠ V ⟦ (_ ,, _), (_ ,,_) ⟧)). *)
(* (functor_data_from_functor (precategory_data_from_precategory (@pr1 _ _ Mon_V ⊠ @pr1 _ _ Mon_V)) *)
(*        (precategory_data_from_precategory (@pr1 _ _ Mon_V)) tensor) *)
Lemma IModule_tensor_is_IModule_mor {A B C D : IModule_ob}
           (f : IModule_mor A B)(g : IModule_mor C D) : is_IModule_mor (IModule_tensor A C) (IModule_tensor B D)
                                                                       (f #⊗ g).
Proof.
  split.
  cbn.
  - rewrite <- assoc.
    apply cancel_precomposition.
    etrans;[apply pathsinv0,functor_comp|].
    apply maponpaths.
    apply dirprod_paths; apply IModule_mor_unit_commutes.
  - cbn.
    rewrite <- assoc.
    etrans.
    {
      apply cancel_precomposition.
      etrans;[apply pathsinv0,functor_comp|].
      eapply (maponpaths (# tensor) (t2 := (f · id _ #, _))).
      apply dirprod_paths.
      + cbn.
        rewrite id_right , id_left.
        reflexivity.
      + cbn.
        eapply IModule_mor_action_commutes.
    }
    apply pathsinv0.
    etrans.
    {
      rewrite assoc.
      apply cancel_postcomposition.
      apply (nat_trans_ax α _ _ ((f #, g) #, id _)).
    }
    apply pathsinv0.
    etrans;[|apply assoc].
    apply cancel_precomposition.
    apply pathsinv0.
    exact (! (functor_comp tensor _ _)).
Qed.

Definition IModule_tensor_mor {A B C D : IModule_ob}
           (f : IModule_mor A B)(g : IModule_mor C D) : IModule_mor (IModule_tensor A C) (IModule_tensor B D) := _ ,, IModule_tensor_is_IModule_mor f g.

(* first step of definition *)
Definition IModule_tensor_data (hsC: has_homsets V):
   functor_data ((IModule hsC)⊠ (IModule hsC))(IModule hsC).
Proof.
  set (onobs := fun alg : ((IModule hsC)⊠ (IModule hsC))  => IModule_tensor (pr1 alg)(pr2 alg)).
  apply (make_functor_data (C' := IModule hsC)  onobs).
  intros alg1 alg2 m.
  simpl in m.
  exact (IModule_tensor_mor (pr1 m) (pr2 m)).
Defined.
Lemma IModule_tensor_is_functor (hsC: has_homsets V):
  is_functor (IModule_tensor_data hsC).
Proof.
  split.
  - intro alg.
    apply (IModule_mor_eq hsC).
    apply (functor_id tensor).
  - intros a b c f g.
    apply (IModule_mor_eq hsC).
    etrans;revgoals.
    apply (functor_comp tensor).
    apply idpath.
Qed.

Definition IModule_tensor_functor (hsC: has_homsets V): functor ((IModule hsC)⊠ (IModule hsC))(IModule hsC) :=
  make_functor (IModule_tensor_data hsC) (IModule_tensor_is_functor hsC).

End IModule_Definition.

Notation IModule := precategory_IModule.
