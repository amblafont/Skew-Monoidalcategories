(**
  Definition of the category of pointed I-modules (can be generalized to X-Modules,
for any monoid X)

An I-module is a module over the skew monoid I (whose multiplication is given
by λ_I : I ⊗ I → I), that is:
- an object X
- a morphism x : X ⊗ I → X
 s.t. the following diagrams commute:
<<<
   ρ
X --> X ⊗ I
\\      |
 \\     |  x
  \\    |
   \\   |
    \\  |
     \\ |
      \\V
        X
>>>
(i.e. x is a retract of ρ)

and

<<<
           α               X ⊗ λ
X ⊗ I ⊗ I ---> X ⊗ (I ⊗ I) ----> X ⊗ I
   |                               |
   |                               |
x⊗I|                               | x
   |                               |
   V                               V
 X ⊗ I --------------------------> X
                   x

>>>

In the skew monoidal setting, not all objects are modules over I.


Skew monoids induce IModules (quick explanation: any monoid morphism induce
a functor between categories of modules, and I is the initial monoid).

**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.eqdiag.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.SkewMonoidal.SkewMonoidalCategories.
Require Import UniMath.CategoryTheory.SkewMonoidal.CategoriesOfMonoids.
Require Import Complements.

Local Open Scope cat.


Section IModule_Definition.

Delimit Scope morphism_scope with m.
Delimit Scope object_scope with o.
Open Scope object_scope.

Context (V : skewmonoidal_precategory).
Context (hsV : has_homsets V).

Notation "( c , d )" := (make_precatbinprod c d).
Notation "( f #, g )" := (precatbinprodmor f g).
Notation "C ⊠ D" := (precategory_binproduct C D) (at level 38).

(* Implicit coercions do not work for reversible notations *)
Notation tensor := (skewmonoidal_tensor (data_from_skewmonoidal V)).
Notation I := (skewmonoidal_I (data_from_skewmonoidal V)).
Notation "X ⊗ Y" := (tensor (X , Y)).
Notation "f #⊗ g" :=
   (functor_on_morphisms (functor_data_from_functor _ _ tensor) (f #, g))
                         (at level 31).


Notation α' := (skewmonoidal_assoc (data_from_skewmonoidal V)).
Notation λ' := (skewmonoidal_unitl (data_from_skewmonoidal V)).
Notation ρ' := (skewmonoidal_unitr (data_from_skewmonoidal V)).


Definition IModule_data : UU
  := ∑ F , F ⊗ I --> F.

Definition make_IModule_data F (Z : F ⊗ I --> F) : IModule_data :=
  tpair (fun F => V ⟦ F ⊗ I, F ⟧) F Z.

Coercion ob_from_IModule_data (F : IModule_data)
  : V := pr1 F.

Definition im_action  (F : IModule_data) : F⊗ I --> F := pr2 F.

Local Notation σ := im_action.

Definition IModule_laws  (T : IModule_data) : UU :=
      ( ρ' T · σ T  = identity _)
        × ( α' T I I · (identity _) #⊗ ((λ' I) ) · σ T  =
            σ T #⊗ identity I · σ T ).

Lemma isaprop_IModule_laws   (T : IModule_data ) :
   isaprop (IModule_laws T).
Proof.
  repeat apply isapropdirprod; apply hsV.
Qed.

Definition IModule : UU := ∑ X : IModule_data, IModule_laws X.

Coercion IModule_data_from_IModule  (T : IModule) : IModule_data  := pr1 T.

Definition IModule_isRetract  (T : IModule ) :  ρ' T · σ T  = identity _ :=
  pr1 (pr2 T).

Definition IModule_law2  (T : IModule ) :
          α' T I I · (identity T) #⊗ ((λ' I) ) · σ T  =
            σ T #⊗ identity I · σ T 
   :=
  pr2 (pr2 T).


Local Notation η := (sm_unit _).
Local Notation μ := (sm_mult _).

Local Notation φ₁ := (functor_fix_fst_arg _ _ _).
Local Notation φ₂ := (functor_fix_snd_arg _ _ _).


Definition IModule_Mor_laws  (X Y : IModule_data ) (f : X --> Y)
  : UU
  :=  σ X · f =  (f #⊗ identity _) · σ Y.

Lemma isaprop_IModule_Mor_laws
  (T T' : IModule_data ) (α : T --> T')
  : isaprop (IModule_Mor_laws T T' α).
Proof.
   apply hsV.
Qed.

Definition IModule_Mor  (T T' : IModule_data ) : UU
  := ∑ α : T --> T', IModule_Mor_laws T T' α.

Coercion mor_from_IModule_Mor (X Y : IModule_data) (f : IModule_Mor X Y) : X --> Y := pr1 f.


Definition IModule_Mor_action (X Y : IModule_data) (f : IModule_Mor X Y)
  : σ X · f =  (f #⊗ identity _) · σ Y
                                           := pr2 f.


Definition isaset_IModule_Mor (X Y : IModule_data) : isaset (IModule_Mor X Y).
Proof.
  apply isaset_total2 .
  - apply hsV.
  - intro f.
    apply isasetaprop.
    apply isaprop_IModule_Mor_laws.
Qed.

Definition IModule_Mor_equiv  {X Y : IModule_data} {f g : IModule_Mor X Y}
  : (f : X --> Y) = g ≃ f = g.
Proof.
  apply invweq.
  apply subtypeInjectivity.
  intro a. apply isaprop_IModule_Mor_laws.
Defined.


Lemma IModule_identity_laws X : IModule_Mor_laws X X (identity X).
Proof.
  etrans;[apply id_right|].
  apply pathsinv0.
  etrans;[|apply id_left].
  apply cancel_postcomposition.
  eapply (functor_id tensor (_ ,, _) ).
Qed.

Definition IModule_identity (X : IModule_data) : IModule_Mor X X :=
  identity _ ,, IModule_identity_laws X.

Lemma IModule_composition_laws (X Y Z : IModule_data) (f : IModule_Mor X Y) (g : IModule_Mor Y Z)  :
  IModule_Mor_laws X Z (f · g).
Proof.
  red.
  repeat rewrite assoc.
  rewrite IModule_Mor_action.
  repeat rewrite <- assoc.
  etrans.
  {
     apply cancel_precomposition.
     apply (IModule_Mor_action _ _ g).
  }
  etrans;[apply assoc|].
  apply cancel_postcomposition.
  apply pathsinv0.
  etrans;[|eapply (functor_comp tensor (f #, _) (g #, _))].
  cbn.
  rewrite id_right.
  apply idpath.
Qed.



Definition IModule_composition (X Y Z : IModule_data)
           (f : IModule_Mor X Y) (g : IModule_Mor Y Z)
  : IModule_Mor X Z := f · g ,, IModule_composition_laws X Y Z f g.

Definition precategory_IMod_ob_mor : precategory_ob_mor :=
  make_precategory_ob_mor IModule IModule_Mor. 

Definition precategory_IMod_data : precategory_data.
Proof.
  use make_precategory_data.
  - exact precategory_IMod_ob_mor.
  - intro. apply IModule_identity.
  - intros ???; apply IModule_composition.
Defined.

Lemma is_precategory_precategory_IMod_data
  : is_precategory precategory_IMod_data.
Proof.
  repeat split; intros; simpl.
  - apply IModule_Mor_equiv.
    + apply id_left.
  - apply IModule_Mor_equiv.
    + apply id_right.
  - apply IModule_Mor_equiv.
    + apply assoc.
  - apply IModule_Mor_equiv.
    + apply assoc'.
Qed.

Definition precategory_IModule
  : precategory := tpair _ _ is_precategory_precategory_IMod_data .

Local Notation IMOD := precategory_IModule.

Lemma has_homsets_IModule
  : has_homsets IMOD.
Proof.
  intros f g.
  apply isaset_IModule_Mor.
Qed.


(** forgetful functor from IModule to its underlying category *)

(* first step of definition *)
Definition forget_IModules_data : functor_data IMOD V.
Proof.
  set (onobs := fun alg : IMOD =>  (alg : IModule )).
  apply (make_functor_data onobs).
  intros alg1 alg2 m.
  simpl in m.
  exact (mor_from_IModule_Mor _ _ m).
Defined.

(* the forgetful functor *)
Definition forget_IModules : functor IMOD V.
Proof.
  apply (make_functor (forget_IModules_data )).
  abstract ( split; [intro alg; apply idpath | intros alg1 alg2 alg3 m n; apply idpath] ).
Defined.




Lemma idtomor_FunctorIMod (X Y: IMOD )(e: X = Y):
  mor_from_IModule_Mor _ _ (idtomor _ _ e) = idtomor _ _
                                                     (maponpaths (fun (x : IModule) => (x : V)) e).
Proof.
  induction e.
  apply idpath.
Qed.


(*
forgetful functor creates colimits (and also limits)
 *)
Definition forget_IMod_creates_colim_action_data
            {g : graph}{d : diagram g IMOD}
      (dV := (mapdiagram forget_IModules d))
      (cc : ColimCocone dV) 
      (c := colim cc)
      (* true if the tensor is left cocontinuous *)
      (is_ccV : preserves_colimits_of_shape (φ₂ tensor I) g)
       : c ⊗ I --> c.
Proof.
  set (ccV := make_ColimCocone _ _ _ (is_ccV _ _ _ (isColimCocone_from_ColimCocone cc))).
  change (colim ccV --> (colim cc )).
  unshelve eapply colimOfArrows.
  - intro.
    apply σ.
  - intros u v e.
    cbn.
    apply pathsinv0.
    apply IModule_Mor_action.
Defined.

Definition forget_IMod_creates_colim_data
            {g : graph}{d : diagram g IMOD}
      (dV := (mapdiagram forget_IModules d))
      (cc : ColimCocone dV) 
      (c := colim cc)
      (* true if the tensor is left cocontinuous *)
      (is_ccV : preserves_colimits_of_shape (φ₂ tensor I) g)
  : IModule_data :=
  make_IModule_data c (forget_IMod_creates_colim_action_data  cc is_ccV).

Lemma forget_IMod_creates_colimIn_IMod_Mor_laws
            {g : graph}{d : diagram g IMOD}
      (dV := (mapdiagram forget_IModules d))
      (cc : ColimCocone dV) 
      (c := colim cc)
      (* true if the tensor is left cocontinuous *)
      (is_ccV : preserves_colimits_of_shape (φ₂ tensor I) g)
  : ∏ (u : vertex g),
    IModule_Mor_laws _ (forget_IMod_creates_colim_data cc is_ccV)
                     (colimIn cc u).
Proof.
  set (ccV := make_ColimCocone _ _ _ (is_ccV _ _ _ (isColimCocone_from_ColimCocone cc))).
  intro u.
  red.
  cbn.
  apply pathsinv0.
  use (colimOfArrowsIn _ _ ccV cc _ _).
Qed.


Lemma forget_IMod_creates_colim_law
            {g : graph}{d : diagram g IMOD}
      (dV := (mapdiagram forget_IModules d))
      (cc : ColimCocone dV) 
      (c := colim cc)
      (* true if the tensor is left cocontinuous *)
      (is_ccV : preserves_colimits_of_shape (φ₂ tensor I) g)
       : IModule_laws (forget_IMod_creates_colim_data cc is_ccV).
Proof.
  set (ccV := make_ColimCocone _ _ _ (is_ccV _ _ _ (isColimCocone_from_ColimCocone cc))).

  split.
  - cbn.
    apply pathsinv0.
    apply colim_endo_is_identity.
    intro u.
    rewrite assoc.
    etrans.
    {
      apply cancel_postcomposition.
      apply skewmonoidal_unitr_ax.
    }
    etrans.
    {
      rewrite assoc'.
      apply cancel_precomposition.
      apply (colimOfArrowsIn _ _ ccV cc _ _).
    }
    cbn.
    rewrite assoc.
    etrans; [apply cancel_postcomposition,IModule_isRetract|].
    apply id_left.
  - cbn.

  set (ccV' := make_ColimCocone _ _ _ (is_ccV _ _ _ (isColimCocone_from_ColimCocone ccV))).

  apply (colimArrowUnique' ccV').
  (* goal: move the colimIn towards the end, in each hand side
   we start with the l.h.s *)
  intro u.
  etrans.
  {
    etrans;[apply assoc|].
    etrans.
    {
      apply cancel_postcomposition.
      etrans.
      {
        etrans;[apply assoc|].
        apply cancel_postcomposition.
        apply skewmonoidal_assoc_ax.
      }
      rewrite assoc'.
      apply cancel_precomposition.
      rewrite (functor_id tensor).
      eapply (binprod_functor_swap_morphisms tensor).
      
    }
    rewrite assoc'.
    apply cancel_precomposition.
    rewrite assoc'.
    apply cancel_precomposition.
    apply (colimOfArrowsIn _ _ ccV cc).
  }
  (* Now the r.h.s *)
  apply pathsinv0.
  etrans.
  {
    etrans.
    {
      rewrite assoc.
      apply cancel_postcomposition.
      apply binprod_change_mor; [| apply idpath].
      apply (colimOfArrowsIn _ _ ccV cc).
    }
    rewrite assoc'.
    apply cancel_precomposition.
    apply (colimOfArrowsIn _ _ ccV cc).
  }
  repeat rewrite assoc.
  apply cancel_postcomposition.
  apply pathsinv0, IModule_law2.
Qed.


Definition forget_IMod_creates_colim_IModule
            {g : graph}{d : diagram g IMOD}
      (dV := (mapdiagram forget_IModules d))
      (cc : ColimCocone dV) 
      (c := colim cc)
      (* true if the tensor is left cocontinuous *)
      (is_ccV : preserves_colimits_of_shape (φ₂ tensor I) g)
  : IModule :=
   _ ,, forget_IMod_creates_colim_law cc is_ccV.

Definition forget_IMod_creates_colim_cocone
            {g : graph}{d : diagram g IMOD}
      (dV := (mapdiagram forget_IModules d))
      (cc : ColimCocone dV) 
      (c := colim cc)
      (* true if the tensor is left cocontinuous *)
      (is_ccV : preserves_colimits_of_shape (φ₂ tensor I) g)
      : cocone d (forget_IMod_creates_colim_IModule cc is_ccV).
Proof.
  use make_cocone.
  - intro v.
    eapply tpair.
    apply forget_IMod_creates_colimIn_IMod_Mor_laws.
  - intros u v e.
    apply IModule_Mor_equiv.
    apply (colimInCommutes cc).
Defined.

Lemma forget_IMod_creates_colim_colimArrow_laws
            {g : graph}{d : diagram g IMOD}
      (dV := (mapdiagram forget_IModules d))
      (cc : ColimCocone dV) 
      (c := colim cc)
      (* true if the tensor is left cocontinuous *)
      (is_ccV : preserves_colimits_of_shape (φ₂ tensor I) g)
    {M : IModule} (ccM : cocone d M) :
  IModule_Mor_laws (forget_IMod_creates_colim_IModule cc is_ccV) M
                   (colimArrow cc M (mapcocone forget_IModules _ ccM)).
Proof.
  set (ccV := make_ColimCocone _ _ _ (is_ccV _ _ _ (isColimCocone_from_ColimCocone cc))).
  etrans.
  apply (precompWithColimOfArrows _ _ ccV).
  apply pathsinv0.
  apply (colimArrowUnique ccV).
  intro u.
  rewrite assoc.
  etrans.
  {
    apply cancel_postcomposition.
    assert (H := (colimArrowCommutes ccV M)).
    cbn in H.
    unfold functor_fix_snd_arg_mor in H.
    cbn in H.
    unfold make_dirprod in H.
    cbn in H.
    etrans ;[apply pathsinv0, (functor_comp (φ₂ tensor I))|].
    apply maponpaths.
    apply (colimArrowCommutes cc).
  }
  apply pathsinv0.
  apply IModule_Mor_action.
Qed.

Definition forget_IMod_creates_colim_isColimCocone
            {g : graph}{d : diagram g IMOD}
      (dV := (mapdiagram forget_IModules d))
      (cc : ColimCocone dV) 
      (c := colim cc)
      (* true if the tensor is left cocontinuous *)
      (is_ccV : preserves_colimits_of_shape (φ₂ tensor I) g)
      : isColimCocone d _ (forget_IMod_creates_colim_cocone cc is_ccV).
Proof.
  red.
  intros M ccM.
  use unique_exists.
  - eapply tpair.
     apply (forget_IMod_creates_colim_colimArrow_laws _ _ ccM).
  - intro v.
    apply IModule_Mor_equiv.
    apply (colimArrowCommutes _ _ (mapcocone forget_IModules d ccM) _).
  - intro f.
    cbn.
    apply impred_isaprop.
    intro t.
    apply has_homsets_IModule.
  - cbn.
    intros f eq.
    apply IModule_Mor_equiv.
    apply path_to_ctr.
    intro v.
    apply (invmap IModule_Mor_equiv (eq v)).
Defined.

Definition forget_IMod_creates_colim
            {g : graph}{d : diagram g IMOD}
      (dV := (mapdiagram forget_IModules d))
      (cc : ColimCocone dV) 
      (c := colim cc)
      (* true if the tensor is left cocontinuous *)
      (is_ccV : preserves_colimits_of_shape (φ₂ tensor I) g)
  : ColimCocone d := make_ColimCocone d _ _
                                       (forget_IMod_creates_colim_isColimCocone cc is_ccV).


Definition forget_IMod_creates_colim_action_eq
            {g : graph}{d : diagram g IMOD}
      (dV := (mapdiagram forget_IModules d))
      (cc : ColimCocone dV) 
      (c := colim cc)
      (* true if the tensor is left cocontinuous *)
      (is_ccV : preserves_colimits_of_shape (φ₂ tensor I) g)
      (u : vertex g)
  : (colimIn cc u ) #⊗ identity I · forget_IMod_creates_colim_action_data cc is_ccV =
    σ (dob d u : IModule) ·
      (colimIn (forget_IMod_creates_colim cc is_ccV) u : IModule_Mor _ _).
Proof.
  set (ccV := make_ColimCocone _ _ _ (is_ccV _ _ _ (isColimCocone_from_ColimCocone cc))).
  apply (colimOfArrowsIn _ _ ccV cc).
Qed.


(* I is a I-module *)
Definition IModule_I_data : IModule_data :=
  make_IModule_data (I : V) (λ' I ).

Lemma IModule_I_laws : IModule_laws IModule_I_data.
Proof.
  split.
  - exact (skewmonoidal_rho_lambda_eq _).
  - apply I_mult_laws.
Qed.

Definition IModule_I : IModule :=
  IModule_I_data ,, IModule_I_laws.

(* The tensor product of I-modules is a I-module (actually, we only need
 that the right object is a module) *)
Definition IModule_tensor_data (A : V) (B : IModule_data) : IModule_data :=
  make_IModule_data (A ⊗ B) ((α' A B I ·  (identity A #⊗ σ B))  ).
   
(* We only use the action of B *)
Lemma IMod_tensor_isRetract (A : V)(B : IModule)
   : ρ' (A ⊗ B) · (α' A B I ·  (identity A #⊗ σ B)) = identity (A ⊗ B).
Proof.
    rewrite assoc.
    etrans.
    {
      apply cancel_postcomposition.
      apply skewmonoidal_rho_alpha_eq.
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
    + apply IModule_isRetract.
Qed.

Lemma IModule_tensor_laws (A : V) (B : IModule) : IModule_laws (IModule_tensor_data A B).
Proof.
  split.
  - apply (IMod_tensor_isRetract A B).
  - cbn.
    etrans.
    {
      etrans; [apply assoc |].
      apply cancel_postcomposition.
      etrans; [apply pathsinv0,assoc |].
      apply cancel_precomposition.
      rewrite <- (functor_id tensor).
      apply (skewmonoidal_assoc_ax).
    }
    etrans.
    {
      apply cancel_postcomposition.
      (etrans; [apply assoc |]).
      apply cancel_postcomposition.
      apply skewmonoidal_pentagon_eq.
    }
    cbn.
    repeat (etrans; [apply pathsinv0,assoc |]).
    etrans.
    {
      apply cancel_precomposition.
      apply cancel_precomposition.
      etrans.
      {
        apply cancel_precomposition.
        apply pathsinv0.
        apply (functor_comp (φ₁ tensor A)).
      }
      etrans.
      {
        apply pathsinv0.
        apply (functor_comp (φ₁ tensor A)).
      }
      etrans.
      {
        eapply (maponpaths (# (φ₁ tensor A) )).
        rewrite assoc.
        apply (IModule_law2 B).
      }
      apply (functor_comp (φ₁ tensor A)).
    }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans.
    {
      etrans; [apply pathsinv0, assoc |].
      apply cancel_precomposition.
      apply pathsinv0.
      apply skewmonoidal_assoc_ax.
    }
    cbn.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    repeat fold I.
    apply pathsinv0.
    cbn.
    apply (functor_comp (φ₂ tensor I)).
Qed.

Definition IModule_tensor (A : V) (B : IModule) : IModule :=
  _ ,, IModule_tensor_laws A B.


Notation IM := IModule_I.

Infix "⊗M" := IModule_tensor (at level 31).

Lemma IModule_tensor_Mor_laws {A B} {C D : IModule}
      (f : V ⟦ A, B⟧)(g : IModule_Mor C D) :
  IModule_Mor_laws (A ⊗M C) (B ⊗M D) (f #⊗ g).
Proof.
  red.
  cbn.
  rewrite <- assoc.
  etrans.
  {
    apply cancel_precomposition.
    etrans;[apply pathsinv0,functor_comp|].
    eapply (maponpaths (# tensor) (t2 := (f · identity _ #, _))).
    apply dirprod_paths.
    + cbn.
      rewrite id_right , id_left.
      reflexivity.
    + cbn.
      eapply IModule_Mor_action.
  }
  apply pathsinv0.
  etrans.
  {
    rewrite assoc.
    apply cancel_postcomposition.
    apply skewmonoidal_assoc_ax.
  }
  apply pathsinv0.
  etrans;[|apply assoc].
  apply cancel_precomposition.
  apply pathsinv0.
  exact (! (functor_comp tensor _ _)).
Qed.

Definition IModule_tensor_Mor {A B}{ C D : IModule}
           (f : V ⟦ A, B⟧)(g : IModule_Mor C D) :
  IModule_Mor (IModule_tensor A C) (IModule_tensor B D)
  := _ ,, IModule_tensor_Mor_laws f g.

Infix "#⊗M" := IModule_tensor_Mor (at level 31).

(* first step of definition *)
Definition IModule_tensor_functor_data :
   functor_data (V ⊠ IMOD) IMOD.
Proof.
  set (onobs := fun alg : (V ⊠ IMOD )  => IModule_tensor
                                            (pr1 alg : V)(pr2 alg : IModule)).
  apply (make_functor_data (C' := IMOD)  onobs).
  intros alg1 alg2 m.
  simpl in m.
  exact (IModule_tensor_Mor (pr1 m) (pr2 m)).
Defined.
Lemma IModule_tensor_is_functor :
  is_functor IModule_tensor_functor_data.
Proof.
  split.
  - intro alg.
    apply (IModule_Mor_equiv ).
    apply (functor_id tensor).
  - intros a b c f g.
    apply (IModule_Mor_equiv ).
    etrans;[| use (functor_comp tensor)].
    apply idpath.
Qed.

Definition IModule_tensor_functor : functor (V ⊠ IMOD)IMOD :=
  make_functor (IModule_tensor_functor_data ) (IModule_tensor_is_functor ).

Definition action_as_IModule_Mor (X : IModule) : IModule_Mor (X ⊗M IM) X :=
  (σ X,, IModule_law2 X).


(* left unitor for IModules *)

Lemma IModule_unitl_laws (x : IModule) :
   IModule_Mor_laws (IModule_tensor I x) x (λ' x).
Proof.
  red; cbn.
  etrans.
  {
    rewrite <- assoc.
    apply cancel_precomposition.
    apply skewmonoidal_unitl_ax.
  }
  etrans;[apply assoc|].
  apply cancel_postcomposition.
  unfold functor_fix_snd_arg_ob.
  apply skewmonoidal_alpha_lambda_eq.
Qed.

Definition IModule_unitl x : IModule_Mor (IModule_tensor I x) x :=
  (λ' x ,, IModule_unitl_laws x).

Notation λM := IModule_unitl.


(* the category of IModules do not have right unitor for the ususal tensor *)


(* associator *)
Lemma IModule_assoc_laws x y z :
  IModule_Mor_laws ( (x ⊗ y) ⊗M z) (x ⊗M (y ⊗M z))
                   (α' x y z).
Proof.
  red; cbn.
  etrans; revgoals.
  {
    etrans; revgoals.
    {
      apply cancel_precomposition.
      apply cancel_precomposition.
      apply (pathscomp0 (b := (identity x #⊗ α' _ _ _)
                                · (identity x #⊗ (identity y #⊗ σ z)))); revgoals.
      {
        etrans.
        {
          apply pathsinv0.
          apply functor_comp.
        }
        apply (maponpaths (fun z => z #⊗ _)).
        apply id_left.
      }
      apply idpath.
    }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    apply  (skewmonoidal_pentagon_eq V x y z I).
  }
  repeat rewrite <- assoc.
  apply cancel_precomposition.
  etrans;[| apply skewmonoidal_assoc_ax].
  (* etrans;[| apply (nat_trans_ax α' _ _ ((identity x #, identity y) #, σ z))]. *)
  apply cancel_postcomposition.
  apply (maponpaths (# tensor)).
  apply dirprod_paths.
  + apply pathsinv0, (functor_id tensor (x , y)).
  + apply idpath.
Qed.
Definition IModule_assoc x y z : IModule_Mor ( (x ⊗ y) ⊗M z)
                                                  (x ⊗M (y ⊗M z)) :=
  (α' x y z) ,, IModule_assoc_laws x y z.

Notation αM := IModule_assoc.



(** Any monoid morphism induces a source-module structure on the target, and I is
the initial monoid *)
Lemma IModule_laws_from_monoid (X : skewMonoid V)
  :
  IModule_laws (make_IModule_data (X : V) (identity X #⊗ η X · μ X)).
Proof.
  split.
  - etrans;[apply assoc|].
    apply skewMonoid_unitr.
  - cbn.
    etrans; revgoals.
    {
      rewrite assoc.
      apply cancel_postcomposition.
      apply pathsinv0.
      etrans.
      {
        apply (binprod_functor_swap_morphisms tensor).
      }
      apply cancel_precomposition.
      use (functor_comp (φ₂ tensor _)).
    }
    etrans; revgoals.
    {
      repeat rewrite <- assoc.
      apply cancel_precomposition.
      apply cancel_precomposition.
      apply pathsinv0, skewMonoid_pentagon.
    }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans; revgoals.
    {
      apply cancel_postcomposition.
      etrans;[|apply assoc].
      apply cancel_precomposition.
      apply pathsinv0.
      use skewmonoidal_assoc_ax.
    }
    etrans; revgoals.
    {
      etrans;[|apply assoc].
      apply cancel_precomposition.
      etrans;[|apply assoc].
      apply cancel_precomposition.
      cbn.
      etrans; revgoals.
      {
        apply (functor_comp (φ₁ tensor X)).
      }
      eapply (maponpaths (# (φ₁ tensor X))).
      apply pathsinv0.
      apply skewMonoid_unitl.
    }
    etrans; revgoals.
    {
      rewrite assoc.
      apply cancel_postcomposition.
      apply pathsinv0.
      rewrite <- (functor_id tensor).
      apply skewmonoidal_assoc_ax.
    }

    repeat rewrite <- assoc.
    apply cancel_precomposition.
    cbn.
    etrans; [|apply  (functor_comp tensor (_ #, _)(_ #, _))].
    etrans; [apply pathsinv0, (functor_comp tensor (_ #, _)(_ #, _))|].
    cbn.
    apply maponpaths.
    apply maponpaths.
    apply pathsinv0.
    apply skewmonoidal_unitl_ax.
Qed.




Definition IModule_from_monoid (X : skewMonoid V)
  : IModule  := _ ,, IModule_laws_from_monoid X.



(** unit of a monoid is a module morphism *)
Lemma unit_IModule_Mor_laws 
      (X : skewMonoid V) : IModule_Mor_laws   IModule_I
                                             (IModule_from_monoid X) (η X).
Proof.
  cbn.
  apply pathsinv0.
  etrans.
  {
    etrans;[apply assoc|].
    apply cancel_postcomposition.
    apply binprod_functor_swap_morphisms.
  }
  etrans;[|apply  skewmonoidal_unitl_ax].
  rewrite <- assoc.
  apply cancel_precomposition.
  apply skewMonoid_unitl.
Qed.

Definition unit_IModule_Mor
      (X : skewMonoid V) : IModule_Mor   IModule_I
                                         (IModule_from_monoid X)  :=
  η X ,, unit_IModule_Mor_laws X.
  



(** * The quotiented tensor on IModules



 *)



(* We suppose that the category has coequalizers, and that the left tensor preserves them *)
Context (coeqsV : Coequalizers V)
        (tensorl_coeqs : preserves_colimits_of_shape (φ₂ tensor I) Coequalizer_graph).
Definition IModule_Coequalizers : Coequalizers IMOD.
Proof.
  intros M M' u v.
  apply forget_IMod_creates_colim.
  - specialize (coeqsV _ _ (# forget_IModules u)(# forget_IModules v)).
    eapply (eq_diag_liftcolimcocone (C := make_category V hsV) ); revgoals.
    + apply coeqsV.
    + apply sym_eq_diag.
      apply (mapdiagram_coequalizer_eq_diag (D := make_category _ hsV)).
  - apply tensorl_coeqs.
Defined.

Definition IModule_tensor' (X : IModule_data)(Y : IModule) : IModule :=
  CoequalizerObject
    _ (IModule_Coequalizers _ _ ((αM X I Y : IMOD ⟦ _, _ ⟧) · identity X #⊗M λM Y)
                      (σ X #⊗M identity (C := IMOD) Y)).

Arguments IModule_tensor' : simpl never.
Infix "⊗M'" := IModule_tensor' (at level 31).



Definition IModule_tensor'_proj (X : IModule_data)(Y : IModule)
  : IModule_Mor (X ⊗M Y) (X ⊗M' Y) :=
  CoequalizerArrow 
    _ (IModule_Coequalizers _ _ ((αM X I Y : IMOD ⟦ _, _ ⟧) · identity X #⊗M λM Y)
                      (σ X #⊗M identity (C := IMOD) Y)).

Arguments IModule_tensor'_proj : simpl never.
Notation κ := IModule_tensor'_proj.



Definition IModule_tensor'_Out_V
           {X : IModule_data}{Y : IModule}{Z : V}
           (f : X ⊗ Y --> Z)
  (eqf : α' X I Y · identity X #⊗ λ' Y · f = σ X #⊗ identity Y · f)
  : X ⊗M' Y --> Z
      := CoequalizerOut _ _ _ _ eqf.

Arguments IModule_tensor'_Out_V : simpl never.

Lemma IModule_tensor'_Out_VM_eq_aux 
           {X : IModule_data}{Y : IModule}{Z : IModule}
           (f : IModule_Mor (X ⊗M Y) Z)
  (eqf : α' X I Y · identity X #⊗ λ' Y · f = σ X #⊗ identity Y · f)
  : IModule_tensor'_Out_V f eqf =
    (CoequalizerOut IMOD _ _ _
                   (IModule_Mor_equiv (f := (αM X I Y : IMOD ⟦ _, _ ⟧) · identity X #⊗M λM Y · f)
                                      (g := (σ X #⊗M identity (C := IMOD) Y : IMOD ⟦_,_⟧) · f)
                                      eqf ) : IModule_Mor _ _).
Proof.
  set (ccM := IModule_Coequalizers _ _ _ _).
  set (f' := CoequalizerOut _ _ _ _ _ ).
  apply pathsinv0.
  apply CoequalizerOutUnique.
  assert (h' : (CoequalizerArrow IMOD ccM : IMOD ⟦_, _⟧) · f' = f) by eapply CoequalizerArrowComm.
  apply (invmap IModule_Mor_equiv ) in h'.
  apply h'.
Qed.

Lemma IModule_tensor'_Out_V_laws
           {X : IModule_data}{Y : IModule}{Z : IModule}
           (f : IModule_Mor (X ⊗M Y) Z)
  (eqf : α' X I Y · identity X #⊗ λ' Y · f = σ X #⊗ identity Y · f)
  : IModule_Mor_laws (X ⊗M' Y) Z (IModule_tensor'_Out_V f eqf).
Proof.
  rewrite IModule_tensor'_Out_VM_eq_aux.
  apply pr2.
Qed.

Definition IModule_tensor'_Out_M
           {X : IModule_data}{Y : IModule}{Z : IModule}
           (f : IModule_Mor (X ⊗M Y) Z)
  (eqf : α' X I Y · identity X #⊗ λ' Y · f = σ X #⊗ identity Y · f)
  : IModule_Mor (X ⊗M' Y) Z := _ ,, IModule_tensor'_Out_V_laws f eqf.

Lemma IModule_tensor'_Out_eq
           {X : IModule_data}{Y : IModule}{Z : V}
           (f :  (X ⊗M Y) --> Z)
  (eqf : α' X I Y · identity X #⊗ λ' Y · f = σ X #⊗ identity Y · f)
  : κ X Y · IModule_tensor'_Out_V f eqf = f.
Proof.
  apply CoequalizerArrowComm.
Qed.




Lemma IModule_tensor'_action_eq  X :
  κ X IM #⊗ identity I · σ (X ⊗M' IM) =
  α' X I I · identity X #⊗ λ' I · κ X IM.
Proof.
  unfold IModule_tensor'.
  cbn.
  set (cc := eq_diag_liftcolimcocone _ _ _).
  eapply  (forget_IMod_creates_colim_action_eq
             (g := Coequalizer_graph)
             cc
             _ Two).
Qed.

(** the action is the inverse of the right unit, when using this tensor *)
Lemma IModule_tensor'_action_inv (X : IModule_data) :
  σ X · ρ' X · κ X IM = κ X IM.
Proof.
  rewrite skewmonoidal_unitr_ax.
  rewrite assoc'.
  etrans.
  {
    apply cancel_precomposition.
    apply pathsinv0, CoequalizerArrowEq.
  }
  etrans.
  {
    etrans;[apply assoc|].
    apply cancel_postcomposition.
    etrans;[apply assoc|].
    etrans;[apply cancel_postcomposition, skewmonoidal_rho_alpha_eq|].
    cbn.
    rewrite <- (functor_comp tensor).
    apply maponpaths.
    cbn.
    apply map_on_two_paths.
    - apply id_left.
    - apply skewmonoidal_rho_lambda_eq.
  }
  etrans;[|apply id_left].
  apply cancel_postcomposition.
  apply (functor_id tensor).
  Qed.
         


Lemma IModule_tensor'_on_mor_law1
      {X Y : IModule_data}{X' Y' : IModule}
      (f : V ⟦X, Y⟧)
      (f' : IModule_Mor X' Y') :
  α' X I X' · identity X #⊗ λ' X' · f #⊗ f' =
  (f #⊗ identity I) #⊗ f' · (α' Y I Y' · identity Y #⊗ λ' Y').
Proof.
  etrans.
  {
    rewrite assoc'.
    apply cancel_precomposition.
    apply binprod_change_mor.
    - etrans;[apply id_left|].
      apply pathsinv0, id_right.
    - apply pathsinv0, skewmonoidal_unitl_ax.
  }
  repeat rewrite assoc.
  apply cancel_postcomposition.
  apply pathsinv0,  skewmonoidal_assoc_ax.
Qed.


Lemma IModule_tensor'_on_mor_law2
      {X Y : IModule_data}{X' Y' : IModule}
      (f : IModule_Mor X Y)
      (f' : IModule_Mor X' Y') :
  σ X #⊗ identity X' · f #⊗ f' = (f #⊗ identity I) #⊗ f' · σ Y #⊗ identity Y'.
Proof.
  do 2 rewrite <- functor_comp.
  apply maponpaths.
  cbn.
  apply map_on_two_paths.
  - apply IModule_Mor_action.
  - rewrite id_left,id_right.
    apply idpath.
Qed.


Definition IModule_tensor'_on_mor
           {X Y : IModule_data}{X' Y' : IModule}
           (f : IModule_Mor X Y)
           (f' : IModule_Mor X' Y') :
  IModule_Mor (X ⊗M' X') (Y ⊗M' Y').
Proof.
  unshelve eapply (CoequalizerOfArrows IMOD).
  - exact ((f #⊗ identity I) #⊗M f').
  - exact (f #⊗M f').
  - apply IModule_Mor_equiv.
    apply IModule_tensor'_on_mor_law1.
  - apply IModule_Mor_equiv.
    apply IModule_tensor'_on_mor_law2.
Defined.

Arguments IModule_tensor'_on_mor : simpl never.

Infix "#⊗M'" := IModule_tensor'_on_mor (at level 31).

Lemma IModule_tensor'_id
      (X : IModule)(X' : IModule) :
  (IModule_identity X #⊗M' IModule_identity X' : V ⟦_, _⟧) = identity (C := V) _.
Proof.
  assert (h : (IModule_identity X #⊗M' IModule_identity X' : IMOD ⟦_,_⟧) = identity (C := IMOD) _).
  {
     apply pathsinv0, CoequalizerOutUnique.
     etrans;[apply id_right|].
     apply pathsinv0.
     etrans;[|apply id_left].
     apply cancel_postcomposition.
     apply IModule_Mor_equiv.
     apply (functor_id tensor (X, X')).
  }
  exact (invmap IModule_Mor_equiv h).
Qed.


Lemma IModule_tensor'_ax {X Y : IModule_data}{X' Y' : IModule}
      (f : IModule_Mor X Y)(f' : IModule_Mor X'  Y')
  : f #⊗M f'  · κ Y Y' = κ X X' · f #⊗M' f'.
  (* : (f #⊗M f' : IMOD ⟦ _, _ ⟧) · κ Y Y' = (κ X X' : IMOD ⟦ _, _⟧ ) · f #⊗M' f'. *)
Proof.
  assert (h : (f #⊗M f' : IMOD ⟦ _, _ ⟧) · κ Y Y' = (κ X X' : IMOD ⟦ _, _⟧ ) · f #⊗M' f').
  {
    apply pathsinv0.
    apply CoequalizerOfArrowsEq.
  }
  apply IModule_Mor_equiv in h.
  exact h.
Qed.

Lemma IModule_unitr'_law (X : IModule) :
  IModule_Mor_laws X (X ⊗M' IM)
                   (ρ' X · κ X IM).
Proof.
  etrans.
  {
    rewrite assoc.
    apply IModule_tensor'_action_inv.
  }
  apply pathsinv0.
  etrans.
  {
    etrans.
    {
      apply cancel_postcomposition.

      rewrite <- (id_left (identity _)).
      exact (functor_comp tensor (ρ' X #, identity I)(κ X IM #, identity I)).
    }
    etrans.
    {
      rewrite assoc'.
      apply cancel_precomposition.
      apply IModule_tensor'_action_eq.
      
    }
    do 2 rewrite assoc.
    apply cancel_postcomposition.
    apply skewmonoidal_triangle_eq.
    
  }
  apply id_left.
Qed.

Definition IModule_unitr' (X : IModule) :
  IModule_Mor X (X ⊗M' IM) := _ ,, IModule_unitr'_law X.

Notation ρM' := IModule_unitr'.

Lemma IModule_unitr'_ax {x y : IModule} (f : IModule_Mor x y) :
  f · ρM' y = ρM' x · f #⊗M' identity (C := IMOD) IM.
Proof.
  cbn.
  rewrite assoc.
  rewrite skewmonoidal_unitr_ax.
  do 2 rewrite assoc'.
  apply cancel_precomposition.
  apply  (IModule_tensor'_ax _ (identity (C := IMOD) IM)).
Qed.

Definition im_action' (X : IModule) : IModule_Mor (X ⊗M' IM) X :=
   IModule_tensor'_Out_M (action_as_IModule_Mor X) (IModule_law2 X).

Notation σ' := im_action'.

(* the action is the invers of the right unit *)
Lemma IModule_unitr'_action' X :
  ρM' X · σ' X = identity X.
Proof.
  etrans;[apply assoc'|].
  etrans.
  {
    apply cancel_precomposition.
    apply (IModule_tensor'_Out_eq (Y := IM)).
  }
  apply IModule_isRetract.
Qed.


Definition IModule_unitl' (X : IModule) :
  IModule_Mor (IM ⊗M' X) X
:= (IModule_tensor'_Out_M (X := IM) (λM X)(I_mult_laws _ X)).

Notation λM' := IModule_unitl'.

(* unfortunately, λM' IM is not definitionally equal to σ' IM *)

Definition V_IModules_assoc (X : V)(Y Z : IModule) : X ⊗ Y ⊗ Z --> X ⊗ (Y ⊗M' Z)
  := α' X Y Z · identity X #⊗ κ Y Z.

Local Notation αVM := V_IModules_assoc.

Lemma V_IModules_assoc_ax 
           {x x' : V}{ y y' z z' : IModule } (f : x --> x')(g : IModule_Mor y y')(h : IModule_Mor z z') :
  ((f #⊗ g) #⊗ h) · αVM x' y' z' = αVM x y z · (f #⊗ (g #⊗M' h)).
Proof.
  etrans.
  {
    etrans;[apply assoc|].
    rewrite skewmonoidal_assoc_ax.
    rewrite assoc'.
    rewrite <- (functor_comp tensor).
    cbn.
    apply cancel_precomposition.
    eapply (map_on_two_paths (fun a b => a #⊗ b)).
    - rewrite id_right.
      apply pathsinv0, id_left.
    - apply (IModule_tensor'_ax g h ).
  }
  etrans;[|apply assoc].
  apply cancel_precomposition.
  etrans; [|apply (functor_comp tensor)].
  apply idpath.
Qed.

Lemma V_IModules_assoc_postcomp {Y : IModule}{Z : IModule}{ W} (f : Y ⊗ Z --> W) X 
  (eqf : α' Y I Z · identity Y #⊗ λ' Z · f = σ Y #⊗ identity Z · f) :
  α' X Y Z · identity X #⊗ f = αVM X Y Z ·
                                   identity X #⊗ IModule_tensor'_Out_V (X := Y)(Y := Z) f eqf.
Proof.
  apply pathsinv0.
  etrans;[apply assoc'|].
  apply cancel_precomposition.
  etrans; [apply pathsinv0,(functor_comp (φ₁ tensor X))|].
  apply (maponpaths (# (φ₁ tensor X))).
  apply IModule_tensor'_Out_eq.
Qed.

Lemma V_IModules_assoc_mult X (Y : IModule) :
  α' X Y I · identity X #⊗ σ Y = αVM X Y IM · identity X #⊗ σ' Y.
Proof.
  unshelve eapply (@V_IModules_assoc_postcomp Y IM _ _ X).
Qed.

Definition alphaVM_lambda_eq a b :
   αVM I a b · λ' (a ⊗M' b) = λM a #⊗ identity _ · κ a b.
Proof.
  etrans;[apply assoc'|].
  etrans;[apply cancel_precomposition, skewmonoidal_unitl_ax|].
  etrans;[apply assoc|].
  apply cancel_postcomposition.
  apply skewmonoidal_alpha_lambda_eq.
Qed.

Lemma make_IModule'_eq_aux {X} (s : X ⊗ I --> X)
  (eq2 : αVM X IM IM · identity X #⊗ λM' IM · s = s #⊗ identity I · s) :
  α' X I I · identity X #⊗ λ' I · s = s #⊗ identity I · s.
Proof.
  etrans;[| exact eq2].
  apply cancel_postcomposition.
  apply (@V_IModules_assoc_postcomp IM IM).
Qed.

Definition make_IModule' {X} (s : X ⊗ I --> X)
      (eq1 : ρ' X · s  = identity _)
      (eq2 : αVM X IM IM · (identity _) #⊗ (λM' IM) · s  =
            s #⊗ identity I · s ) : IModule :=
   make_IModule_data X s ,, eq1 ,, make_IModule'_eq_aux s eq2.

Lemma make_IModule_Mor'_eq_aux {X}{Y : IModule} {Z : IModule_data} (f : X ⊗M Y --> Z)
           (eqf :   αVM X Y IM · identity X #⊗ σ' Y · f = f #⊗ identity I · σ Z) :
  α' X Y I · identity X #⊗ σ Y · f = f #⊗ identity I · σ Z.
Proof.
  etrans;[ |exact eqf].
  apply cancel_postcomposition.
  apply (@V_IModules_assoc_mult).
Qed.

Definition make_IModule_Mor' {X}{Y : IModule} {Z : IModule_data} (f : X ⊗M Y --> Z)
           (eqf :   αVM X Y IM · identity X #⊗ σ' Y · f = f #⊗ identity I · σ Z)
           : IModule_Mor (X ⊗M Y) Z :=
  f ,,  make_IModule_Mor'_eq_aux f eqf.


Definition PtIModule := coslicecat_ob IMOD IM.

Coercion IModule_from_PtIModule (x : PtIModule)(* (x : precategory_PtIModule) *) : IModule :=
   pr1 x.


Definition im_unit (X : PtIModule) : IModule_Mor (IM : IModule) X := pr2 X.
Notation ε := im_unit.

Definition PtIModule_I : PtIModule := IM ,, identity (C := IMOD) IM.

Notation IP := PtIModule_I.

Definition PtIModule_tensor (X Y : PtIModule) : PtIModule :=
  (X ⊗M' Y) ,, (ρM' IM : IMOD ⟦ _ , _ ⟧) · ε X #⊗M' ε Y.


Infix "⊠M" := PtIModule_tensor (at level 31).


Definition PtIModule_Mor (X Y : PtIModule) := coslicecat_mor _ _ X Y.
Coercion IModule_Mor_from_PtIModule_Mor {X Y } (f : PtIModule_Mor X Y) : IModule_Mor X Y
                                                                                := pr1 f.

Definition PtIModule_Mor_commutes {X Y}(f : PtIModule_Mor X Y) :
  ε X · f = ε Y :=  invmap IModule_Mor_equiv (pr2 f).

Definition make_PtIModule_Mor {X Y : PtIModule} (f : IModule_Mor X Y)
           (eq : ε X · f = ε Y) : PtIModule_Mor X Y :=
   (f,, IModule_Mor_equiv (f := (ε X : IMOD ⟦ _, _ ⟧) · f) eq).

Definition IModule_tensor'_Out_M_unit
           {X : PtIModule}{Y : PtIModule}{Z : PtIModule}
           (f : IModule_Mor (X ⊗M Y) Z)
  (eqf : α' X I Y · identity X #⊗ λ' Y · f = σ X #⊗ identity Y · f)
  (eqf_unit : ρ' I · ε X #⊗ ε Y · f = ε Z)
  : ε (X ⊠M Y) · IModule_tensor'_Out_M f eqf = ε Z.
Proof.
  cbn -[IModule_Coequalizers ].
  etrans.
  {
    apply cancel_postcomposition.
    rewrite assoc'.
    apply cancel_precomposition.
    apply pathsinv0.
    apply (IModule_tensor'_ax (ε X)(ε Y)).
  }
  etrans.
  {
    rewrite assoc'.
    apply cancel_precomposition.
    rewrite assoc'.
    apply cancel_precomposition.
    apply IModule_tensor'_Out_eq.
  }
  rewrite assoc.
  exact eqf_unit.
Qed.

Definition IModule_tensor'_Out_PtM
           {X : PtIModule}{Y : PtIModule}{Z : PtIModule}
           (f : IModule_Mor (X ⊗M Y) Z)
  (eqf : α' X I Y · identity X #⊗ λ' Y · f = σ X #⊗ identity Y · f)
  (eqf_unit : ρ' I · ε X #⊗ ε Y · f = ε Z)
  : PtIModule_Mor (X ⊠M Y) Z :=
  make_PtIModule_Mor _ (IModule_tensor'_Out_M_unit f eqf eqf_unit).


Definition PtIModule_unitr (X : PtIModule) :
  PtIModule_Mor X (X ⊠M IP) :=
  make_PtIModule_Mor (Y := X ⊠M IP) (ρM' X) (IModule_unitr'_ax _).

(* TODO: decomposer ca *)
Lemma IModule_unitl'_unit (X : PtIModule) :
  ε (IP ⊠M X) · λM' X = ε X.
Proof.
  cbn.
  etrans.
  {
    apply cancel_postcomposition.
    etrans;[apply assoc'|].
    apply cancel_precomposition.
    apply pathsinv0.
    apply (IModule_tensor'_ax (identity (C := IMOD) IM) (ε X)).
  }
  etrans.
  {
    etrans;[apply assoc'|].
    apply cancel_precomposition.
    etrans;[apply assoc'|].
    apply cancel_precomposition.
    apply IModule_tensor'_Out_eq.
  }
  etrans.
  {
    apply cancel_precomposition.
    apply skewmonoidal_unitl_ax.
  }
  etrans;[apply assoc|].
  etrans;[|apply id_left].
  apply cancel_postcomposition.
  apply skewmonoidal_rho_lambda_eq.
Qed.

Definition PtIModule_unitl (X : PtIModule) :
  PtIModule_Mor (IP ⊠M X) X :=
   make_PtIModule_Mor (X := IP ⊠M X) (λM' X)(IModule_unitl'_unit X).

Lemma IModule_action'_unit (X : PtIModule) :
  ε (X ⊠M IP) · σ' X = ε X.
Proof.
  cbn -[ρM' σ'].
  etrans; [apply cancel_postcomposition, pathsinv0, (IModule_unitr'_ax (x := IM) )|].
  etrans; [apply assoc'|].
  etrans;[|apply id_right].
  apply cancel_precomposition.
  apply IModule_unitr'_action'.
Qed.

Definition PtIModule_action (X : PtIModule) :
  PtIModule_Mor (X ⊠M IP) X :=
   make_PtIModule_Mor (X := X ⊠M IP) (σ' X)(IModule_action'_unit X).



Definition PtIModule_unit_Mor (X : PtIModule) : PtIModule_Mor PtIModule_I X
                                                              := ε X ,, id_left _.


Definition precategory_PtIModule := coslice_precat precategory_IModule IM (has_homsets_IModule _).

Definition forget_PtIModules_IModules : functor precategory_PtIModule precategory_IModule
  := coslicecat_to_cat (C := precategory_IModule) IM (has_homsets_IModule IM).

Definition forget_PtIModules : functor precategory_PtIModule V :=
  forget_PtIModules_IModules ∙ forget_IModules.




Definition PtIModule_from_monoid (X : skewMonoid V) : PtIModule :=
  IModule_from_monoid X ,, unit_IModule_Mor X.

Lemma pt_imodule_eq_tr
      (Q : V -> Type)
      (m : forall (x : PtIModule), Q x )
      (x : V)
      {f1 f2} 
      (eqf : f1 = f2)
      (e1 : IModule_laws (make_IModule_data x f1))
      (e2 : IModule_laws (make_IModule_data x f2))
      (x1 := (make_IModule_data x f1 ,, e1 : IModule))
      (x2 := (make_IModule_data x f2 ,, e2 : IModule))
      (u1 u2 : I --> x)
      (* pas forcement necessaire *)
      (equ : u1 = u2)
  (hu1 : IModule_Mor_laws IP x1 u1)
  (hu2 : IModule_Mor_laws IP x2 u2)
      (um1 := u1 ,, hu1 : IModule_Mor IM x1)
      (um2 := u2 ,, hu2 : IModule_Mor IM x2)
      (xp1 := x1 ,, um1 : PtIModule)
      (xp2 := x2 ,, um2 : PtIModule)
  :
    m xp1 = m xp2.
Proof.
  cbv.
  induction eqf.
  induction equ.
  assert (eqe : e1  = e2).
  {
    apply proofirrelevance.
    apply isaprop_IModule_laws.
  }
  induction eqe.
  assert(heq : hu1 = hu2).
  apply (proofirrelevance _ (isaprop_IModule_Mor_laws IP x1 u1)).
  induction heq.
  apply paths_refl.
Qed.
Corollary pt_imodule_eq (x : V)
      {f1 f2} 
      (eqf : f1 = f2)
      (e1 : IModule_laws (make_IModule_data x f1))
      (e2 : IModule_laws (make_IModule_data x f2))
      (x1 := (make_IModule_data x f1 ,, e1 : IModule))
      (x2 := (make_IModule_data x f2 ,, e2 : IModule))
      (u1 u2 : I --> x)
      (* pas forcement necessaire *)
      (equ : u1 = u2)
  (hu1 : IModule_Mor_laws IP x1 u1)
  (hu2 : IModule_Mor_laws IP x2 u2)
      (um1 := u1 ,, hu1 : IModule_Mor IM x1)
      (um2 := u2 ,, hu2 : IModule_Mor IM x2)
      (xp1 := x1 ,, um1 : PtIModule)
      (xp2 := x2 ,, um2 : PtIModule)

  :
    xp1 = xp2.
Proof.
apply (pt_imodule_eq_tr (fun _ => PtIModule) (fun x => x)).
apply eqf.
apply equ.
Qed.
End IModule_Definition.
Arguments PtIModule_Mor {_}{_} _ _.
