(**
  Definition of the category of pointed I-modules

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
          X ⊗ λ
X ⊗ I ⊗ I ----> X ⊗ I
   |              |
   |              | 
x⊗I|              | x
   |              |
   V              V
 X ⊗ I ---------> X 
          x

>>>

In the skew monoidal setting, not all objects are modules over I.

That 
The square law is not necessary because the multiplication for I is an
isomorphism

  Based on the definitions of the category of algebras of an endofunctor

skew monoids induce IModules (quick explanation: any monoid morphism induce
a functor between categories of modules, and I is the initial monoid).
**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import SkewMonoidalCategories.
Require Import SkewMonoids.
Require Import Complements.

Local Open Scope cat.

(* (* Definition of a retract *) *)
(* Definition retract {C : precategory}{x y : C}(f : C ⟦ x , y ⟧) : UU := *)
(*   ∑ (g : C ⟦ y , x ⟧), f · g = identity _. *)

(* Coercion morphism_from_rectract {C : precategory}{x y : C}{f : C ⟦ x , y ⟧}(r : retract f) : C ⟦ y , x ⟧ := *)
(*   pr1 r. *)

(* Definition retract_isRetract {C : precategory}{x y : C}{f : C ⟦ x , y ⟧} *)
(*            (r : retract f) : f · r = identity _ := pr2 r. *)

(** ** Category of algebras of an endofunctor *)

Section IModule_Definition.

Delimit Scope morphism_scope with m.
Delimit Scope object_scope with o.
Open Scope object_scope.

Context (V : skewmonoidal_precat).
Context (hsV : has_homsets V).

Notation I := (skewmonoidal_precat_unit V).
Notation tensor := (skewmonoidal_precat_tensor V).

Notation "X ⊗ Y" := (tensor (X , Y)) : object_scope.

(* The following notation does not work, for an unknown reason (you may use it,
but coq won't use it for display).

  Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).
  Check  (fun a b c d (f : V ⟦a , b ⟧)(g : V ⟦ c , d ⟧) => idpath (f #⊗ g)).

 Coq then displays
λ (a b c d : V) (f : V ⟦ a, b ⟧) (g : V ⟦ c, d ⟧), idpath (# tensor (f #, g))
     : ∏ (a b c d : V) (f : V ⟦ a, b ⟧) (g : V ⟦ c, d ⟧), # tensor (f #, g) = # tensor (f #, g)

instead of f #⊗ g = f #⊗ g

Our trick then consists in defining tensor_on_mor, defining a notation for it, and
a tactic or a lemma to rewrite according to its definition
 *)
Let tensor_on_mor {a b c d}(f : V ⟦a , b ⟧)(g : V ⟦ c , d ⟧) : V ⟦ a ⊗ c , b ⊗ d ⟧ := # tensor (f #, g).
Infix "#⊗" := (tensor_on_mor) (at level 31).


Notation α' := (skewmonoidal_precat_associator V).
Notation λ' := (skewmonoidal_precat_left_unitor V).
Notation ρ' := (skewmonoidal_precat_right_unitor V).


Definition IModule_data : UU
  := ∑ F , F ⊗ I --> F × I --> F.

Coercion ob_from_IModule_data (F : IModule_data)
  : V := pr1 F.

Definition im_action  (F : IModule_data) : F⊗ I --> F := pr1 (pr2 F).
Definition im_unit (F : IModule_data) : I --> F := pr2 (pr2 F).

Local Notation σ := im_action.
Local Notation ϵ := im_unit.

Definition IModule_laws  (T : IModule_data) : UU :=
      ( ρ' T · σ T  = identity _)
        × ( α' (((T : V) ,, I) ,, I) · (identity _) #⊗ ((λ' I) ) · σ T  =
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
          α' (((T : V) ,, I) ,, I) · (identity T) #⊗ ((λ' I) ) · σ T  =
            σ T #⊗ identity I · σ T 
   :=
  pr2 (pr2 T).


Local Notation η := (sm_unit _).
Local Notation μ := (sm_mult _).

Local Notation φ₁ := (functor_fix_fst_arg _ _ _).
Local Notation φ₂ := (functor_fix_snd_arg _ _ _).


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
Definition IModule_Mor_laws  (X Y : IModule_data ) (f : X --> Y)
  : UU 
  := ϵ X · f = ϵ Y × σ X · f =  (f #⊗ identity _) · σ Y.

Lemma isaprop_IModule_Mor_laws  
  (T T' : IModule_data ) (α : T --> T')
  : isaprop (IModule_Mor_laws T T' α).
Proof.
   apply isapropdirprod; apply hsV.
Qed.

Definition IModule_Mor  (T T' : IModule_data ) : UU
  := ∑ α : T --> T', IModule_Mor_laws T T' α.

Coercion mor_from_IModule_Mor (X Y : IModule_data) (f : IModule_Mor X Y) : X --> Y := pr1 f.

Definition IModule_Mor_unit (X Y : IModule_data) (f : IModule_Mor X Y)
  : ϵ X · f = ϵ Y := pr1 (pr2 f).

Definition IModule_Mor_action (X Y : IModule_data) (f : IModule_Mor X Y)
  : σ X · f =  (f #⊗ identity _) · σ Y
                                           := pr2 (pr2 f).


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
  split.
  - apply id_right.
  - etrans;[apply id_right|].
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
  rewrite IModule_Mor_unit.
  rewrite IModule_Mor_action.
  repeat rewrite <- assoc.
  rewrite IModule_Mor_unit.
  split.
  - apply idpath.
  - etrans.
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

The category of I-modules is skew monoidal


*)

(* I is a I-module *)
Definition IModule_I_data : IModule_data :=
  ((I : V) ,, make_dirprod (λ' I)(identity I) ).

Lemma IModule_I_laws : IModule_laws IModule_I_data.
Proof.
  split.
  - exact (skewmonoidal_precat_rho_lambda_eq _).
  - apply I_mult_laws.
Qed.

Definition IModule_I : IModule :=
  IModule_I_data ,, IModule_I_laws.

(* The tensor product of I-modules is a I-module (actually, we only need
 that the left object is pointed *)
Definition IModule_tensor_data (A : IModule_data) (B : IModule_data) : IModule_data :=
  (A ⊗ B ,, ((α' ((A, B), I) ·  (identity A #⊗ σ B)) ,, ρ' I · (ϵ A #⊗ ϵ B))).
   
(* On utilise que l'action de B *)
Lemma IMod_tensor_isRetract (A : IModule_data)(B : IModule)
   : ρ' (A ⊗ B) · (α' ((A, B), I) ·  (identity A #⊗ σ B)) = identity (A ⊗ B).
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
    + apply IModule_isRetract.
Qed.

Lemma IModule_tensor_laws (A : IModule_data) (B : IModule) : IModule_laws (IModule_tensor_data A B).
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
      apply (nat_trans_ax α' _ _ ((identity A #, identity B) #, _)).
    }
    etrans.
    {
      apply cancel_postcomposition.
      (etrans; [apply assoc |]).
      apply cancel_postcomposition.
      apply skewmonoidal_precat_pentagon_eq.
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
      apply (nat_trans_ax α' _ _ ((_ #, _) #, _)).
    }
    cbn.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    repeat fold I.
    apply pathsinv0.
    cbn.
    apply (functor_comp (φ₂ tensor I)).
Qed.

Definition IModule_tensor (A : IModule_data) (B : IModule) : IModule :=
  _ ,, IModule_tensor_laws A B.



Lemma IModule_tensor_Mor_laws {A B C D : IModule}
      (f : IModule_Mor A B)(g : IModule_Mor C D) :
  IModule_Mor_laws (IModule_tensor A C) (IModule_tensor B D)
                                                                       (f #⊗ g).
Proof.
  split.
  cbn.
  - rewrite <- assoc.
    apply cancel_precomposition.
    etrans;[apply pathsinv0,functor_comp|].
    apply (maponpaths (#tensor)).
    apply dirprod_paths; apply IModule_Mor_unit.
  - cbn.
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
      apply (nat_trans_ax α' _ _ ((f #, g) #, identity _)).
    }
    apply pathsinv0.
    etrans;[|apply assoc].
    apply cancel_precomposition.
    apply pathsinv0.
    exact (! (functor_comp tensor _ _)).
Qed.

Definition IModule_tensor_Mor {A B C D : IModule}
           (f : IModule_Mor A B)(g : IModule_Mor C D) :
  IModule_Mor (IModule_tensor A C) (IModule_tensor B D)
  := _ ,, IModule_tensor_Mor_laws f g.

(* first step of definition *)
Definition IModule_tensor_functor_data :
   functor_data (IMOD ⊠ IMOD) IMOD.
Proof.
  set (onobs := fun alg : (IMOD ⊠ IMOD )  => IModule_tensor
                                            (pr1 alg : IModule)(pr2 alg : IModule)).
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

Definition IModule_tensor_functor : functor (IMOD⊠ IMOD)IMOD :=
  make_functor (IModule_tensor_functor_data ) (IModule_tensor_is_functor ).

Notation tensorM := IModule_tensor_functor.
Notation IM := (IModule_I : IMOD).
Notation "X ⊗ Y" := (tensorM ((X : IMOD), (Y : IMOD)))  : module_scope.
Notation "f #⊗ g" := (# (tensorM) (f #, g)) : module_scope.
Delimit Scope module_scope with M.

(* left unitor for IModules *)

Lemma IModule_left_unitor_isIModule_Mor (x : IModule) :
   IModule_Mor_laws (IModule_tensor IModule_I x) x ( λ' x).
Proof.
  red; cbn; split.
  - etrans.
    {
      rewrite <- assoc.
      apply cancel_precomposition.
      apply (nat_trans_ax λ').
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
      apply (nat_trans_ax λ').
    }
    etrans;[apply assoc|].
    apply cancel_postcomposition.
    unfold functor_fix_snd_arg_ob.
    apply skewmonoidal_precat_alpha_lambda_eq.
Qed.

Definition IModule_left_unitor_data x : IModule_Mor (IModule_tensor (IModule_I) x) x :=
  (λ' x ,, IModule_left_unitor_isIModule_Mor x).

Lemma IModule_left_unitor_is_nat_trans :
  is_nat_trans (I_pretensor tensorM (IModule_I : IMOD)) (functor_identity IMOD) IModule_left_unitor_data.
Proof.
  intros x y f.
  apply IModule_Mor_equiv.
  apply (nat_trans_ax λ').
Qed.

Definition IModule_left_unitor : left_unitor tensorM IM := make_nat_trans _ _ _ IModule_left_unitor_is_nat_trans.

(* the category of IModules do not have right unitor for IModules *)


(* associator *)
Lemma IModule_associator_isIModule_Mor x y z :
  IModule_Mor_laws (IModule_tensor (IModule_tensor x y) z) (IModule_tensor x (IModule_tensor y z)) (α' ((x, y), z)).
Proof.
  red; cbn; split.
  - rewrite <- assoc.
    eapply (pathscomp0 (b := _ · ((ρ' I #⊗ identity _) · (((ϵ x #⊗ ϵ y) #⊗ (ϵ z)) ·
                                            α' ((_ , _),_))))).
    {
      apply cancel_precomposition.
      rewrite assoc.
      apply cancel_postcomposition.
      etrans;[| apply functor_comp].
      apply (maponpaths (fun z => _ #⊗ z)).
      apply pathsinv0, id_left.
    }
    etrans.
    {
      apply cancel_precomposition.
      apply cancel_precomposition.
      apply (nat_trans_ax α' _ _ (( ϵ x #, ϵ y) #, ϵ z) ).
    }
    apply pathsinv0.
    eapply (pathscomp0 (b := _ · ((identity _ #⊗ ρ' I ) · ((ϵ x #⊗ (ϵ y #⊗ ϵ z))
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
    etrans;[| apply cancel_precomposition, (skewmonoidal_precat_rho_alpha_eq V)].
    repeat rewrite assoc.
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (nat_trans_ax ρ').
  - etrans; revgoals.
    {
      etrans; revgoals.
      {
        apply cancel_precomposition.
        apply cancel_precomposition.
        apply (pathscomp0 (b := (identity x #⊗ α' ((_ , _) , _))
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
      apply  (skewmonoidal_precat_pentagon_eq V x y z I).
    }
    repeat rewrite <- assoc.
    apply cancel_precomposition.
    etrans;[| apply (nat_trans_ax α' _ _ ((identity x #, identity y) #, σ z))].
    apply cancel_postcomposition.
    apply (maponpaths (# tensor)).
    apply dirprod_paths.
    + apply pathsinv0, (functor_id tensor (x , y)).
    + apply idpath.
Qed.
Definition IModule_associator_data x y z : IModule_Mor (IModule_tensor (IModule_tensor x y) z)
                                                  (IModule_tensor x (IModule_tensor y z)) :=
  (α' ((x , y) , z)) ,, IModule_associator_isIModule_Mor x y z.

Lemma IModule_associator_is_nat_trans : is_nat_trans (assoc_left tensorM) (assoc_right tensorM)
                                                     (fun x => IModule_associator_data
                                                              (pr1 (pr1 x) : IModule ) (pr2 (pr1 x)) (pr2 x)).
Proof.
  intros x y f.
  apply IModule_Mor_equiv.
  apply (nat_trans_ax α' _ _ ((_ #, _) #, _)).
Qed.

Definition IModule_associator : associator tensorM := make_nat_trans _ _ _ IModule_associator_is_nat_trans.


(** Any monoid morphism induces a source-module structure on the target, and I is
the initial monoid *)
Lemma IModule_laws_from_monoid (X : skewMonoid V)
  :
  IModule_laws ((X : V) ,, (identity X #⊗ η X · μ X ,, η X)).
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
      use (nat_trans_ax α' _ _ ((_ #, _) #, _)).
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
      apply (nat_trans_ax α' _ _ ((_ #, _) #, _)).
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
    apply (nat_trans_ax λ' ).
Qed.




Definition IModule_from_monoid (X : skewMonoid V)
  : IModule  := _ ,, IModule_laws_from_monoid X.


(** unit of a monoid is a module morphism *)
Lemma unit_IModule_Mor_laws 
      (X : skewMonoid V) : IModule_Mor_laws   IModule_I
                                             (IModule_from_monoid X) (η X).
Proof.
  split.
  - apply id_left.
  - cbn.
    apply pathsinv0.
    etrans.
    {
      etrans;[apply assoc|].
      apply cancel_postcomposition.
      apply binprod_functor_swap_morphisms.
    }
    etrans;[|apply  (nat_trans_ax λ' )].
    rewrite <- assoc.
    apply cancel_precomposition.
    apply skewMonoid_unitl.
Qed.

Definition unit_IModule_Mor
      (X : skewMonoid V) : IModule_Mor   IModule_I
                                         (IModule_from_monoid X)  :=
  η X ,, unit_IModule_Mor_laws X.
  


End IModule_Definition.
