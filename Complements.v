(**
Some useful lemmas, and axiomatization of Theorem 4.7 of "List object with
algebraic structure" (Fiore-Saville, extended version)
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


(* Require Import UniMath.Foundations.NaturalNumbers. *)

Local Open Scope cat.

(** Binary product of categories *)
Local Notation "C ⊠ D" := (precategory_binproduct C D) (at level 38).
Local Notation "( c , d )" := (make_precatbinprod c d).
Local Notation "( f #, g )" := (precatbinprodmor f g).

Local Infix "×" := pair_functor  : functor_scope .
Local Notation carrier := (alg_carrier _ ).

Delimit Scope functor_scope with F.

(** Theorem 4.7 of "List object with algebraic structure" (extended version)
as an axiom
 *)
Section Theorem47.

  Context {D C B A : precategory}
          (hsC : has_homsets C)(OC : Initial C)(chC : Colims_of_shape nat_graph C)
          (hsA : has_homsets A)(chA : Colims_of_shape nat_graph A)
          {J : C ⟶ A}(OJ : isInitial _ (J (InitialObject OC)))
          (omegaJ : is_omega_cocont J)
          {F : D ⊠ C ⟶ C}
          (omegaF : ∏ d , is_omega_cocont (functor_fix_fst_arg _ _ _ F d))
          {G : B ⊠ A ⟶ A}
          (omegaG : ∏ b , is_omega_cocont (functor_fix_fst_arg _ _ _ G b))
          {K : D ⟶ B} (h : F ∙ J ⟹ (K × J)%F ∙ G).

  Let OA : Initial A := make_Initial _ OJ.
  (* (alg_map _ (InitialObject (colimAlgInitial hsV O (Fromega Z) (Vch (initChain O _))))) *)

  Context {a : A}{d : D}(α : A ⟦ G (K d , a) , a ⟧).

  Let iniChd := (initChain OC (functor_fix_fst_arg D C C F d)).

(*   Definition cocone_a : cocone (mapdiagram J iniChd) a. *)
(*   Proof. *)
(* use make_cocone. *)
(* - intro n. *)
(*   cbn. *)
(* - abstract (intros m n e; destruct e ; *)
(*             apply (coconeInCommutes (colimCocone CC) (S m) _ (idpath _))). *)
(* Defined. *)
  Proof.

  Let μFd := (InitialObject (colimAlgInitial hsC OC (omegaF d) (chC iniChd))).

  (* Definition Thm47_mor : A ⟦ J (carrier μFd) , a ⟧. *)

  (*   red in omegaJ. *)
  (*   unfold preserves_colimit in omegaJ. *)
  (*   set (chI := (chC (initChain OC (functor_fix_fst_arg D C C F d)))). *)
  (*   specialize (omegaJ _ _ _ (pr2 chI)). *)
  (*   (initChain OC _) *)
  (*     ColimCocone *)
  (*   apply  *)

  Lemma Thm47 : ∃! (β : A ⟦ J (carrier μFd) , a ⟧), 
                h (d , carrier μFd) · # G ( identity _ #, β ) · α  =
                # J (alg_map _ μFd) · β.
  Admitted.

  Definition Thm47_mor : A ⟦ J (carrier μFd) , a ⟧ := pr1 (pr1 Thm47).

  Definition Thm47_commutes
    : h (d , carrier μFd) · # G ( identity _ #, Thm47_mor ) · α  =
      # J (alg_map _ μFd) · Thm47_mor
        := pr2 (pr1 Thm47).

  Lemma Thm47_unique
        {β}
        (eq : h (d , carrier μFd) · # G (identity _ #, β) · α  = # J (alg_map _ μFd) · β)
    : β = Thm47_mor.
  Proof.
    apply path_to_ctr.
    exact eq.
  Qed.

  Lemma Thm47_eq 
        {β} (eq : h (d , carrier μFd) · # G ( identity _ #, β ) · α  = # J (alg_map _ μFd) · β)
        {β'} (eq' : h (d , carrier μFd) · # G ( identity _ #, β' ) · α  = # J (alg_map _ μFd) · β')
        : β = β'.
  Proof.
    eapply pathscomp0;[exact (Thm47_unique eq)|].
    apply pathsinv0, (Thm47_unique eq').
  Qed.

End Theorem47.


Local Infix ",," := bindelta_pair_functor  : functor_scope .

(* TODO upload in UniMath *)
Lemma BinCoproductOfIdentities
           {C : precategory}   {a b : C}
           (ccab : BinCoproduct C a b) :
  identity ccab = BinCoproductOfArrows _ ccab ccab (identity a) (identity b).
Proof.
  apply BinCoproduct_endo_is_identity.
  - etrans;[apply BinCoproductOfArrowsIn1|apply id_left].
  - etrans;[apply BinCoproductOfArrowsIn2|apply id_left].
Qed.
           
(* A version of BinCoproductOfArrows with given bincoproducts
TODO: upload in Unimath
 *)
Definition BinCoproductOfArrows_comp'
           {C : precategory}   {a b c d x y : C}
           (ccab : BinCoproduct C a b)(cccd : BinCoproduct C c d)
           (ccxy : BinCoproduct C x y)
           (f : C ⟦ a, c ⟧) (f' : C ⟦ b, d ⟧)
(g : C ⟦ c, x ⟧) (g' : C ⟦ d, y ⟧) 
  : BinCoproductOfArrows _ ccab cccd f f' ·
    BinCoproductOfArrows _ _ _ g g'
    =
    BinCoproductOfArrows _ _ ccxy (f · g) (f' · g').
Proof.
  apply BinCoproductArrowUnique.
  - rewrite assoc.
    rewrite BinCoproductOfArrowsIn1.
    rewrite <- assoc.
    rewrite BinCoproductOfArrowsIn1.
    apply assoc.
  - rewrite assoc.
    rewrite BinCoproductOfArrowsIn2.
    rewrite <- assoc.
    rewrite BinCoproductOfArrowsIn2.
    apply assoc.
Qed.

Lemma binprod_functor_combine_morphisms {C D E : precategory} (F : C ⊠ D ⟶ E)
      {c c'} (f : C ⟦ c , c' ⟧)
      {d d'} (g : D ⟦ d , d' ⟧)
  : # F (f #, identity _) · # F (identity _ #, g) = # F (f #, g).
Proof.
  etrans; [apply pathsinv0, functor_comp|].
  apply maponpaths.
  apply dirprod_paths;[apply id_right|apply id_left].
Qed.

Lemma binprod_functor_combine_morphisms_reverse {C D E : precategory} (F : C ⊠ D ⟶ E)
      {c c'} (f : C ⟦ c , c' ⟧)
      {d d'} (g : D ⟦ d , d' ⟧)
  : # F (identity _ #, g) · # F (f #, identity _)  = # F (f #, g).
Proof.
  etrans; [apply pathsinv0, functor_comp|].
  apply maponpaths.
  apply dirprod_paths;[apply id_left|apply id_right].
Qed.

Lemma binprod_functor_swap_morphisms {C D E : precategory} (F : C ⊠ D ⟶ E)
      {c c'} (f : C ⟦ c , c' ⟧)
      {d d'} (g : D ⟦ d , d' ⟧)
  : # F (f #, identity _) · # F (identity _ #, g) = 
    # F (identity _ #, g) · # F (f #, identity _)  .
Proof.
  etrans;[apply binprod_functor_combine_morphisms|].
  apply pathsinv0, binprod_functor_combine_morphisms_reverse.
Qed.



(** All diagrams over the empty graphs are equal *)
Lemma eq_diag_empty_graph  {D : category} (d d' : diagram initial.empty_graph D) :
  eq_diag (C := D) d d'.
Proof.
  use tpair; use empty_rect.
Defined.

(** ** A pair of functors (F,G) : A  -> C * D is omega cocontinuous if F and G are *)
Section delta_pairfunctors.
(* TODO: upload this to UniMath (omegacocontfunctors)

This is adapted from the section pair_functor
 *)
Context {A C D : precategory} (F : functor A C) (G : functor A D)
        (hsA : has_homsets A)  (hsC : has_homsets C) (hsD : has_homsets D).
Lemma isColimCocone_delta_pair_functor {gr : graph}
  (HF : ∏ (d : diagram gr A) (c : A) (cc : cocone d c) (h : isColimCocone d c cc),
        isColimCocone _ _ (mapcocone F d cc))
  (HG : ∏ (d : diagram gr A) (c : A) (cc : cocone d c) (h : isColimCocone d c cc),
        isColimCocone _ _ (mapcocone G d cc)) :
  ∏ (d : diagram gr A) (cd : A ) (cc : cocone d cd),
  isColimCocone _ _ cc ->
  isColimCocone _ _ (mapcocone (bindelta_pair_functor F G) d cc).
Proof.
intros cAB ml ccml Hccml xy ccxy.
transparent assert (cFAX : (cocone (mapdiagram F cAB) (pr1 xy))).
{ use make_cocone.
  - intro n; apply (pr1 (pr1 ccxy n)).
  - abstract (intros m n e; apply (maponpaths dirprod_pr1 (pr2 ccxy m n e))).
}
transparent assert (cGBY : (cocone (mapdiagram G cAB) (pr2 xy))).
{ use make_cocone.
  - intro n; apply (pr2 (pr1 ccxy n)).
  - abstract (intros m n e; apply (maponpaths dirprod_pr2 (pr2 ccxy m n e))).
}
destruct (HF _ _ _ Hccml _ cFAX) as [[f hf1] hf2].
destruct (HG _ _ _ Hccml _ cGBY) as [[g hg1] hg2].
simpl in *.
use tpair.
- apply (tpair _ (f,,g)).
  abstract (intro n; unfold precatbinprodmor, compose; simpl;
             rewrite hf1;rewrite hg1; apply idpath).
- abstract (intro t; apply subtypePath; simpl;
             [ intro x; apply impred; intro; apply isaset_dirprod; [ apply hsC | apply hsD ]
             | induction t as [[f1 f2] p]; simpl in *; apply pathsdirprod;
               [ apply (maponpaths pr1 (hf2 (f1,, (λ n, maponpaths pr1 (p n)))))
               | apply (maponpaths pr1 (hg2 (f2,, (λ n, maponpaths dirprod_pr2 (p n)))))]]).
Defined.

Lemma is_cocont_delta_pair_functor (HF : is_cocont F) (HG : is_cocont G) :
  is_cocont (bindelta_pair_functor F G).
Proof.
intros gr cAB ml ccml Hccml.
now apply isColimCocone_delta_pair_functor; [apply HF|apply HG|].
Defined.

Lemma is_omega_cocont_delta_pair_functor (HF : is_omega_cocont F) (HG : is_omega_cocont G) :
  is_omega_cocont (bindelta_pair_functor F G).
Proof.
now intros cAB ml ccml Hccml; apply isColimCocone_delta_pair_functor.
Defined.

End delta_pairfunctors.

Definition functor_fix_fst_arg'  (C D E : precategory) (F : C ⊠ D ⟶ E) (c : C) : D ⟶ E :=
  ((constant_functor _ _ c ,, functor_identity _ )%F ∙ F).
Definition functor_fix_snd_arg'  (C D E : precategory) (F : C ⊠ D ⟶ E) (d : D) : C ⟶ E :=
  ((functor_identity _  ,, constant_functor _ _ d  )%F ∙ F).

Section FunctorFixCocont.
  Context {C D E : precategory}
          (hsD : has_homsets D)
          (hsC : has_homsets C)
          (hsE : has_homsets E)
         {F :  C ⊠ D ⟶ E}(omegaF : is_omega_cocont F).

Lemma is_omega_cocont_fix_fst_arg' c : is_omega_cocont (functor_fix_fst_arg' _ _ _ F c).
Proof.
  apply is_omega_cocont_functor_composite.
  - exact hsE.
  - apply is_omega_cocont_delta_pair_functor;[exact hsC | exact hsD |  |].
    + apply is_omega_cocont_constant_functor.
      exact hsC.
    + apply is_omega_cocont_functor_identity.
      exact hsD.
  - exact omegaF.
Qed.

Definition is_omega_cocont_fix_fst_arg c : is_omega_cocont (functor_fix_fst_arg _ _ _ F c) :=
  is_omega_cocont_fix_fst_arg' c.

Lemma is_omega_cocont_fix_snd_arg' c : is_omega_cocont (functor_fix_snd_arg' _ _ _ F c).
Proof.
  apply is_omega_cocont_functor_composite.
  - exact hsE.
  - apply is_omega_cocont_delta_pair_functor;[exact hsC | exact hsD |  |].
    + apply is_omega_cocont_functor_identity.
      exact hsC.
    + apply is_omega_cocont_constant_functor.
      exact hsD.
  - exact omegaF.
Qed.

Definition is_omega_cocont_fix_snd_arg c : is_omega_cocont (functor_fix_snd_arg _ _ _ F c) :=
  is_omega_cocont_fix_snd_arg' c.

End  FunctorFixCocont.


