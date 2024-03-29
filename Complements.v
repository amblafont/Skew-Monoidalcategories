(**
Some useful lemmas, and axiomatization of Theorem 4.7 of "List object with
algebraic structure" (Fiore-Saville, extended version): [Thm47]
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
Require Import UniMath.CategoryTheory.limits.graphs.bincoproducts.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.graphs.eqdiag.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.coslicecat.


Local Open Scope cat.

(** Binary product of categories *)
Local Notation "C ⊠ D" := (category_binproduct C D) (at level 38).
Local Notation "( c , d )" := (make_catbinprod c d).
Local Notation "( f #, g )" := (catbinprodmor f g).

Local Infix "×" := pair_functor  : functor_scope .
Local Notation carrier := (alg_carrier _ ).

Delimit Scope functor_scope with F.

(** Theorem 4.7 of "List object with algebraic structure" (extended version)
as an axiom
 *)
Section Theorem47.

  Context {D C B A : category}
          (hsC := homset_property C)(OC : Initial C)(chC : Colims_of_shape nat_graph C)
          (hsA := homset_property A)(chA : Colims_of_shape nat_graph A)
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


  Let μFd := (InitialObject (colimAlgInitial OC (omegaF d) (chC iniChd))).


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

(** The rest of this file consists of useful lemmas that should be uploaded
 to UniMath at some point. *)

Local Infix ",," := bindelta_pair_functor  : functor_scope .

(** id + id = id *)
Lemma BinCoproductOfIdentities
           {C : category}   {a b : C}
           (ccab : BinCoproduct a b) :
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
           {C : category}   {a b c d x y : C}
           (ccab : BinCoproduct a b)(cccd : BinCoproduct c d)
           (ccxy : BinCoproduct x y)
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


Lemma binprod_functor_combine_morphisms {C D E : category} (F : C ⊠ D ⟶ E)
      {c c'} (f : C ⟦ c , c' ⟧)
      {d d'} (g : D ⟦ d , d' ⟧)
  : # F (f #, identity _) · # F (identity _ #, g) = # F (f #, g).
Proof.
  etrans; [apply pathsinv0, functor_comp|].
  apply maponpaths.
  apply dirprod_paths;[apply id_right|apply id_left].
Qed.

Lemma binprod_functor_combine_morphisms_reverse {C D E : category}
      (F : C ⊠ D ⟶ E)
      {c c'} (f : C ⟦ c , c' ⟧)
      {d d'} (g : D ⟦ d , d' ⟧)
  : # F (identity _ #, g) · # F (f #, identity _)  = # F (f #, g).
Proof.
  etrans; [apply pathsinv0, functor_comp|].
  apply maponpaths.
  apply dirprod_paths;[apply id_left|apply id_right].
Qed.

Lemma binprod_functor_swap_morphisms {C D E : category} (F : C ⊠ D ⟶ E)
      {c c'} (f : C ⟦ c , c' ⟧)
      {d d'} (g : D ⟦ d , d' ⟧)
  : # F (f #, identity _) · # F (identity _ #, g) = 
    # F (identity _ #, g) · # F (f #, identity _)  .
Proof.
  etrans;[apply binprod_functor_combine_morphisms|].
  apply pathsinv0, binprod_functor_combine_morphisms_reverse.
Qed.



(** ** A pair of functors (F,G) : A  -> C * D is omega cocontinuous if F and G are *)
Section delta_pairfunctors.
(* TODO: upload this to UniMath (omegacocontfunctors)

This is adapted from the section pair_functor
 *)
Context {A C D : category} (F : functor A C) (G : functor A D)
        (hsA := homset_property A)  (hsC := homset_property C) (hsD := homset_property D).
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
  (intro n; unfold catbinprodmor, compose; simpl;
  clear hf2 hg2;
   specialize (hf1 n);
   specialize (hg1 n);
   cbn in hf1, hg1;

  rewrite hf1, hg1; apply idpath).
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

Definition functor_fix_fst_arg'  (C D E : category) (F : C ⊠ D ⟶ E) (c : C) : D ⟶ E :=
  ((constant_functor _ _ c ,, functor_identity _ )%F ∙ F).
Definition functor_fix_snd_arg'  (C D E : category) (F : C ⊠ D ⟶ E) (d : D) : C ⟶ E :=
  ((functor_identity _  ,, constant_functor _ _ d  )%F ∙ F).

Section FunctorFixCocont.
  Context {C D E : category}
          (hsD := homset_property D)
          (hsC := homset_property C)
          (hsE := homset_property E)
         {F :  C ⊠ D ⟶ E}(omegaF : is_omega_cocont F).

Lemma is_omega_cocont_fix_fst_arg' c : is_omega_cocont (functor_fix_fst_arg' _ _ _ F c).
Proof.
  apply is_omega_cocont_functor_composite.
  - apply is_omega_cocont_delta_pair_functor.
    + apply is_omega_cocont_constant_functor.
    + apply is_omega_cocont_functor_identity.
  - exact omegaF.
Qed.

Definition is_omega_cocont_fix_fst_arg c : is_omega_cocont (functor_fix_fst_arg _ _ _ F c) :=
  is_omega_cocont_fix_fst_arg' c.

Lemma is_omega_cocont_fix_snd_arg' c : is_omega_cocont (functor_fix_snd_arg' _ _ _ F c).
Proof.
  apply is_omega_cocont_functor_composite.
  - apply is_omega_cocont_delta_pair_functor.
    + apply is_omega_cocont_functor_identity.
    + apply is_omega_cocont_constant_functor.
  - exact omegaF.
Qed.

Definition is_omega_cocont_fix_snd_arg c : is_omega_cocont (functor_fix_snd_arg _ _ _ F c) :=
  is_omega_cocont_fix_snd_arg' c.

End  FunctorFixCocont.


Lemma cocont_preserves_isBinCoproduct
      {C : category}
      {D : category}
      {F : functor C D}
      (cocontF : is_cocont F)
      {A B : C} (ccAB : BinCoproduct A B) :
  isBinCoproduct D (F A) (F B) (F ccAB)
                 (# F (BinCoproductIn1 ccAB))
                 (# F (BinCoproductIn2 ccAB)).
Proof.
  set (Io := pr2 ccAB).
  cbn in Io.
  red in cocontF.
  transparent assert (h : (BinCoproductCocone (F A) (F B))).
  {
    red.
    eapply (eq_diag_liftcolimcocone (C := D)).
    - unshelve apply mapdiagram_bincoproduct_eq_diag.
    - eapply make_ColimCocone.
      eapply cocontF.
      apply limits_isBinCoproductCocone_from_isBinCoproduct.
      + exact (isBinCoproduct_BinCoproduct _ ccAB).
  }
  apply limits_isBinCoproduct_from_isBinCoproductCocone.
  red.
  generalize (pr2 h).
  cbn.
  apply transportf.
  apply cocone_paths.
  use bool_rect; apply idpath.
Qed.



Lemma cocont_preserves_isInitial
      {C : category}
      {D : category}
      {F : functor C D}
      (cocontF : is_cocont F)
      {o : C}(Io : isInitial _ o) : isInitial D (F o).
Proof.
  transparent assert (h : (initial.Initial D)).
  {
    eapply (eq_diag_liftcolimcocone (C := D)).
    - eapply (graphs.initial.empty_graph_eq_diag ).
    - eapply make_ColimCocone.
      apply initial.equiv_isInitial1 in Io.
      eapply cocontF in Io.
      exact Io.
  }
  apply initial.equiv_isInitial2.
  exact (initial.isInitial_Initial h).
Qed.

(* TODO: upload in UniMath coslicecat *)
Section coslice_precat_theory.

Context {C : category}  (x : C)(sets : ∏ y, isaset (x --> y)).

Local Notation "X / C" := (coslice_precat C X sets).
(** The forgetful functor from C/x to C *)
Definition coslicecat_to_cat : (x / C) ⟶ C.
Proof.
  use make_functor.
  + use tpair.
    - apply pr1.
    - intros a b; apply pr1.
  + abstract ( split; [intro; apply idpath | red; intros; apply idpath] ).
Defined.

End coslice_precat_theory.


(* TODO: move to complememts, and use it more often
 for example for the swap stuff in Complements *)
Lemma binprod_change_mor {C D E : category }
      (F : C ⊠ D ⟶ E)
      {c1 c2 c2' c3 : C}
      (f : c1 --> c2)(g : c2 --> c3) 
      (f' : c1 --> c2')(g' : c2' --> c3)
      {d1 d2 d2' d3 : D}
      (u : d1 --> d2)(v : d2 --> d3) 
      (u' : d1 --> d2')(v' : d2' --> d3)
      (eqc : f · g = f' · g')
      (eqd : u · v = u' · v')
  :
    # F (f #, u) ·
    # F (g #, v)
    =
    # F (f' #, u') ·
    # F (g' #, v').
Proof.
  do 2 rewrite <- (functor_comp F (_ #, _)).
  cbn.
  rewrite eqc , eqd.
  apply idpath.
Qed.
