(** Summary of the formalization (kernel)

Tip: The Coq command [About ident] prints where the ident was defined
 *)

Require Import UniMath.Foundations.PartD.
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
Require Import UniMath.CategoryTheory.coslicecat.

Require Import UniMath.CategoryTheory.SkewMonoidal.SkewMonoidalCategories.
Require Import UniMath.CategoryTheory.SkewMonoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.

Require Import StructuralStrengths.
Require Import IModules.
Require Import Complements.
Require Import InitialAlgebraicMonoid.

Local Open Scope cat.

(** Notation for product of functors *)
Delimit Scope functor_scope with F.
Infix "××" := pair_functor (at level 31).

(* Notation for product category *)
Infix "×C" := precategory_binproduct (at level 38).
(** Notation for constructing objects and morphisms of a product category *)
Notation "( c , d )" := (make_catbinprod c d).
Notation "( f #, g )" := (catbinprodmor f g).



(**
The command:

Check (x ≡ y) 

succeeds if and only if [x] is convertible to [y]

*)
Notation  "x ≡ y :> A "  := (@paths_refl A x = @paths_refl A y) (at level 70, y at next level, no associativity).
Notation  "x ≡ y"  := (paths_refl x = paths_refl y) (at level 70, no associativity).

Fail Check (true ≡ false).
Check (true ≡ true).



Section Summary.


(** We suppose given a skew monoidal category V
 *)
Context (V : skewmonoidal_category).

(** Some notations for the monoidal structure *)
Notation tensor := (skewmonoidal_tensor (data_from_skewmonoidal V)).
Notation I := (skewmonoidal_I (data_from_skewmonoidal V)).
Notation α' := (skewmonoidal_assoc (data_from_skewmonoidal V)).
Notation λ' := (skewmonoidal_unitl (data_from_skewmonoidal V)).
Notation ρ' := (skewmonoidal_unitr (data_from_skewmonoidal V)).

(** We denote ⊗ the tensor product, and #⊗ the action on morphisms *)
Notation "X ⊗ Y" := (tensor (X , Y)).
Notation "f #⊗ g" :=
   (functor_on_morphisms (functor_data_from_functor _ _ tensor) (f #, g))
                         (at level 31).


(** * I-modules and pointed I-modules
covered by IModules.v 
 *)



(**
A I-module on V consists of an object F of V together
with a map F ⊗ I → F, subject to some laws given later.
There is an implicit coercion between I-modules and objects of V
 *)
Check ((IModule_data V) ≡ (∑ (F : V), F ⊗ I --> F : UU)).

(** Some notations for the action *)
Check (∏  F : IModule_data V, im_action V F ≡ (pr2 F : F ⊗ I --> F)).
Notation σ := (im_action V).

(** A I-module consists of the data previously defined subject to
  two laws *)
Check (IModule V ≡
         ∑ (F : IModule_data V) ,
         (** First law *)
         (ρ' F · σ F  = identity _)
           ×
           (** Second law *)
           (α' F I I · (identity _) #⊗ λ' I · σ F  =
            σ F #⊗ identity I · σ F)
      ).


(** A morphism between I-modules X and Y is a morphism between
underlying objects of V preserving the action
 *)
Check  (∏ (X Y : IModule V),
        IModule_Mor V X Y ≡
          ∑ (f :  V ⟦X, Y⟧) , 
            (** the morphism is compatible with σ *)
             σ X · f = (f #⊗ identity _) · σ Y).

          (* (** the unit is preserved *) *)
          (* (ϵ X · f = ϵ Y) *)

(** I-modules form a category  *)
Check (precategory_IModule V ≡
          (make_precategory_ob_mor (IModule V) (IModule_Mor V)
             ,, _) ,, _ ,, _).


(** The unit can be given the structure of a pointed I-module *)
Notation IM := (IModule_I V).
(** Checking the underlying V object. *)
Check ((IM : V) ≡ I).

(** The category of pointed I-modules is the coslice category of the category
of I-modules under I *)
Check (precategory_PtIModule V ≡
                             coslice_precat (precategory_IModule V ) IM
                             (has_homsets_IModule V IM)).

Notation PtIM_Cat := (category_PtIModule V).

Check (PtIModule V ≡ ob PtIM_Cat).

(* Notation for the point *)
Notation ϵ := (im_unit V).

(** IM is canonically a pointed I-module *)
Notation IP := (PtIModule_I V).
Check ((IP : IModule V) ≡ IM).
Check (ϵ IP ≡ identity (C := precategory_IModule V) IM).

(** The forgetful functor from pointed I-modules to V *)
Check (forget_PtIModules V : functor PtIM_Cat V).

(** We use the notation 𝒰 in the following when we want to make explicit the
coercion between pointed I-modules and objects of V. *)
Notation 𝒰 := (forget_PtIModules V).
Check (∏ (X : PtIModule V), 𝒰 X ≡ (X : V)).



(** There is a tensor product on pointed I-modules, defined as a coequalizer,
here called [PtIModule_tensor].
This requires that V has coequalizers (in fact, reflexive coequalizers are enough), and
the tensoring on the right with I preserves them.
 *)
Context (coeqsV : coequalizers.Coequalizers V).
Context  (tensorl_coeqs : preserves_colimits_of_shape
                            ((functor_fix_snd_arg _ _ _ tensor I)) coequalizers.Coequalizer_graph ).

Check (PtIModule_tensor V coeqsV tensorl_coeqs
       : PtIModule V → PtIModule V → PtIModule V).
Infix "⊠M" := (PtIModule_tensor V coeqsV tensorl_coeqs) (at level 31).

(** The underlying object of V of the tensor is the coequalizer of two morphisms
 from (X ⊗ I) ⊗ Y to X ⊗ Y
 *)
Check  (∏ (X Y : PtIModule V),
        𝒰 (X ⊠M Y) ≡
          CoequalizerObject
               V (coeqsV ((X ⊗ I) ⊗ Y) (X ⊗ Y)
                         (** Here is the first one *)
                         (α' X I Y · identity X #⊗ λ' Y)
                         (** Here is the second one *)
                         (σ X #⊗ identity Y)
            )).

(** Notation for the coequalizer arrow *)
Notation κ := (IModule_tensor'_proj V coeqsV tensorl_coeqs).
Check (fun (M N : PtIModule V) => κ M N : M ⊗ N --> M ⊠M N).


(** The tensor product can be lifted to the category of I-modules, there
 called [IModule_tensor] *)
(*
Check (IModule_tensor V : IModule V -> IModule V -> IModule V ).
Infix "⊗M" := (IModule_tensor V) (at level 31).

Lemma IModule_tensor_lifts_tensor (A B : IModule V) :
  𝒰 (A ⊗M B) = (𝒰 A) ⊗ (𝒰 B).
Proof.
  reflexivity.
Qed.
*)



(** * Structural strengths 
covered by StructuralStrengths.v

************* *)

(** We suppose given an endofunctor H on V *)
Context  (H : V ⟶ V).

(** A structural strength consists of a natural transformation between
the two relevant parallel functors from V × M (denoted by V ⊠ M below)
to V, subject to two laws.

There is an implicit coercion between strengths and natural
transformations.  *)
Check (strength coeqsV tensorl_coeqs H ≡
         ∑ (st : nat_trans (C := V ×C PtIM_Cat) (C' := V)
                   ((H ×× 𝒰) ∙ tensor)
                   ((functor_identity _ ×× 𝒰) ∙ tensor ∙ H)
           ),
         (** first law: triangle *)
         (∏ (a : V), ρ' (H a) · st (a, (IP : PtIM_Cat))  = # H (ρ' a))
         (** second law: pentagon *)
           ×
           (∏ (a : V),
            ∏ (x y : PtIModule V) ,
            α' (H a) x y · identity (H a) #⊗ κ x y · st (a , (x ⊠M y : PtIM_Cat))
            =
            (st (a, (x : PtIM_Cat)) #⊗ identity y)
              · st ((a ⊗ x), (y : PtIM_Cat))
              · # H (α' a x y · identity a #⊗ κ x y))).

(** * Skew H-monoids

.. for H a strong endofonctor on V

covered by StructuralStrengths.v

************* *)


(** Notations for the unit and multiplication of a (skew) monoid (see
    SkewMonoids.v for the precise definition) *)
Local Definition η (m : skewMonoid V) : V ⟦I , m⟧ := sm_unit V m.
Local Definition μ (m : skewMonoid V) : V ⟦m ⊗ m, m⟧ := sm_mult V m.

(** We suppose given a strength for the endofunctor H *)
Context (st : strength coeqsV tensorl_coeqs H).

(**
A H-monoid consists of a skew monoid with an H algebra structure,
subject to some laws.
There is an implicit coercion between H-monoids and skew monoids.
 *)
Check (@algMonoid_data V H ≡ ∑ X : skewMonoid V, H X --> X).

(** Notation for the algebra structure *)
Check (∏ (X : algMonoid_data), am_alg X ≡ (pr2 X : H X --> X)).

Local Notation γ := am_alg.

(** A H-monoid consists of the data previously detailed subject to an equation *)
Check (algMonoid st ≡
         ∑ (X : algMonoid_data),
         st X (PtIModule_from_monoid _ X)
           · # H (μ X) · γ X
         = γ X #⊗ identity X · (μ X)).

(** A H-monoid morphism between H-monoids X and Y consists of a morphism that is
both a morphism of skew monoids and of algebras *)
Check  (∏ (X Y : algMonoid st),
        algMonoid_Mor X Y ≡
          ∑ (f : skewMonoid_Mor _ X Y) , γ X · f = # H f · (γ Y)).


(** H-monoids form a category (see StructuralStrengths.precategory_algMonoid
   for the details)
 *)
Check ( precategory_algMonoid st ≡
          (make_precategory_ob_mor (algMonoid st) (algMonoid_Mor (F := H) )
             ,, _) ,, _ ,, _).

End Summary.

(** * Axiomatized theorem from Fiore-Saville

Covered by Complements.v
Axiomatization of Theorem 4.7 of "List object with
algebraic structure" (Fiore-Saville, extended version).

This is the only admitted result of this formalization.

 *)

Check (@Thm47 :
         ∏ {D C B A : category}
           (OC : Initial C)(chC : Colims_of_shape nat_graph C)
           (chA : Colims_of_shape nat_graph A)
           {J : C ⟶ A}(OJ : isInitial _ (J (InitialObject OC)))
           (omegaJ : is_omega_cocont J)
           {F : D ×C C ⟶ C}
           (omegaF : ∏ d , is_omega_cocont (functor_fix_fst_arg _ _ _ F d))
           {G : B ×C A ⟶ A}
           (omegaG : ∏ b , is_omega_cocont (functor_fix_fst_arg _ _ _ G b))
           {K : D ⟶ B} (h : F ∙ J ⟹ (K ×× J) ∙ G)
           {a : A}{d : D}(α : A ⟦ G (K d , a) , a ⟧)
           (** Initial algebra of F(_, d) using Adamek's lemma *)
           (μFd :=
              (InitialObject
                 (colimAlgInitial
                    OC (omegaF d)
                    (chC (initChain OC (functor_fix_fst_arg D C C F d)))))),
         ∃! (β : A ⟦ J (alg_carrier _ μFd) , a ⟧),
         h (d , alg_carrier _ μFd) · # G ( identity _ #, β ) · α  =
         # J (alg_map _ μFd) · β).



(** * Main result,
 stated in a void context: the category of H-monoids has an
 initial object under the following assumptions

covered by InitialAlgebraicMonoid.v
 *)
Check (algMonoid_Initial :
           (** V is a skew monoidal category *)
        ∏ (V : skewmonoidal_category),
         (** V has colimits of chains *)
         Colims_of_shape nat_graph V ->
         (** V has an initial object *)
         Initial V ->
         (** V has binary coproducts *)
         BinCoproducts V ->
         (** V has coequalizers *)
         ∏ (coeqsV : Coequalizers V)
         (** the tensor is left cocontinuous *)
         (ltensor_CC : (∏ X : V,
                 is_cocont
                   (functor_fix_snd_arg V V V (skewmonoidal_tensor V) X)))
         (** H is an endofunctor on V with a strength *),
      ∏ (H : V ⟶ V) (st : strength coeqsV _ H),
         (** H is omega cocontinuous *)
         is_omega_cocont H →
         Initial (precategory_algMonoid st)
         ).

(** Notation for binary coproducts of functors *)
Infix "++" := (BinCoproduct_of_functors _ _ _) .

(** The underlying object of V is the initial algebra of the endofunctor
    X ↦ I + H(X) *)
Definition underlying_object :
         ∏ (V : skewmonoidal_category)
         ω O cp coeqsV lcc 
         H st
         Hωcc,
       ((InitialObject (algMonoid_Initial V ω O cp coeqsV lcc H st Hωcc)
         : algMonoid st)
          (** The coercion yields the underlying object of V *)
        : V) =
       (** [alg_carrier F a] takes an F-algebra a and returns the underlying
           object *)
         alg_carrier
           (** here, F = I + H *)
           (constant_functor _ _ (skewmonoidal_I V) ++ H)
           (** and we consider the initial algebra *)
           (InitialObject (colimAlgInitial _ _ _))
  := 
    (* The proof *)
    (fun V ω O cp coeqsV lcc H st Hωcc =>
       A_is_InitialAlg_sumFI V ω O cp H Hωcc).

