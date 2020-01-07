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

Require Import SkewMonoidalCategories.
Require Import StructuralStrengths.
Require Import IModules.
Require Import Complements.
Require Import SkewMonoids.
Require Import InitialAlgebraicMonoid.

Local Open Scope cat.

(** Notation for product of functors *)
Delimit Scope functor_scope with F.
Infix "××" := pair_functor (at level 31).

Section Summary.



(**
The command:

Check (x ::= y) 

succeeds if and only if [x] is convertible to [y]

*)
Notation  "x ::= y"  := ((idpath _ : x = y) = idpath _) (at level 70, no associativity).

Fail Check (true ::= false).
Check (true ::= true).


(** We suppose given a skew monoidal category V
(see SkewMonoidalCategories.skewmonoidal_precat for the definition)
 *)
Context (V : skewmonoidal_precat) (hsV : has_homsets V).

(** Some notations for the monoidal structure *)
Notation I := (skewmonoidal_precat_unit V).
Notation α' := (skewmonoidal_precat_associator V).
Notation λ' := (skewmonoidal_precat_left_unitor V).
Notation ρ' := (skewmonoidal_precat_right_unitor V).
Notation tensor := (skewmonoidal_precat_tensor V).

(** We denote ⊗ the tensor product, and #⊗ the action on morphisms *)
Notation "X ⊗ Y" := (tensor (X , Y)).
Notation "f #⊗ g" := (# tensor  (f #, g)) (at level 31).


(** * Pointed I-modules
covered by IModules.v 

We sometimes call them simply I-modules.
 *)



(**
A pointed I-module on V consists of an object F of V together
with two maps, subject to some laws given later.
There is an implicit coercion between pointed I-modules and objects of V
 *)
Check (IModule_data V ::= ∑ (F : V) , F ⊗ I --> F × I --> F).

(** Some notations for the maps *)
Local Definition σ (F : IModule_data V) : F ⊗ I --> F := pr1 (pr2 F).
Local Definition ϵ (F : IModule_data V) : I --> F := pr2 (pr2 F).

(** A pointed I-module consists of the data previously defined subject to
  two laws *)
Check (IModule V ::=
         ∑ (F : IModule_data V) ,
         (** First law *)
         (ρ' F · σ F  = identity _)
           ×
           (** Second law *)
           (α' (((F : V) , I) , I) · (identity _) #⊗ ((λ' I) ) · σ F  =
            σ F #⊗ identity I · σ F)
      ).


(** A morphism between pointed I-modules X and Y is a morphism between
underlying objects of V subject to two laws.
 *)
Check  (∏ (X Y : IModule V),
        IModule_Mor V X Y ::=
          ∑ (f :  V ⟦X, Y⟧) ,
          (** the unit is preserved *)
          (ϵ X · f = ϵ Y)
            (** the morphism is compatible with σ *)
            × σ X · f = (f #⊗ identity _) · σ Y).

(** pointed I-modules form a category (see StructuralStrengths.precategory_algMonoid
   for the details)
 *)
Check (precategory_IModule V hsV ::=
          (make_precategory_ob_mor (IModule V) (IModule_Mor V)
             ,, _) ,, _ ,, _).

(** We denote M this category in the following *)
Notation M := (precategory_IModule V hsV).

(** The forgetful functor from M to V *)
Check (forget_IModules V hsV : functor M V).
(** We use the notation 𝒰 in the following when we want to make explicit the
coercion between pointed I-modules and objects of V. *)
Notation 𝒰 := (forget_IModules V hsV).
Check (∏ (X : IModule V), 𝒰 X ::= (X : V)).

(** The unit can be given the structure of a pointed I-module *)
Definition IM : IModule V := IModule_I V.

Lemma IM_as_object_of_V_is_I : 𝒰 IM = I.
  reflexivity.
Qed.

(** The tensor product can be lifted to the category of I-modules, there
 called [IModule_tensor] *)
Check (IModule_tensor V : IModule V -> IModule V -> IModule V ).
Infix "⊗M" := (IModule_tensor V) (at level 31).

Lemma IModule_tensor_lifts_tensor (A B : IModule V) :
  𝒰 (A ⊗M B) = (𝒰 A) ⊗ (𝒰 B).
Proof.
  reflexivity.
Qed.


(** * Structural strengths 
covered by StructuralStrengths.v

************* *)

(** We suppose given an endofunctor H on V *)
Context  (H : V ⟶ V).

(**
A structural strength consists of a natural transformation between the two
relevant  parallel functors from V × M (denoted V ⊠ M below) to V, subject
to two laws.

There is an implicit coercion between strengths and natural transformations.
 *)
Check (strength V hsV H ::=
         ∑ (st : nat_trans (C := V ⊠ M) (C' := V)
                   ((H ×× 𝒰) ∙ tensor)
                   ((functor_identity _ ×× 𝒰) ∙ tensor ∙ H)
           ),
         (** first law: triangle *)
         (∏ (a : V), ρ' (H a) · st (a, (IM : M))  = # H (ρ' a))
         (** second law: pentagon *)
           ×
           (∏ (a : V),
            ∏ (x y : IModule V) (z : V)(f : V ⟦ x ⊗ y , z ⟧)
              (eqf : (σ x #⊗ identity y) · f =
                     α' ((x , I) , y) · (identity x #⊗ λ' y) · f),
            (α' ((H a,  x),  y)) · st (a , (x ⊗M y : M))
                                 · # H (identity _ #⊗ f)
            =
            (st (a, (x : M)) #⊗ identity y)
              · st ((a ⊗ x), (y : M))
              · # H (α' ((a,  x),  y))
              · # H (identity _ #⊗ f))
      ).

(** * Skew H-monoids

.. for H a strong endofonctor on V

covered by StructuralStrengths.v

************* *)


(** Notations for the unit and multiplication of a (skew) monoid (see
    SkewMonoids.v for the precise definition) *)
Local Definition η (m : skewMonoid V) : V ⟦I , m⟧ := sm_unit V m.
Local Definition μ (m : skewMonoid V) : V ⟦m ⊗ m, m⟧ := sm_mult V m.

(** We suppose given a strength for the endofunctor H *)
Context (st : strength V hsV H).

(**
A H-monoid consists of a skew monoid with an H algebra structure,
subject to some laws.
There is an implicit coercion between H-monoids and skew monoids.
 *)
Check (@algMonoid_data V H ::= ∑ X : skewMonoid V, H X --> X).

(** Notation for the algebra structure *)
Local Definition κ (X : @algMonoid_data V H) : H X --> X := pr2 X.

(** A H-monoid consists of the data previously detailed subject to an equation *)
Check (algMonoid st ::=
         ∑ (X : algMonoid_data),
         (st : nat_trans _ _)
           (X , (IModule_from_monoid _ X : M))
           · # H (μ X) · κ X
         = κ X #⊗ identity X · (μ X)).

(** A H-monoid morphism between H-monoids X and Y consists of a morphism that is
both a morphism of skew monoids and of algebras *)
Check  (∏ (X Y : algMonoid st),
        algMonoid_Mor X Y ::=
          ∑ (f : skewMonoid_Mor _ X Y) , κ X · f = # H f · (κ Y)).


(** H-monoids form a category (see StructuralStrengths.precategory_algMonoid
   for the details)
 *)
Check ( precategory_algMonoid st ::=
          (make_precategory_ob_mor (algMonoid st) (algMonoid_Mor (F := H) )
             ,, _) ,, _ ,, _).

End Summary.

(** * Axiomatized theorem from Fiore-Saville

TODO
Axiomatization of Theorem 4.7 of "List object with
algebraic structure" (Fiore-Saville, extended version).

This is the only admitted result of this formalization.

 *)

Check (@Thm47 :
         ∏ {D C B A : precategory}
           (hsC : has_homsets C)(OC : Initial C)(chC : Colims_of_shape nat_graph C)
           (hsA : has_homsets A)(chA : Colims_of_shape nat_graph A)
           {J : C ⟶ A}(OJ : isInitial _ (J (InitialObject OC)))
           (omegaJ : is_omega_cocont J)
           {F : D ⊠ C ⟶ C}
           (omegaF : ∏ d , is_omega_cocont (functor_fix_fst_arg _ _ _ F d))
           {G : B ⊠ A ⟶ A}
           (omegaG : ∏ b , is_omega_cocont (functor_fix_fst_arg _ _ _ G b))
           {K : D ⟶ B} (h : F ∙ J ⟹ (K ×× J) ∙ G)
           {a : A}{d : D}(α : A ⟦ G (K d , a) , a ⟧)
           (** Initial algebra of F(_, d) using Adamek's lemma *)
           (μFd :=
              (InitialObject
                 (colimAlgInitial
                    hsC OC (omegaF d)
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
        ∏ (V : skewmonoidal_precat) (hsV : has_homsets V),
         (** V has colimits of chains *)
         Colims_of_shape nat_graph V ->
         (** V has an initial object *)
         Initial V ->
         (** V has binary coproducts *)
         BinCoproducts V ->
         (** the tensor is left cocontinuous *)
         ((∏ X : V,
                 is_cocont
                   (functor_fix_snd_arg V V V (skewmonoidal_precat_tensor V) X)))
         (** H is an endofunctor on V with a strength *)
      → ∏ (H : V ⟶ V) (st : strength V hsV H),
         (** H is omega cocontinuous *)
         is_omega_cocont H →
         Initial (precategory_algMonoid st)
         ).

