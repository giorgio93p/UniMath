Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
(**
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.opp_precat.
 **)
Require Import UniMath.CategoryTheory.All.

Local Open Scope cat .
Declare Scope institutions.
Local Open Scope institutions.

Section def_Institution.
  Definition signature : UU := category .

  Definition signature_to_category (sign : signature) : category := sign .
  Coercion signature_to_category : signature >-> category .

  Definition sents_of (sign : signature)  : UU :=
    functor sign type_precat . (** for some reason, sign → SET fails below; do we need it however? **)

  Definition mods_of (sign: signature) : UU :=
    functor (oppositeCategory sign) type_precat .

  Definition satisfaction_of (sign : signature) (sent : sents_of sign) (mod : oppositeCategory sign ⟶ type_precat) : UU :=
    ∏ Σ : sign, mod Σ -> (pr1 sent) Σ -> bool .

  Definition institution_data : UU
    := ∑ (sign : signature), ∑ (sent : sents_of sign), ∑ (mod: mods_of sign), satisfaction_of sign sent mod  .

  Definition make_institution_data (sign : signature) (sent : sents_of sign) (mod: mods_of sign) (rel : satisfaction_of sign sent mod) : institution_data
    := sign ,, sent ,, mod ,,  rel .

  Definition sign (I : institution_data) : category := pr1 I.
  Definition mod (I : institution_data) : mods_of (sign I) :=  pr122 I.
  Definition sent (I : institution_data) : sents_of (sign I) := pr12 I.
  Definition satisfaction (I : institution_data) : satisfaction_of (sign I) (sent I) (mod I) := pr222 I.

  Definition satisfies {I:institution_data} {Σ : sign I} (M : pr1 (mod I) Σ) (φ : pr1 (sent I) Σ) := satisfaction I Σ M φ .
  Notation "M ⊧ φ" := (satisfies M φ) (at level 100) : institutions.

  Definition is_institution (I : institution_data) : UU
    :=
      ∏ (Σ Σ' : sign I) (σ : Σ --> Σ'),
      ∏ (M' : pr1 (mod I) Σ'),
      ∏ φ : pr1 (sent I) Σ,
            satisfies M' (#(pr1 (sent I)) σ φ) = satisfies (#(pr1 (mod I)) σ M') φ.

  (* Mossakowski: We assume that all institutions are such that satisfaction is
invariant under model isomorphism, i.e., if Σ-models M, M' are isomorphic, then
M ⊧ φ iff M' ⊧ φ for all Σ-sentences φ. *)

  Definition institution := total2 is_institution .

  Definition institution_to_institution_data (I : institution) : institution_data := pr1 I.
  Coercion institution_to_institution_data : institution >-> institution_data.
End def_Institution.
