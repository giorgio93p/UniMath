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

Section def_Institution.
  Variable truth_values : hSet .
(**
    sign : category,
    sent : sign → SET,
    mod : sign → category,
    ⊨ : sign -> ob (mod sign) -> sent sign -> truth_values  .
such that
    forall (σ : s --> s' : sign)
           (m' : ob (mod (s')))
           φ : sent(s),

           m' ⊨ #sent(σ)(φ)  = #mod(σ)(m')  ⊨ φ

 **)

  Definition sents_of (sign : category) : UU :=
    functor sign type_precat . (** for some reason, sign → SET fails below; do we need it however? **)

  Definition mods_of (sign: category) : UU :=
    functor (oppositeCategory sign) type_precat .

  Definition satisfaction_of (sign : category) (sent : sents_of sign) (mod : oppositeCategory sign ⟶ type_precat) : UU :=
    ∏ Σ : sign, mod Σ -> (pr1 sent) Σ -> truth_values .

  Definition institution_data : UU
    := ∑ (sign : category), ∑ (sent : sents_of sign), ∑ (mod: mods_of sign), satisfaction_of sign sent mod  .

  Definition make_institution_data (sign : category) (sent : sents_of sign) (mod: mods_of sign) (rel : satisfaction_of sign sent mod) : institution_data
    := sign ,, sent ,, mod ,,  rel .

  Definition sign (I : institution_data) : category := pr1 I.
  Definition mod (I : institution_data) : mods_of (sign I) :=  pr122 I.
  Definition sent (I : institution_data) : sents_of (sign I) := pr12 I.
  Definition satisfaction (I : institution_data) : satisfaction_of (sign I) (sent I) (mod I) := pr222 I.

  Variable I : institution_data .

  Definition is_institution (I : institution_data) : UU
    :=
      ∏ (Σ Σ' : sign I) (σ : Σ --> Σ'),
      ∏ (M' : pr1 (mod I) Σ'),
      ∏ φ : pr1 (sent I) Σ,
            satisfaction I Σ' M' (#(pr1 (sent I)) σ φ) = satisfaction I Σ (#(pr1 (mod I)) σ M') φ.

End def_Institution.
