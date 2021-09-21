Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.


Section def_Institution.
  Variable truth_values : hSet .

(**
    sign : category,
    sent : sign → hSet ,
    mod : sign → category,
    ⊨ : sign -> ob (mod sign) -> sent sign -> truth_values  .
such that
    forall (σ : s --> s' : sign)
           (m' : ob (mod (s')))
           φ : sent(s),

           m' ⊨ #sent(σ)(φ)  = #mod(σ)(m')  ⊨ φ

**)
  Definition institution_data : UU
    := ∑ sign : category,  (sign → sign) .

End def_Institution.
