Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.Categories.PrecategoryOfCategories.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.Type.Core.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.OrderTheory.Lattice.Lattice.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.Combinatorics.Lists.


Definition map_compose_idfun_l {A B : UU} (f : A → B) (xs : list A):
  map ((idfun B) ∘ f) xs = map f xs.
Proof.
  use map_homot.
  now intro x.
Defined.

Definition map_compose_idfun_r {A B : UU} (f : A → B) (xs : list A):
  map (f ∘ (idfun A)) xs = map f xs.
Proof.
  use map_homot.
  now intro x.
Defined.


Local Open Scope cat .
  Definition forgetful_category_precategory_to_type_precat : functor category_precategory type_precat.
  Proof.
    use make_functor.
    - use make_functor_data.
      exact (λ C, pr1 C).
      intros ? ? F.
      cbn in F.
      exact F.
    - split.
      -- intro. apply idpath.
      -- intros ? ? ? ? ?. apply idpath.
  Defined.

  Definition forgetful_cat_of_setcategory_to_hset : functor cat_of_setcategory HSET.
  Proof.
    use make_functor.
    - use make_functor_data.
      exact (λ C, setcategory_objects_set C).
      intros ? ? F.
      cbn in F.
      exact F.
    - split.
      -- intro.
         apply idpath.
      -- intros ? ? ? ? ?. apply idpath.
  Defined.

  Definition forgetful_setcategory_to_category_precategory
    : univalent_cat_of_setcategory ⟶ category_precategory.
  Proof.
    use make_functor.
    - use make_functor_data.
      exact (λ C, category_from_setcategory C).
      intros ? ? F.
      exact F.
    - split.
      -- intro. apply idpath.
      -- intros ? ? ? ? ?. apply idpath.
  Defined.

Declare Scope institutions.
Local Open Scope institutions.

Section def_Institution.
  Context {truth_vals : hSet}.

  Definition signature : UU := category .

  Definition signature_to_category (sign : signature) : category := sign .
  Coercion signature_to_category : signature >-> category .

  Definition sents_of_sign (sign : signature)  : UU :=
    functor sign type_precat .

  Definition mods_of_sign (sign: signature) : UU :=
    functor sign (opp_precat category_precategory) .
(*
  Definition strict_mods_of_sign (sign: signature) : UU :=
    functor sign (opp_precat univalent_cat_of_setcategory) .

  Definition strict_mods_of_sign_to_mods_of_sign {sign : signature} (m : strict_mods_of_sign sign) : mods_of_sign (sign) := m ∙ functor_opp forgetful_setcategory_to_category_precategory.
 *)

  Definition valuations_of_sign (sign : signature) (sent : sents_of_sign sign) (mod : mods_of_sign sign) : UU.
  Proof.
    unfold sents_of_sign in sent.
    exact (sent ⟹ mod ∙ (functor_opp forgetful_category_precategory_to_type_precat) ∙ (@contra_hom_functor type_precat truth_vals)).
  Defined.

  Print valuations_of_sign.

  Definition institution_data : UU
    := ∑ (sign : signature), ∑ (sent : sents_of_sign sign), ∑ (mod: mods_of_sign sign), valuations_of_sign sign sent mod  .
(*
  Definition strict_institution_data : UU
    := ∑ (sign : signature), ∑ (sent : sents_of_sign sign), ∑ (mod: strict_mods_of_sign sign), valuations_of_sign sign sent (strict_mods_of_sign_to_mods_of_sign mod)  .
*)
  Definition make_institution_data (sign : signature) (sent : sents_of_sign sign) (mod: mods_of_sign sign) (rel : valuations_of_sign sign sent mod) : institution_data
    := sign ,, sent ,, mod ,,  rel .
(*
  Definition strict_institution_data_to_institution_data (I : strict_institution_data) : institution_data.
  Proof.
    use make_institution_data.
    - exact (pr1 I).
    - exact (pr12 I).
    - exact (strict_mods_of_sign_to_mods_of_sign (pr122 I)).
    - exact (pr222 I).
  Defined.
  Coercion strict_institution_data_to_institution_data : strict_institution_data >-> institution_data.
*)
  Definition sign (I : institution_data) : category := pr1 I.
  Definition mod (I : institution_data) : mods_of_sign (sign I) :=  pr122 I.
  Definition sent (I : institution_data) : sents_of_sign (sign I) := pr12 I.
  Definition valuation (I : institution_data) : valuations_of_sign (sign I) (sent I) (mod I) := pr222 I.

  Definition models (I : institution_data) (Σ : sign I) : category .
  Proof.
    set (M := mod I).
    unfold mods_of_sign in M.
    exact (M Σ).
  Defined.

  Definition model_transl (I : institution_data) {Σ Σ' : sign I} (σ : Σ --> Σ') : functor (models I Σ') (models I Σ).
  Proof.
    set (M := mod I).
    unfold mods_of_sign in M.
    exact (#M σ).
  Defined.

  Definition sentences (I : institution_data) (Σ : sign I) : UU .
  Proof.
    set (S := sent I).
    unfold sents_of_sign in S.
    exact (S Σ).
  Defined.

  Definition sentence_transl (I : institution_data) {Σ Σ' : sign I} (σ : Σ --> Σ') : (sentences I Σ) -> (sentences I Σ').
  Proof.
    set (S := sent I).
    unfold sents_of_sign in S.
    exact (#S σ).
  Defined.

  Definition valuation_of {I:institution_data} {Σ : sign I} (M : models I Σ) (s : sentences I Σ) : truth_vals.
  Proof.
    set (V := (valuation I)).
    unfold valuations_of_sign in V.
    exact (V Σ s M).
  Defined.
  Notation "M ⊧ s" := (valuation_of M s) (at level 50) : institutions.

  (* Opaque because truth_vals is an hSet *)
  Lemma institution_condition (I : institution_data) : (
      ∏ {Σ Σ' : sign I} (σ : Σ --> Σ') (M' : models I Σ')  (s : sentences I Σ),
      (M' ⊧ (sentence_transl I σ s)) = ((model_transl I σ M') ⊧ s)
  ).
  Proof.
    intros ? ? σ M' s.
    set (prop := nat_trans_ax (valuation I) _ _ σ).
    exact (eqtohomot (eqtohomot prop s) M').
  Qed.

  Definition is_institution (I : institution_data) : UU :=
    (
      ∏ (Σ : sign I) (M M' : models I Σ), are_isomorphic M M' -> ∏ (s : sentences I Σ), M ⊧ s = M' ⊧ s
    )
  .
  Definition isaprop_is_institution (I : institution_data) (Σ : sign I) (M M' : models I Σ) (w : iso M M') (s : sentences I Σ) : isaprop (M ⊧ s = M' ⊧ s).
  Proof.
    use setproperty.
  Qed.

  Definition institution := total2 is_institution .

  Definition institution_to_institution_data (I : institution) : institution_data := pr1 I.
  Coercion institution_to_institution_data : institution >-> institution_data.

  Definition make_institution (I : institution_data) (w : is_institution I) : institution := I,, w.

  Definition sem_equiv (I : institution) {Σ:sign I} (s1 s2 : sentences I Σ) :=
    ∏ (M : models I Σ), M ⊧ s1 = M ⊧ s2 .
End def_Institution.
