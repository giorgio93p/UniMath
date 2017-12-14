(* Category generated by a preorder *)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.

Section po_category_def.
Context {X : UU}.
Context (PO : po X).

(* Precategory over a po *)
Definition po_precategory_ob_mor : precategory_ob_mor :=
    precategory_ob_mor_pair X (carrierofpo X PO).

Definition po_precategory_data : precategory_data :=
  precategory_data_pair (po_precategory_ob_mor)
                        (pr2 (pr2 PO)) (pr1 (pr2 PO)).


Lemma po_homsets_isaprop : ∏(a b : po_precategory_data),
                      isaprop (po_precategory_data ⟦a,b⟧).
Proof.
  intros.
  apply propproperty.
Defined.

Definition po_precategory_data_is_precategory :
  is_precategory po_precategory_data.
Proof.
  use mk_is_precategory; intros; apply po_homsets_isaprop.
Defined.

Definition po_precategory  : precategory :=
  tpair _ po_precategory_data po_precategory_data_is_precategory.

(* Category over po *)
Definition po_precategory_has_homsets : has_homsets po_precategory_ob_mor.
Proof.
  intros a b.
  apply hlevelntosn.
  apply po_homsets_isaprop.
Defined.

Definition po_category : category :=
   tpair _ po_precategory po_precategory_has_homsets.

End po_category_def.