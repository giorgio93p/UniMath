Require Import UniMath.Algebra.Lattice.

Definition bilattice (X : hSet) := lattice X × lattice X .
Definition make_bilattice {X : hSet} : lattice X -> lattice X -> bilattice X :=
  λ x y , x,, y.

Definition tlattice {X : hSet} (b : bilattice X) : lattice X := pr1 b .
Definition klattice {X : hSet} (b : bilattice X) : lattice X := pr2 b .

Definition meet {X : hSet} (b : bilattice X) : binop X := Lmin (tlattice b) .
Definition join {X: hSet} (b : bilattice X) : binop X := Lmax (tlattice b) .
Definition consensus {X : hSet} (b : bilattice X) : binop X := Lmin (klattice b) .
Definition gullibility {X : hSet} (b : bilattice X) : binop X := Lmax (klattice b) .


(** Bounded bilattices *)

Definition bounded_bilattice (X : hSet) :=
  ∑ (b : bilattice X) (tbot ttop kbot ktop : X), bounded_latticeop (tlattice b) tbot ttop × bounded_latticeop (klattice b) kbot ktop.

Definition bounded_bilattice_to_bilattice X : bounded_bilattice X → bilattice X := pr1.
Coercion bounded_bilattice_to_bilattice : bounded_bilattice >-> bilattice.

Definition fls {X : hSet} (b : bounded_bilattice X) : X := pr1 (pr2 b).
Definition tru {X : hSet} (b : bounded_bilattice X) : X := pr1 (pr2 (pr2 b)).
Definition bot {X: hSet} (b : bounded_bilattice X) : X := pr1 (pr2 (pr2 (pr2 b))) .
Definition top {X: hSet} (b : bounded_bilattice X) : X := pr1 (pr2 (pr2 (pr2 (pr2 b)))) .

Section prod_bilattices .
  Context {X1 X2 : hSet} .
  Variable l1 : lattice X1 .
  Variable l2 : lattice X2 .

  Definition prod_bilattice_carrier := setdirprod X1 X2 .
  Definition tmin : binop prod_bilattice_carrier :=
    λ x y, (((Lmin l1) (pr1 x) (pr1 y)),, (Lmax l2) (pr2 x) (pr2 y)) .
  Definition tmax : binop prod_bilattice_carrier :=
    λ x y, (((Lmax l1) (pr1 x) (pr1 y)),, (Lmin l2) (pr2 x) (pr2 y)) .
  Definition kmin : binop prod_bilattice_carrier :=
    λ x y, (((Lmin l1) (pr1 x) (pr1 y)),, (Lmin l2) (pr2 x) (pr2 y)) .
  Definition kmax : binop prod_bilattice_carrier :=
    λ x y, (((Lmax l1) (pr1 x) (pr1 y)),, (Lmax l2) (pr2 x) (pr2 y)) .

  Definition latticeop_prod_t : latticeop tmin tmax .
  Proof .
    unfold latticeop; repeat apply make_dirprod.
    - unfold isassoc; intros a b c; induction a; induction b; induction c; unfold tmin; apply dirprod_paths; simpl; [apply isassoc_Lmin | apply isassoc_Lmax].
    - unfold iscomm; intros a b; induction a; induction b; unfold tmin; apply dirprod_paths; simpl; [apply iscomm_Lmin | apply iscomm_Lmax].
    - unfold isassoc; intros a b c; induction a as [a1 a2]; induction b as [b1 b2]; induction c as [c1 c2]; unfold tmin; apply dirprod_paths; simpl; [apply isassoc_Lmax | apply isassoc_Lmin].
    - unfold iscomm; intros a b; induction a; induction b; unfold tmin; apply dirprod_paths; simpl; [apply iscomm_Lmax | apply iscomm_Lmin].
    - intros a b; induction a; induction b; unfold tmin; unfold tmax; apply dirprod_paths; simpl; [apply Lmin_absorb | apply Lmax_absorb].
    - intros a b; induction a; induction b; unfold tmin; unfold tmax; apply dirprod_paths; simpl; [apply Lmax_absorb | apply Lmin_absorb].
  Qed .

  Definition latticeop_prod_k : latticeop kmin kmax .
  Proof .
    unfold latticeop; repeat apply make_dirprod.
    - unfold isassoc; intros a b c; induction a; induction b; induction c; unfold kmin; apply dirprod_paths; simpl; apply isassoc_Lmin.
    - unfold iscomm; intros a b; induction a; induction b; unfold kmin; apply dirprod_paths; simpl; apply iscomm_Lmin.
    - unfold isassoc; intros a b c; induction a as [a1 a2]; induction b as [b1 b2]; induction c as [c1 c2]; unfold kmax; apply dirprod_paths; simpl; apply isassoc_Lmax .
    - unfold iscomm; intros a b; induction a; induction b; unfold kmax; apply dirprod_paths; simpl; apply iscomm_Lmax.
    - intros a b; induction a; induction b; unfold kmin; unfold kmax; apply dirprod_paths; simpl; apply Lmin_absorb .
    - intros a b; induction a; induction b; unfold kmin; unfold kmax; apply dirprod_paths; simpl; apply Lmax_absorb .
  Qed .

  Definition make_prod_bilattice := make_bilattice (mklattice latticeop_prod_t) (mklattice latticeop_prod_k) .
End prod_bilattices .

Section example.
  Definition AND : binop boolset := λ b1 b2,
                                    match b1 with true => b2 | false => b1 end.
  Definition OR : binop boolset := λ b1 b2,
                                   match b1 with true => b1 | false => b2 end.

  Definition bool_latticeop : latticeop AND OR .
  Proof .
    unfold latticeop; repeat apply make_dirprod;
      try (unfold isassoc; intros a b c; induction a; induction b; induction c; simpl; trivial);
      try (unfold iscomm; intros a b; induction a; induction b; simpl; trivial);
      try (intros a b; induction a; induction b; simpl; trivial) .
  Qed.

  Definition FOUR := make_prod_bilattice (mklattice bool_latticeop) (mklattice bool_latticeop) .
End example.
