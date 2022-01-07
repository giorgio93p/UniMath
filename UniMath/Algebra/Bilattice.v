Require Import UniMath.Algebra.Lattice.

Section bilattices .
  Definition bilattice (X : hSet) := lattice X × lattice X .

  Definition make_bilattice {X : hSet} (tLattice kLattice: lattice X) : bilattice X := tLattice,, kLattice.

  Definition tlattice {X : hSet} (b : bilattice X) : lattice X := pr1 b .
  Definition klattice {X : hSet} (b : bilattice X) : lattice X := pr2 b .

  Definition meet {X : hSet} (b : bilattice X) : binop X := Lmin (tlattice b) .
  Definition join {X: hSet} (b : bilattice X) : binop X := Lmax (tlattice b) .
  Definition consensus {X : hSet} (b : bilattice X) : binop X := Lmin (klattice b) .
  Definition gullibility {X : hSet} (b : bilattice X) : binop X := Lmax (klattice b) .
End bilattices .


(** Bounded bilattices *)
Section bounded_bilattices .
  Definition bounded_bilattice (X : hSet) :=
    bounded_lattice X × bounded_lattice X.

  Definition make_bounded_bilattice {X : hSet} (tLattice kLattice : bounded_lattice X) : bounded_bilattice X := tLattice,, kLattice.

  Definition bounded_bilattice_to_bilattice X (b : bounded_bilattice X) : bilattice X := make_bilattice (pr1 b) (pr2 b) .
  Coercion bounded_bilattice_to_bilattice : bounded_bilattice >-> bilattice.

  Definition fls {X : hSet} (b : bounded_bilattice X) : X :=  Lbot (pr1 b).
  Definition tru {X : hSet} (b : bounded_bilattice X) : X :=  Ltop (pr1 b).
  Definition bot {X: hSet} (b : bounded_bilattice X) : X :=  Lbot (pr2 b) .
  Definition top {X: hSet} (b : bounded_bilattice X) : X :=  Ltop (pr2 b) .
End bounded_bilattices .
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
    unfold latticeop; repeat apply make_dirprod; [
      unfold isassoc; intros a b c; induction a; induction b; induction c; unfold tmin; apply dirprod_paths; [apply isassoc_Lmin | apply isassoc_Lmax]
    | unfold iscomm; intros a b; induction a; induction b; unfold tmin; apply dirprod_paths; [apply iscomm_Lmin | apply iscomm_Lmax]
    | unfold isassoc; intros a b c; induction a as [a1 a2]; induction b as [b1 b2]; induction c as [c1 c2]; unfold tmin; apply dirprod_paths; [apply isassoc_Lmax | apply isassoc_Lmin]
    | unfold iscomm; intros a b; induction a; induction b; unfold tmin; apply dirprod_paths; [apply iscomm_Lmax | apply iscomm_Lmin]
    | intros a b; induction a; induction b; unfold tmin; unfold tmax; apply dirprod_paths; [apply Lmin_absorb | apply Lmax_absorb]
    | intros a b; induction a; induction b; unfold tmin; unfold tmax; apply dirprod_paths; [apply Lmax_absorb | apply Lmin_absorb] ].
  Defined .

  Definition latticeop_prod_k : latticeop kmin kmax .
  Proof .
    unfold latticeop; repeat apply make_dirprod; [
      unfold isassoc; intros a b c; induction a; induction b; induction c; unfold kmin; apply dirprod_paths; apply isassoc_Lmin
    | unfold iscomm; intros a b; induction a; induction b; unfold kmin; apply dirprod_paths; apply iscomm_Lmin
    | unfold isassoc; intros a b c; induction a as [a1 a2]; induction b as [b1 b2]; induction c as [c1 c2]; unfold kmax; apply dirprod_paths; apply isassoc_Lmax
    | unfold iscomm; intros a b; induction a; induction b; unfold kmax; apply dirprod_paths; apply iscomm_Lmax
    | intros a b; induction a; induction b; unfold kmin; unfold kmax; apply dirprod_paths; apply Lmin_absorb
    | intros a b; induction a; induction b; unfold kmin; unfold kmax; apply dirprod_paths; apply Lmax_absorb] .
  Defined .

  Definition make_prod_bilattice := make_bilattice (mklattice latticeop_prod_t) (mklattice latticeop_prod_k) .
End prod_bilattices .

Section bounded_prod_bilattices.
  Context {X1 X2 : hSet} .
  Variable bl1 : bounded_lattice X1 .
  Variable bl2 : bounded_lattice X2 .

  Definition tbot : prod_bilattice_carrier :=
    Lbot bl1,, Ltop bl2 .
  Definition ttop : prod_bilattice_carrier :=
    Ltop bl1,, Lbot bl2 .
  Definition kbot : prod_bilattice_carrier :=
    Lbot bl1,, Lbot bl2 .
  Definition ktop : prod_bilattice_carrier :=
    Ltop bl1,, Ltop bl2.

  Definition bounded_latticeop_prod_t : bounded_latticeop (mklattice (latticeop_prod_t bl1 bl2)) tbot ttop .
  Proof.
    unfold bounded_latticeop; unfold islunit; apply make_dirprod; intro x; apply dirprod_paths; [apply islunit_Lmax_Lbot | apply islunit_Lmin_Ltop | apply islunit_Lmin_Ltop | apply islunit_Lmax_Lbot].
  Defined.

  Definition bounded_latticeop_prod_k : bounded_latticeop (mklattice (latticeop_prod_k bl1 bl2)) kbot ktop .
  Proof.
    unfold bounded_latticeop; unfold islunit; apply make_dirprod; intro x; apply dirprod_paths; [apply islunit_Lmax_Lbot | apply islunit_Lmax_Lbot | apply islunit_Lmin_Ltop | apply islunit_Lmin_Ltop].
  Defined.

  Definition make_bounded_prod_bilattice := make_bounded_bilattice (mkbounded_lattice bounded_latticeop_prod_t) (mkbounded_lattice bounded_latticeop_prod_k) .
End bounded_prod_bilattices.

Section bilattice_FOUR.
  Definition AND : binop boolset :=
    λ b1 b2,
    match b1 with true => b2 | false => b1 end.

  Definition OR : binop boolset :=
    λ b1 b2,
    match b1 with true => b1 | false => b2 end.

  Definition bool_lattice : lattice boolset .
  Proof .
    unfold lattice; exists AND; exists OR;
      unfold latticeop; repeat apply make_dirprod;
        try (unfold isassoc; intros a b c; induction a; induction b; induction c; trivial);
        try (unfold iscomm; intros a b; induction a; induction b; trivial);
        try (intros a b; induction a; induction b; trivial) .
  Defined.

  Definition bool_boundedlattice : bounded_lattice boolset .
  Proof.
    unfold bounded_lattice; exists bool_lattice; exists false; exists true;
      unfold bounded_latticeop; unfold islunit; apply make_dirprod; unfold bool_lattice; unfold Lmax; trivial .
  Defined.

  Definition FOUR := make_bounded_prod_bilattice bool_boundedlattice bool_boundedlattice .
End bilattice_FOUR.
