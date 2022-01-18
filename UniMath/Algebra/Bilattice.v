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

  Definition iscomm_consensus {X : hSet} (b : bilattice X) : iscomm (consensus b) := iscomm_Lmin (klattice b) .
  Definition iscomm_gullibility {X : hSet} (b : bilattice X) : iscomm (gullibility b) := iscomm_Lmax (klattice b) .
  Definition iscomm_meet {X : hSet} (b : bilattice X) : iscomm (meet b) := iscomm_Lmin (tlattice b) .
  Definition iscomm_join {X : hSet} (b : bilattice X) : iscomm (join b) := iscomm_Lmax (tlattice b) .

  Definition tle {X : hSet} (b : bilattice X) : hrel X := Lle (tlattice b).
  Definition kle {X : hSet} (b : bilattice X) : hrel X := Lle (klattice b).
  Definition tge {X : hSet} (b : bilattice X) : hrel X := Lge (tlattice b).
  Definition kge {X : hSet} (b : bilattice X) : hrel X := Lge (klattice b).
End bilattices .

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

Section interlaced_bilattices .
  Definition is_interlaced {X : hSet} (b : bilattice X) : UU :=
    ∏ x y z : X,
              (meet b x y = x -> meet b (consensus b x z) (consensus b y z) = consensus b x z)
                ×
                (meet b x y = x -> (meet b (gullibility b x z) (gullibility b y z)) = gullibility b x z)
                ×
                (consensus b x y = x -> consensus b (meet b x z) (meet b y z) = meet b x z)
                ×
                (consensus b x y = x -> consensus b (join b x z) (join b y z) = join b x z) .

  Definition interlaced_bilattice (X : hSet) :=
    ∑ b : bilattice X,  is_interlaced b.

  Definition make_interlaced_bilattice {X : hSet} {b : bilattice X} (is : is_interlaced b) : interlaced_bilattice X := b,,is.

  Definition interlaced_bilattice_to_bilattice {X : hSet} (b: interlaced_bilattice X) : bilattice X := pr1 b.
  Coercion interlaced_bilattice_to_bilattice : interlaced_bilattice >-> bilattice .
End interlaced_bilattices.

Section distributive_bilattices.

  Definition distributivity {X : hSet} (op1 op2 : binop X) :=
    ∏ x y z : X, op1 x (op2 y z) = op2 (op1 x y) (op1 x z) .

  Definition is_distributive_lattice {X : hSet} (l : lattice X) :=
    (distributivity (Lmin l) (Lmax l)) × distributivity (Lmax l) (Lmin l) .

  Definition is_distributive_bilattice {X : hSet} (b : bilattice X) :=
              is_distributive_lattice (klattice b)
                × is_distributive_lattice (tlattice b)
                × distributivity (consensus b) (meet b)
                × distributivity (meet b) (consensus b)
                × distributivity (consensus b) (join b)
                × distributivity (join b) (consensus b)
                × distributivity (gullibility b) (meet b)
                × distributivity (meet b) (gullibility b)
                × distributivity (gullibility b) (join b)
                × distributivity (join b) (gullibility b)
  .
  Definition distributive_bilattice (X : hSet) :=
    ∑ b : bilattice X, is_distributive_bilattice b.

  Definition make_distributive_bilattice {X : hSet} {b : bilattice X} (is : is_distributive_bilattice b) : distributive_bilattice X := b,,is.

  Theorem distributive_bilattices_are_interlaced_bilattices {X : hSet} {b : bilattice X} (p : is_distributive_bilattice b) : is_interlaced b .
  Proof.
    unfold is_interlaced; intros x y z; repeat split; induction p as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 p10]]]]]]]]]; intro H.
    - rewrite iscomm_consensus with (x0 := x), iscomm_consensus with (x0 := y),  <- p3,  H; reflexivity.
    - rewrite iscomm_gullibility with (x0 := x), iscomm_gullibility with (x0 := y), <- p7, H; reflexivity.
    - rewrite iscomm_meet with (x0 := x), iscomm_meet with (x0 := y), <- p4, H;  reflexivity.
    - rewrite iscomm_join with (x0 := x), iscomm_join with (x0 := y), <- p6,  H; reflexivity .
  Defined.

  Definition distributive_bilattices_to_interlaced_bilattices {X : hSet} (b : distributive_bilattice X) :=
    make_interlaced_bilattice (distributive_bilattices_are_interlaced_bilattices (pr2 b)).

  Coercion distributive_bilattices_to_interlaced_bilattices : distributive_bilattice >-> interlaced_bilattice .
End distributive_bilattices.
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
    unfold latticeop; do 4 (try use make_dirprod).
    -  unfold isassoc; intros a b c; induction a, b, c; unfold tmin; use dirprod_paths; [use isassoc_Lmin | use isassoc_Lmax].
    - unfold iscomm; intros a b; induction a, b; unfold tmin; use dirprod_paths; [use iscomm_Lmin | use iscomm_Lmax] .
    - unfold isassoc; intros a b c; induction a,  b, c; unfold tmin; use dirprod_paths; [use isassoc_Lmax | use isassoc_Lmin] .
    - unfold iscomm; intros a b; induction a, b; unfold tmin; use dirprod_paths; [use iscomm_Lmax | use iscomm_Lmin ].
    - intros a b; induction a, b; unfold tmin; unfold tmax; use dirprod_paths; [use Lmin_absorb | use Lmax_absorb ].
    - intros a b; induction a, b; unfold tmin; unfold tmax; use dirprod_paths; [use Lmax_absorb | use Lmin_absorb] .
  Defined .

  Definition latticeop_prod_k : latticeop kmin kmax .
  Proof .
    unfold latticeop; do 4 (try use make_dirprod).
    -  unfold isassoc; intros a b c; induction a, b, c; unfold kmin; use dirprod_paths; use isassoc_Lmin.
    - unfold iscomm; intros a b; induction a, b; unfold kmin; use dirprod_paths; use iscomm_Lmin.
    - unfold isassoc; intros a b c; induction a, b, c; unfold kmax; use dirprod_paths; use isassoc_Lmax .
    - unfold iscomm; intros a b; induction a, b; unfold kmax; use dirprod_paths; use iscomm_Lmax .
    - intros a b; induction a, b; unfold kmin; unfold kmax; use dirprod_paths; use Lmin_absorb .
    - intros a b; induction a, b; unfold kmin; unfold kmax; use dirprod_paths; use Lmax_absorb .
  Defined .

  Definition make_prod_bilattice := make_bilattice (mklattice latticeop_prod_t) (mklattice latticeop_prod_k) .
(*
  Definition Lwhatever {X : hSet} (is : lattice X) : ∏ x y : X, Lmax is x y = x -> Lle is y x.
  Proof.
    intros x y H.
    rewrite <- H. exact (Lmax_le_r is _ _).
  Defined.
*)
  Definition Lmax_le_case_ {X : hSet} (is : lattice X) :  ∏ x y z : X, Lle is x z → Lle is y z → Lle is (Lmax is x y) z.
  Proof .
    intros x y z <- <-.
    set (w := Lmax _ (Lmin _ x z) (Lmin _ y z)).
    assert (c : z = (Lmax is w z)).
    - unfold w. rewrite isassoc_Lmax, (iscomm_Lmax _ (Lmin _ y z) z), (iscomm_Lmin _ y z), Lmax_absorb, iscomm_Lmax, iscomm_Lmin, Lmax_absorb. reflexivity.
    - rewrite c. use (Lmin_absorb is).
  Defined.

  Definition prod_bilattices_are_interlaced : is_interlaced make_prod_bilattice .
  Proof.
    unfold is_interlaced; intros [x1 x2] [y1 y2] [z1 z2]; do 3 (try use make_dirprod); intro H; use dirprod_paths; unfold make_prod_bilattice,mklattice,tmin,tmax,kmin,kmax,meet in H; cbn in H; cbn; set (H1 := maponpaths dirprod_pr1 H); cbn in H1; set (H2 := maponpaths dirprod_pr2 H); cbn in H2.
    - rewrite (iscomm_Lmin l1 x1 z1), isassoc_Lmin, <- (isassoc_Lmin l1 x1 y1 z1), H1, (iscomm_Lmin l1 x1 z1), <- isassoc_Lmin, Lmin_id; reflexivity .
    - use Lmax_ge_eq_l; use Lmin_ge_case.
      -- use (istrans_Lge l2 x2 y2 (Lmin l2 y2 z2)).
         --- rewrite <- H2; exact (Lmax_ge_r l2 x2 y2).
         --- exact (Lmin_ge_l l2 y2 z2).
      -- exact (Lmin_ge_r l2 y2 z2).
    - use Lmin_ge_eq_l. use Lmax_le_case_.
      -- use (istrans_Lle l1 x1 y1 (Lmax l1 y1 z1)).
         --- rewrite <- H1. exact (Lmin_le_r l1 x1 y1).
         --- exact (Lmax_ge_l l1 y1 z1).
      -- exact (Lmax_le_r l1 y1 z1).
    - rewrite (iscomm_Lmax l2 x2 z2), (isassoc_Lmax), <- (isassoc_Lmax l2 x2 y2 z2), H2, (iscomm_Lmax l2 x2 z2), <- isassoc_Lmax, Lmax_id. reflexivity.
    - rewrite (iscomm_Lmin l1 x1 z1), isassoc_Lmin, <- (isassoc_Lmin l1 x1 y1 z1), H1, (iscomm_Lmin l1 x1 z1), <- isassoc_Lmin, Lmin_id; reflexivity .
    - use Lmin_ge_eq_l. use Lmax_le_case_.
      -- use (istrans_Lle l2 x2 y2 (Lmax l2 y2 z2)).
         --- rewrite <- H2. exact (Lmin_le_r l2 x2 y2).
         --- exact (Lmax_ge_l l2 y2 z2).
      -- exact (Lmax_le_r l2 y2 z2).
    - use Lmin_ge_eq_l. use Lmax_le_case_.
      -- use (istrans_Lle l1 x1 y1 (Lmax l1 y1 z1)).
         --- rewrite <- H1. exact (Lmin_le_r l1 x1 y1).
         --- exact (Lmax_ge_l l1 y1 z1).
      -- exact (Lmax_le_r l1 y1 z1).
    - rewrite (iscomm_Lmin l2 x2 z2), isassoc_Lmin, <- (isassoc_Lmin l2 x2 y2 z2), H2, (iscomm_Lmin l2 x2 z2), <- isassoc_Lmin, Lmin_id; reflexivity .
  Defined.

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
    unfold bounded_latticeop, islunit; use make_dirprod; intro x; use dirprod_paths; [use islunit_Lmax_Lbot | use islunit_Lmin_Ltop | use islunit_Lmin_Ltop | use islunit_Lmax_Lbot].
  Defined.

  Definition bounded_latticeop_prod_k : bounded_latticeop (mklattice (latticeop_prod_k bl1 bl2)) kbot ktop .
  Proof.
    unfold bounded_latticeop, islunit; use make_dirprod; intro x; use dirprod_paths; [use islunit_Lmax_Lbot | use islunit_Lmax_Lbot | use islunit_Lmin_Ltop | use islunit_Lmin_Ltop].
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
    unfold lattice; exists AND,  OR;
      unfold latticeop; repeat apply make_dirprod;
        try (unfold isassoc; intros a b c; induction a, b, c; trivial);
        try (unfold iscomm; intros a b; induction a, b; trivial);
        try (intros a b; induction a, b; trivial) .
  Defined.

  Definition bool_boundedlattice : bounded_lattice boolset .
  Proof.
    unfold bounded_lattice; exists bool_lattice, false, true;
      unfold bounded_latticeop, islunit; apply make_dirprod; unfold bool_lattice, Lmax; trivial .
  Defined.

  Definition FOUR := make_bounded_prod_bilattice bool_boundedlattice bool_boundedlattice .

  Definition is_distributive_FOUR : is_distributive_bilattice FOUR .
  Proof.
    unfold is_distributive_bilattice; unfold distributivity; repeat apply make_dirprod; intros [x1 x2] [y1 y2] [z1 z2]; induction x1, x2, y1, y2, z1, z2; trivial.
  Defined.
End bilattice_FOUR.
