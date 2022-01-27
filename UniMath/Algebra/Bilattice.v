Require Import UniMath.Algebra.Lattice.

Section bilattices .
  Definition bilattice (X : hSet) := lattice X × lattice X .

  Definition make_bilattice {X : hSet} (tLattice kLattice: lattice X) : bilattice X := tLattice,, kLattice.

  Definition tlattice {X : hSet} (b : bilattice X) : lattice X := pr1 b .
  Definition klattice {X : hSet} (b : bilattice X) : lattice X := pr2 b .

  Definition dual_lattice {X : hSet} (l : lattice X) : lattice X := mklattice (((isassoc_Lmax l),, (iscomm_Lmax l)),, ((isassoc_Lmin l),,(iscomm_Lmin l)),,(Lmax_absorb l),,(Lmin_absorb l)).

  Definition dual_bilattice {X : hSet} (b : bilattice X) := make_bilattice (klattice b)  (tlattice b) .
  Definition t_opp_bilattice {X : hSet} (b : bilattice X) := make_bilattice (dual_lattice (tlattice b)) (klattice b) .
  Definition k_opp_bilattice {X : hSet} (b : bilattice X) := dual_bilattice (t_opp_bilattice (dual_bilattice b)).
  Definition opp_bilattice {X : hSet} (b : bilattice X) := make_bilattice (dual_lattice (tlattice b)) (dual_lattice (klattice b)) .

  Definition meet {X : hSet} (b : bilattice X) : binop X := Lmin (tlattice b) .
  Definition join {X: hSet} (b : bilattice X) : binop X := Lmax (tlattice b) .
  Definition consensus {X : hSet} (b : bilattice X) : binop X := Lmin (klattice b) .
  Definition gullibility {X : hSet} (b : bilattice X) : binop X := Lmax (klattice b) .

  Definition isassoc_consensus {X : hSet} (b : bilattice X) : isassoc (consensus b) := isassoc_Lmin (klattice b) .
  Definition isassoc_join {X : hSet} (b : bilattice X) : isassoc (join b) := isassoc_Lmax (tlattice b) .
  Definition iscomm_consensus {X : hSet} (b : bilattice X) : iscomm (consensus b) := iscomm_Lmin (klattice b) .
  Definition iscomm_gullibility {X : hSet} (b : bilattice X) : iscomm (gullibility b) := iscomm_Lmax (klattice b) .
  Definition iscomm_meet {X : hSet} (b : bilattice X) : iscomm (meet b) := iscomm_Lmin (tlattice b) .
  Definition iscomm_join {X : hSet} (b : bilattice X) : iscomm (join b) := iscomm_Lmax (tlattice b) .

  Definition tle {X : hSet} (b : bilattice X) : hrel X := Lle (tlattice b).
  Definition kle {X : hSet} (b : bilattice X) : hrel X := Lle (klattice b).
  Definition tge {X : hSet} (b : bilattice X) : hrel X := Lge (tlattice b).
  Definition kge {X : hSet} (b : bilattice X) : hrel X := Lge (klattice b).

  Definition istrans_tle {X : hSet} (b : bilattice X) : istrans (tle b) := istrans_Lle (tlattice b).
  Definition istrans_kle {X : hSet} (b : bilattice X) : istrans (kle b) := istrans_Lle (klattice b).
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

  Definition interlacing {X : hSet} (op : binop X) (R : hrel X) :=
    ∏ x y z : X, R x y -> R (op x z) (op y z).

  Definition is_interlaced {X : hSet} (b : bilattice X) : UU :=
    interlacing (consensus b) (tle b)
                ×
                interlacing (gullibility b) (tle b)
                ×
                interlacing (meet b) (kle b)
                ×
                interlacing (join b) (kle b).

  Definition interlaced_bilattice (X : hSet) :=
    ∑ b : bilattice X,  is_interlaced b.

  Definition make_interlaced_bilattice {X : hSet} {b : bilattice X} (is : is_interlaced b) : interlaced_bilattice X := b,,is.

  Definition interlaced_bilattice_to_bilattice {X : hSet} (b: interlaced_bilattice X) : bilattice X := pr1 b.
  Coercion interlaced_bilattice_to_bilattice : interlaced_bilattice >-> bilattice .

  Definition dual_bilattice_is_interlaced {X : hSet} (b : interlaced_bilattice X) : is_interlaced (dual_bilattice b).
  Proof.
    destruct b as [? [? [? [? ?]]]] . do 3 (try split); assumption .
  Defined.

  Definition opp_bilattice_is_interlaced {X : hSet} (b : interlaced_bilattice X) : is_interlaced (opp_bilattice b).
  Proof.
    destruct b as [? [i1 [i2 [i3 i4]]]].
    do 3 (try split); intros ? ? ? H;
    [set (i := i2) | set (i := i1) | set (i := i4) | set (i := i3)];
    use (Lmax_le_eq_l _ _ _ (i _ _ _ (Lmax_le_eq_l _ _ _ H))).
  Defined.

  Definition interlacing_consensus_t {X : hSet} (b : interlaced_bilattice X) : interlacing (consensus b) (tle b) := pr1 (pr2 b) .
  Definition interlacing_gullibility_t {X : hSet} (b : interlaced_bilattice X) : interlacing (gullibility b) (tle b):= pr1 (pr2 (pr2 b)) .
  Definition interlacing_meet_k {X : hSet} (b : interlaced_bilattice X) :  interlacing (meet b) (kle b) := pr1 (pr2 (pr2 (pr2 b))) .
  Definition interlacing_join_k {X : hSet} (b : interlaced_bilattice X) :  interlacing (join b) (kle b) := pr2 (pr2 (pr2 (pr2 b))) .

  Definition iterated_interlacing {X : hSet} {op : binop X} {R : hrel X} (i : interlacing op R) (a : istrans R) (c : iscomm op) {x y z w : X} (p : R x y) (q : R z w) : R (op x z) (op y w).
  Proof.
    use (a (op x z) (op y z)).
    - use i. exact p.
    - rewrite (c y z), (c y w). use i . exact q.
  Defined.

End interlaced_bilattices.

Section distributive_bilattices.

  Definition is_distributive_lattice {X : hSet} (l : lattice X) :=
    (isldistr (Lmin l) (Lmax l)) × isldistr (Lmax l) (Lmin l) .

  Definition is_distributive_bilattice {X : hSet} (b : bilattice X) :=
              is_distributive_lattice (klattice b)
                × is_distributive_lattice (tlattice b)
                × isldistr (consensus b) (meet b)
                × isldistr (meet b) (consensus b)
                × isldistr (consensus b) (join b)
                × isldistr (join b) (consensus b)
                × isldistr (gullibility b) (meet b)
                × isldistr (meet b) (gullibility b)
                × isldistr (gullibility b) (join b)
                × isldistr (join b) (gullibility b)
  .
  Definition distributive_bilattice (X : hSet) :=
    ∑ b : bilattice X, is_distributive_bilattice b.

  Definition distributive_bilattices_to_bilattices {X : hSet} (b : distributive_bilattice X) : bilattice X := pr1 b.

  Coercion distributive_bilattices_to_bilattices : distributive_bilattice >-> bilattice .

  Definition distributive_consensus_gullibility {X : hSet} (b : distributive_bilattice X) : isldistr (consensus b) (gullibility b) := pr1 (pr1 (pr2 b)) .
  Definition distributive_gullibility_consensus {X : hSet} (b : distributive_bilattice X) : isldistr (gullibility b) (consensus b) := pr2 (pr1 (pr2 b)) .
  Definition distributive_meet_join {X : hSet} (b : distributive_bilattice X) : isldistr (meet b) (join b) := pr1 (pr1 (pr2 (pr2 b))) .
  Definition distributive_join_meet {X : hSet} (b : distributive_bilattice X) : isldistr (join b) (meet b) := pr2 (pr1 (pr2 (pr2 b))) .
  Definition distributive_consensus_meet {X : hSet} (b : distributive_bilattice X) : isldistr (consensus b) (meet b) := pr1 (pr2 (pr2 (pr2 b))) .
  Definition distributive_meet_consensus {X : hSet} (b : distributive_bilattice X) : isldistr (meet b) (consensus b) := pr1 (pr2 (pr2 (pr2 (pr2 b)))) .
  Definition distributive_consensus_join {X : hSet} (b : distributive_bilattice X) : isldistr (consensus b) (join b) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 b))))) .
  Definition distributive_join_consensus {X : hSet} (b : distributive_bilattice X) : isldistr (join b) (consensus b) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 b)))))) .
  Definition distributive_gullibility_meet {X : hSet} (b : distributive_bilattice X) : isldistr (gullibility b) (meet b) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 b))))))) .
  Definition distributive_meet_gullibility {X : hSet} (b : distributive_bilattice X) : isldistr (meet b) (gullibility b) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 b)))))))) .
  Definition distributive_gullibility_join {X : hSet} (b : distributive_bilattice X) : isldistr (gullibility b) (join b) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 b))))))))) .
  Definition distributive_join_gullibility {X : hSet} (b : distributive_bilattice X) : isldistr (join b) (gullibility b) := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 b))))))))) .


  Definition make_distributive_bilattice {X : hSet} {b : bilattice X} (is : is_distributive_bilattice b) : distributive_bilattice X := b,,is .

  Theorem distributive_bilattices_are_interlaced_bilattices {X : hSet} (b : distributive_bilattice X) : is_interlaced b .
  Proof.
    repeat split; intros x y z H.
    - rewrite (iscomm_consensus _ x z), (iscomm_consensus _ y z).
      set(d := distributive_meet_consensus b x y z). unfold meet in d. cbn.
      rewrite <- d,  H. reflexivity.
    - rewrite (iscomm_gullibility _ x z), (iscomm_gullibility _ y z).
      set (d := distributive_meet_gullibility b x y z). unfold meet in d. cbn.
      rewrite <- d,  H; reflexivity.
    - rewrite (iscomm_meet _ x z), (iscomm_meet _ y z).
      set (d := (distributive_consensus_meet b x y z)). unfold consensus in d. cbn.
      rewrite <- d , H;  reflexivity.
    - rewrite (iscomm_join _ x z), (iscomm_join _ y z).
      set (d := distributive_consensus_join b x y z). unfold consensus in d. cbn.
      rewrite <- d, H; reflexivity .
  Defined.

  Definition distributive_bilattices_to_interlaced_bilattices {X : hSet} (b : distributive_bilattice X) : interlaced_bilattice X :=
    make_interlaced_bilattice (distributive_bilattices_are_interlaced_bilattices b).

  Coercion distributive_bilattices_to_interlaced_bilattices : distributive_bilattice >-> interlaced_bilattice .
End distributive_bilattices.

Section prod_bilattices .
  Definition prod_bilattice_carrier (X1 X2 : hSet) := setdirprod X1 X2 .

  Definition tmin {X1 X2 : hSet} (l1 : lattice X1) (l2 : lattice X2) : binop (prod_bilattice_carrier X1 X2) :=
    λ x y, (((Lmin l1) (pr1 x) (pr1 y)),, (Lmax l2) (pr2 x) (pr2 y)) .
  Definition tmax  {X1 X2 : hSet} (l1 : lattice X1) (l2 : lattice X2) : binop (prod_bilattice_carrier X1 X2) :=
    λ x y, (((Lmax l1) (pr1 x) (pr1 y)),, (Lmin l2) (pr2 x) (pr2 y)) .
  Definition kmin  {X1 X2 : hSet} (l1 : lattice X1) (l2 : lattice X2) : binop (prod_bilattice_carrier X1 X2) :=
    λ x y, (((Lmin l1) (pr1 x) (pr1 y)),, (Lmin l2) (pr2 x) (pr2 y)) .
  Definition kmax  {X1 X2 : hSet} (l1 : lattice X1) (l2 : lattice X2) : binop (prod_bilattice_carrier X1 X2) :=
    λ x y, (((Lmax l1) (pr1 x) (pr1 y)),, (Lmax l2) (pr2 x) (pr2 y)) .

  Definition latticeop_prod_t {X1 X2 : hSet} (l1 : lattice X1) (l2 : lattice X2) : latticeop (tmin l1 l2) (tmax l1 l2) .
  Proof .
    do 4 (try use make_dirprod).
    - intros a b c; induction a, b, c. use dirprod_paths; [use isassoc_Lmin | use isassoc_Lmax].
    - intros a b; induction a, b. use dirprod_paths; [use iscomm_Lmin | use iscomm_Lmax] .
    - intros a b c; induction a, b, c. use dirprod_paths; [use isassoc_Lmax | use isassoc_Lmin] .
    - intros a b; induction a, b. use dirprod_paths; [use iscomm_Lmax | use iscomm_Lmin ].
    - intros a b; induction a, b. use dirprod_paths; [use Lmin_absorb | use Lmax_absorb ].
    - intros a b; induction a, b. use dirprod_paths; [use Lmax_absorb | use Lmin_absorb] .
  Defined .

  Definition latticeop_prod_k {X1 X2 : hSet} (l1 : lattice X1) (l2 : lattice X2) : latticeop (kmin l1 l2) (kmax l1 l2) .
  Proof .
    do 4 (try use make_dirprod).
    - intros a b c; induction a, b, c. use dirprod_paths; use isassoc_Lmin.
    - intros a b; induction a, b. use dirprod_paths; use iscomm_Lmin.
    - intros a b c; induction a, b, c. use dirprod_paths; use isassoc_Lmax .
    - intros a b; induction a, b. use dirprod_paths; use iscomm_Lmax .
    - intros a b; induction a, b. use dirprod_paths; use Lmin_absorb .
    - intros a b; induction a, b. use dirprod_paths; use Lmax_absorb .
  Defined .

  Definition make_prod_bilattice {X1 X2 : hSet} (l1 : lattice X1) (l2 : lattice X2) := make_bilattice (mklattice (latticeop_prod_t l1 l2)) (mklattice (latticeop_prod_k l1 l2)) .
End prod_bilattices .

Section bounded_prod_bilattices.
  Definition tbot {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : (prod_bilattice_carrier X1 X2) :=
    Lbot bl1,, Ltop bl2 .
  Definition ttop  {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : (prod_bilattice_carrier X1 X2) :=
    Ltop bl1,, Lbot bl2 .
  Definition kbot {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : (prod_bilattice_carrier X1 X2):=
    Lbot bl1,, Lbot bl2 .
  Definition ktop {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : (prod_bilattice_carrier X1 X2) :=  Ltop bl1,, Ltop bl2.

  Definition bounded_latticeop_prod_t  {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : bounded_latticeop (mklattice (latticeop_prod_t bl1 bl2)) (tbot bl1 bl2) (ttop bl1 bl2) .
  Proof.
    use make_dirprod; intro; use dirprod_paths; [use islunit_Lmax_Lbot | use islunit_Lmin_Ltop | use islunit_Lmin_Ltop | use islunit_Lmax_Lbot].
  Defined.

  Definition bounded_latticeop_prod_k  {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : bounded_latticeop (mklattice (latticeop_prod_k bl1 bl2)) (kbot bl1 bl2) (ktop bl1 bl2) .
  Proof.
    use make_dirprod; intro; use dirprod_paths; [use islunit_Lmax_Lbot | use islunit_Lmax_Lbot | use islunit_Lmin_Ltop | use islunit_Lmin_Ltop].
  Defined.

  Definition make_bounded_prod_bilattice  {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) := make_bounded_bilattice (mkbounded_lattice (bounded_latticeop_prod_t bl1 bl2)) (mkbounded_lattice (bounded_latticeop_prod_k bl1 bl2)) .

End bounded_prod_bilattices.

Section representation_theorems.
  Definition prod_bilattices_are_interlaced {X1 X2 : hSet} {l1 : lattice X1} {l2 : lattice X2} : is_interlaced (make_prod_bilattice l1 l2) .
  Proof.
    do 3 (try use make_dirprod); intros [x1 x2] [y1 y2] [z1 z2] H; use dirprod_paths; cbn in H; set (H1 := maponpaths dirprod_pr1 H); cbn in H1; set (H2 := maponpaths dirprod_pr2 H); cbn in H2; cbn.
    - rewrite (iscomm_Lmin _ x1 z1), isassoc_Lmin, <- (isassoc_Lmin _ x1 y1 z1), H1, (iscomm_Lmin _ x1 z1), <- isassoc_Lmin, Lmin_id; reflexivity .
    - use Lmax_ge_eq_l; use Lmin_ge_case.
      -- use (istrans_Lge _ x2 y2 (Lmin _ y2 z2)).
         --- rewrite <- H2; exact (Lmax_ge_r _ x2 y2).
         --- exact (Lmin_ge_l _ y2 z2).
      -- exact (Lmin_ge_r _ y2 z2).
    - use Lmin_ge_eq_l; use Lmax_ge_case.
      -- use (istrans_Lle _ x1 y1 (Lmax _ y1 z1)).
         --- rewrite <- H1; exact (Lmin_ge_r _ x1 y1).
         --- exact (Lmax_ge_l _ y1 z1).
      -- exact (Lmax_ge_r _ y1 z1).
    - rewrite (iscomm_Lmax _ x2 z2), (isassoc_Lmax), <- (isassoc_Lmax _ x2 y2 z2), H2, (iscomm_Lmax _ x2 z2), <- isassoc_Lmax, Lmax_id. reflexivity.
    - rewrite (iscomm_Lmin _ x1 z1), isassoc_Lmin, <- (isassoc_Lmin _ x1 y1 z1), H1, (iscomm_Lmin _ x1 z1), <- isassoc_Lmin, Lmin_id; reflexivity .
    - use Lmin_ge_eq_l. use Lmax_le_case.
      -- use (istrans_Lle _ x2 y2 (Lmax _ y2 z2)).
         --- rewrite <- H2. exact (Lmin_le_r _ x2 y2).
         --- exact (Lmax_ge_l _ y2 z2).
      -- exact (Lmax_le_r _ y2 z2).
    - use Lmin_ge_eq_l; use Lmax_ge_case.
      -- use (istrans_Lle _ x1 y1 (Lmax _ y1 z1)).
         --- rewrite <- H1; exact (Lmin_ge_r _ x1 y1).
         --- exact (Lmax_ge_l _ y1 z1).
      -- exact (Lmax_ge_r _ y1 z1).
    - rewrite (iscomm_Lmin _ x2 z2), (isassoc_Lmin), <- (isassoc_Lmin _ x2 y2 z2), H2, (iscomm_Lmin _ x2 z2), <- isassoc_Lmin, Lmin_id. reflexivity.
  Defined.

  Definition leftRel {X : hSet} (b : interlaced_bilattice X) : hrel X := λ x y : X, eqset (join b x y) (consensus b x y)  .
  Definition isEq_leftRel {X : hSet} (b : interlaced_bilattice X) : iseqrel (leftRel b).
  Proof.
    assert (property1 : ∏ (b : interlaced_bilattice X) (x y : X) , (∑ r : X, tle b x r × kle b r y) -> kle b x (meet b y x)).
    {
      intros ? x y [? [p1 p2]].
      set (w := (meet _ y x)); rewrite <- (Lmin_le_eq_r _ _ _ p1).
      use (interlacing_meet_k _ _ _ _ p2).
    }
    assert (property1_dual : ∏ (b : interlaced_bilattice X) (x y : X) , (∑ r : X, kle b x r × tle b r y) -> tle b x (consensus b y x)).
    {
      intro b'.
      use (property1 (make_interlaced_bilattice (dual_bilattice_is_interlaced b'))).
    }
    assert (property1_op : ∏ (b : interlaced_bilattice X) (x y : X) , (∑ r : X, tle b r x × kle b y r) -> kle b (join b y x) x).
    {
      intros b' ? ? [? [p1 p2]].
      set (bop := make_interlaced_bilattice (opp_bilattice_is_interlaced b')).
      set (H := property1 bop _ _ (_,,(Lmax_le_eq_l _ _ _ p1),, (Lmax_le_eq_l _ _ _ p2))).
      use (Lmax_le_eq_l _ _ _ H).
    }
    assert (property2 : ∏ (b : interlaced_bilattice X) (x y : X) , (∑ r : X, tle b x r × kle b r y) -> tle b x (consensus b y x)).
    {
      intros b' ? ? [? [p1 p2]].
      set (pp := property1 _ _ _ (_,,p1,,p2)).
      rewrite (iscomm_meet) in pp.
      use (property1_dual _ _ _ (_,, pp,, Lmin_le_r (tlattice b') _ _)).
    }
    assert (property2_dual : ∏ (b : interlaced_bilattice X) (x y : X) , (∑ r : X, kle b x r × tle b r y) -> kle b x (meet b y x)).
    {
      intro b'.
      use (property2 (make_interlaced_bilattice (dual_bilattice_is_interlaced b'))).
    }

    unfold iseqrel, ispreorder, iscomm, leftRel, istrans, isrefl, isantisymm.
    do 2 (try split).
    - intros x y z H1 H2. use (isantisymm_Lle (tlattice b)).
      -- use Lmax_le_case.
         --- assert (r1 : tle b x (consensus b (consensus b x y) z) ).
             {
               use (istrans_tle _  x (consensus b x y)).
               - rewrite <- H1. apply (Lmax_le_l (tlattice _)).
               - rewrite (isassoc_consensus _ x y z), (iscomm_consensus _ x y), <- H2, (iscomm_consensus _ x).
                 use interlacing_consensus_t. use Lmin_absorb .
             }
             set (r2 := Lmin_le_r _ _ _ : kle b (consensus b (consensus b x y) z) z ).
             rewrite iscomm_consensus. use (property2 _ _ _ (_,,r1,,r2)).
         --- set (r1 := Lmax_le_r _ _ _  : tle b z (join b (join b x y) z) ).
             assert (r2 : kle b (join b (join b x y) z) x).
             {
               use (istrans_kle _ (join _ (join b x y) z) (join b x y)).
               - rewrite (isassoc_join _ x y z), (iscomm_join _ x y), H2, (iscomm_join _ x).
                 use interlacing_join_k. use Lmin_le_l.
               - rewrite H1. use Lmin_le_l.
             }
             use (property2 _ _ _ (_,,r1,,r2)).
      -- rewrite <- (Lmin_id (klattice b) (join _ x z)).
         use (iterated_interlacing (interlacing_consensus_t _) (istrans_Lle _) (iscomm_Lmin _) (Lmax_le_l _ _ _)  (Lmax_le_r _ _ _)).
    - intro. unfold consensus. rewrite Lmin_id. unfold join. rewrite Lmax_id. reflexivity.
    - intros ? ? H. rewrite iscomm_join, iscomm_consensus. exact H.
  Defined.

(*

  Definition rightRel {X : hSet} (b : interlaced_bilattice X) : hrel X := λ x y : X, eqset (meet b x y) (consensus b x y)  .

  Print setquotfun2.

  Definition leftLattice {X : hSet} (b : interlaced_bilattice X) : lattice (setquotinset (leftRel b)).
  Proof.
    unfold lattice. exists (setquotfun2 (leftRel b) (leftRel b) (consensus b)). (setquotfun2 X X leftRel leftRel (gullibility b)).

  Defined.


  Definition interlaced_bilattices_are_prod {X : hSet} (b : interlaced_bilattice X) : ∑ (X1 X2 : hSet) (l1 : lattice X1) (l2 : lattice X2) (p : X = prod_bilattice_carrier X1 X2),  make_prod_bilattice l1 l2 = transportf interlaced_bilattice p b .
  Proof.
    Search setquot.
    exists (setquotinset (leftRel b)), (setquotinset (rightRel b)), make_lattice.


  Defined.
*)
End representation_theorems.

Section bilattice_FOUR.
  Definition AND : binop boolset :=
    λ b1 b2,
    match b1 with true => b2 | false => b1 end.

  Definition OR : binop boolset :=
    λ b1 b2,
    match b1 with true => b1 | false => b2 end.

  Definition bool_lattice : lattice boolset .
  Proof .
    exists AND, OR.
    repeat apply make_dirprod;
        try (intros a b c; induction a, b, c; trivial);
        try (intros a b; induction a, b; trivial) .
  Defined.

  Definition bool_boundedlattice : bounded_lattice boolset .
  Proof.
    exists bool_lattice, false, true.
    unfold bounded_latticeop, islunit.
    apply make_dirprod; trivial .
  Defined.

  Definition FOUR := make_bounded_prod_bilattice bool_boundedlattice bool_boundedlattice .

  Check prod_bilattices_are_interlaced : is_interlaced FOUR .

  Definition is_distributive_FOUR : is_distributive_bilattice FOUR .
  Proof.
    repeat apply make_dirprod; intros [x1 x2] [y1 y2] [z1 z2]; induction x1, x2, y1, y2, z1, z2; trivial.
  Defined.
End bilattice_FOUR.
