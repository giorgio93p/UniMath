Require Import UniMath.Algebra.Lattice.
Require Import UniMath.MoreFoundations.Subtypes.
Require Import UniMath.MoreFoundations.Equivalences.

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
  Definition isassoc_meet {X : hSet} (b : bilattice X) : isassoc (meet b) := isassoc_Lmin (tlattice b) .
  Definition iscomm_consensus {X : hSet} (b : bilattice X) : iscomm (consensus b) := iscomm_Lmin (klattice b) .
  Definition iscomm_gullibility {X : hSet} (b : bilattice X) : iscomm (gullibility b) := iscomm_Lmax (klattice b) .
  Definition iscomm_meet {X : hSet} (b : bilattice X) : iscomm (meet b) := iscomm_Lmin (tlattice b) .
  Definition iscomm_join {X : hSet} (b : bilattice X) : iscomm (join b) := iscomm_Lmax (tlattice b) .
  Definition join_id {X : hSet} (b : bilattice X) (x : X) : join b x x = x := Lmax_id (tlattice b) x.
  Definition meet_id {X : hSet} (b : bilattice X) (x : X) : meet b x x = x := Lmin_id (tlattice b) x.

  Definition consensus_gullibility_absorb {X : hSet} (b : bilattice X) (x y : X) : consensus b x (gullibility b x y) = x :=
    Lmin_absorb (klattice b) x y.
  Definition gullibility_consensus_absorb {X : hSet} (b : bilattice X) (x y : X) : gullibility b x (consensus b x y) = x :=
    Lmax_absorb (klattice b) x y.
  Definition meet_join_absorb {X : hSet} (b : bilattice X) (x y : X) : meet b x (join b x y) = x :=
    Lmin_absorb (tlattice b) x y.
    Definition join_meet_absorb {X : hSet} (b : bilattice X) (x y : X) : join b x (meet b x y) = x :=
    Lmax_absorb (tlattice b) x y.


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

  Definition interlacing_consensus_t {X : hSet} (b : interlaced_bilattice X) : interlacing (consensus b) (tle b) := pr1 (pr2 b) .
  Definition interlacing_gullibility_t {X : hSet} (b : interlaced_bilattice X) : interlacing (gullibility b) (tle b):= pr1 (pr2 (pr2 b)) .
  Definition interlacing_meet_k {X : hSet} (b : interlaced_bilattice X) :  interlacing (meet b) (kle b) := pr1 (pr2 (pr2 (pr2 b))) .
  Definition interlacing_join_k {X : hSet} (b : interlaced_bilattice X) :  interlacing (join b) (kle b) := pr2 (pr2 (pr2 (pr2 b))) .

  Definition double_interlacing {X : hSet} {op : binop X} {R : hrel X} (i : interlacing op R) (a : istrans R) (c : iscomm op) {x y z w : X} (p : R x y) (q : R z w) : R (op x z) (op y w).
  Proof.
    use (a (op x z) (op y z)).
    - use i. exact p.
    - rewrite (c y z), (c y w). use i . exact q.
  Defined.

  Definition double_interlacing_gullibility_t {X : hSet} {b : interlaced_bilattice X} {x y z w : X} (p : tle b x y) (q : tle b z w) : tle b (gullibility b x z) (gullibility b y w) := double_interlacing (interlacing_gullibility_t _) (istrans_Lle (tlattice _)) (iscomm_Lmax (klattice _)) p q.
  Definition double_interlacing_consensus_t {X : hSet} {b : interlaced_bilattice X} {x y z w : X} (p : tle b x y) (q : tle b z w) : tle b (consensus b x z) (consensus b y w) := double_interlacing (interlacing_consensus_t _) (istrans_Lle (tlattice _)) (iscomm_Lmin (klattice _)) p q.
  Definition double_interlacing_meet_k {X : hSet} {b : interlaced_bilattice X} {x y z w : X} (p : kle b x y) (q : kle b z w) : kle b (meet b x z) (meet b y w) := double_interlacing (interlacing_meet_k _) (istrans_Lle (klattice _)) (iscomm_Lmin (tlattice _)) p q.
  Definition double_interlacing_join_k {X : hSet} {b : interlaced_bilattice X} {x y z w : X} (p : kle b x y) (q : kle b z w) : kle b (join b x z) (join b y w) := double_interlacing (interlacing_join_k _) (istrans_Lle (klattice _)) (iscomm_Lmax (tlattice _)) p q.

  Definition top_interlacing_gullibility_t {X : hSet} {b : interlaced_bilattice X} {x y z : X} (p : tle b x z) (q : tle b y z) : tle b (gullibility b x y) z.
  Proof.
    rewrite <- (Lmax_id (klattice b) z).
    use (double_interlacing_gullibility_t p q).
  Defined.
  Definition top_interlacing_consensus_t {X : hSet} {b : interlaced_bilattice X} {x y z : X} (p : tle b x z) (q : tle b y z) : tle b (consensus b x y) z.
  Proof.
    rewrite <- (Lmin_id (klattice b) z).
    use (double_interlacing_consensus_t p q).
  Defined.
  Definition top_interlacing_join_k {X : hSet} {b : interlaced_bilattice X} {x y z : X} (p : kle b x z) (q : kle b y z) : kle b (join b x y) z.
  Proof.
    rewrite <- (Lmax_id (tlattice b) z).
    use (double_interlacing_join_k p q).
  Defined.
  Definition top_interlacing_meet_k {X : hSet} {b : interlaced_bilattice X} {x y z : X} (p : kle b x z) (q : kle b y z) : kle b (meet b x y) z.
  Proof.
    rewrite <- (Lmin_id (tlattice b) z).
    use (double_interlacing_meet_k p q).
  Defined.

  Definition bottom_interlacing_join_k {X : hSet} {b : interlaced_bilattice X} {x y z : X} (p : kle b z x) (q : kle b z y) : kle b z (join b x y).
  Proof.
    rewrite <- (Lmax_id (tlattice b) z).
    use (double_interlacing_join_k p q).
  Defined.
  Definition bottom_interlacing_meet_k {X : hSet} {b : interlaced_bilattice X} {x y z : X} (p : kle b z x) (q : kle b z y) : kle b z (meet b x y).
  Proof.
    rewrite <- (Lmin_id (tlattice b) z).
    use (double_interlacing_meet_k p q).
  Defined.
  Definition bottom_interlacing_gullibility_t {X : hSet} {b : interlaced_bilattice X} {x y z : X} (p : tle b z x) (q : tle b z y) : tle b z (gullibility b x y).
  Proof.
    rewrite <- (Lmax_id (klattice b) z).
    use (double_interlacing_gullibility_t p q).
  Defined.
  Definition bottom_interlacing_consensus_t {X : hSet} {b : interlaced_bilattice X} {x y z : X} (p : tle b z x) (q : tle b z y) : tle b z (consensus b x y).
  Proof.
    rewrite <- (Lmin_id (klattice b) z).
    use (double_interlacing_consensus_t p q).
  Defined.

  Definition dual_bilattice_is_interlaced {X : hSet} (b : interlaced_bilattice X) : is_interlaced (dual_bilattice b).
  Proof.
    destruct b as [? [? [? [? ?]]]] . do 3 (try split); assumption .
  Defined.

  Definition opp_bilattice_is_interlaced {X : hSet} (b : interlaced_bilattice X) : is_interlaced (opp_bilattice b).
  Proof.
    do 3 (try split); intros ? ? ? H;
    [set (i := (interlacing_gullibility_t b)) | set (i := interlacing_consensus_t b) | set (i := interlacing_join_k b) | set (i := interlacing_meet_k b)];
    use (Lmax_le_eq_l _ _ _ (i _ _ _ (Lmax_le_eq_l _ _ _ H))).
  Defined.

  Definition t_opp_bilattice_is_interlaced {X : hSet} (b : interlaced_bilattice X) : is_interlaced (t_opp_bilattice b).
  Proof.
    do 3 (try split); intros ? ? ? H.
    - use (Lmax_le_eq_l _ _ _ (interlacing_consensus_t _ _ _ _ (Lmax_le_eq_l _ _ _ H))).
    - use (Lmax_le_eq_l _ _ _ (interlacing_gullibility_t _ _ _ _ (Lmax_le_eq_l _ _ _ H))).
    - use (interlacing_join_k _ _ _ _ H).
    - use (interlacing_meet_k _ _ _ _ H).
  Defined.

  Definition k_opp_bilattice_is_interlaced {X : hSet} (b : interlaced_bilattice X) : is_interlaced (k_opp_bilattice b).
  Proof.
    destruct (t_opp_bilattice_is_interlaced (make_interlaced_bilattice (dual_bilattice_is_interlaced b))) as [? [? [? ?]]].
    do 3 (try split); assumption.
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

  Definition prod_bilattice (X1 X2 : hSet) (l1 : lattice X1) (l2 : lattice X2) := (latticeop (tmin l1 l2) (tmax l1 l2)) × (latticeop (kmin l1 l2) (kmax l1 l2)).

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

  Definition make_prod_bilattice {X1 X2 : hSet} (l1 : lattice X1) (l2 : lattice X2) : prod_bilattice X1 X2 l1 l2 :=
    latticeop_prod_t l1 l2,,latticeop_prod_k l1 l2.

  Definition prod_bilattices_to_bilattices {X1 X2 : hSet} {l1 : lattice X1} {l2 : lattice X2} (b : prod_bilattice X1 X2 l1 l2) : bilattice (prod_bilattice_carrier X1 X2) :=  make_bilattice (mklattice (pr1 b)) (mklattice (pr2 b)) .

  Coercion prod_bilattices_to_bilattices : prod_bilattice >-> bilattice .
End prod_bilattices .

Section bounded_prod_bilattices.
  Definition tbot {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : (prod_bilattice_carrier X1 X2) :=
    Lbot bl1,, Ltop bl2 .
  Definition ttop  {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : (prod_bilattice_carrier X1 X2) :=
    Ltop bl1,, Lbot bl2 .
  Definition kbot {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : (prod_bilattice_carrier X1 X2):=
    Lbot bl1,, Lbot bl2 .
  Definition ktop {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : (prod_bilattice_carrier X1 X2) :=  Ltop bl1,, Ltop bl2.

  Definition bounded_prod_bilattice (X1 X2 : hSet) (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) :=
    bounded_latticeop (mklattice (latticeop_prod_t bl1 bl2)) (tbot bl1 bl2) (ttop bl1 bl2)
                      × bounded_latticeop (mklattice (latticeop_prod_k bl1 bl2)) (kbot bl1 bl2) (ktop bl1 bl2).

  Definition bounded_latticeop_prod_t  {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : bounded_latticeop (mklattice (latticeop_prod_t bl1 bl2)) (tbot bl1 bl2) (ttop bl1 bl2) .
  Proof.
    use make_dirprod; intro; use dirprod_paths; [use islunit_Lmax_Lbot | use islunit_Lmin_Ltop | use islunit_Lmin_Ltop | use islunit_Lmax_Lbot].
  Defined.

  Definition bounded_latticeop_prod_k  {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : bounded_latticeop (mklattice (latticeop_prod_k bl1 bl2)) (kbot bl1 bl2) (ktop bl1 bl2) .
  Proof.
    use make_dirprod; intro; use dirprod_paths; [use islunit_Lmax_Lbot | use islunit_Lmax_Lbot | use islunit_Lmin_Ltop | use islunit_Lmin_Ltop].
  Defined.

  Definition make_bounded_prod_bilattice  {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : bounded_prod_bilattice X1 X2 bl1 bl2 := bounded_latticeop_prod_t bl1 bl2,,bounded_latticeop_prod_k bl1 bl2 .

  Definition bounded_prod_bilattices_to_prod_bilattices {X1 X2 : hSet} {bl1 : bounded_lattice X1} {bl2 : bounded_lattice X2} (b : bounded_prod_bilattice X1 X2 bl1 bl2) : prod_bilattice X1 X2 bl1 bl2 := pr221 (mkbounded_lattice (pr1 b)),, pr221 (mkbounded_lattice (pr2 b)).

  Coercion bounded_prod_bilattices_to_prod_bilattices : bounded_prod_bilattice >-> prod_bilattice.

  Definition bounded_prod_bilattices_to_bounded_bilattices {X1 X2 : hSet} {l1 : bounded_lattice X1} {l2 : bounded_lattice X2} (b : bounded_prod_bilattice X1 X2 l1 l2) : bounded_bilattice (prod_bilattice_carrier X1 X2) :=  make_bounded_bilattice (mkbounded_lattice (pr1 b)) (mkbounded_lattice (pr2 b)) .

  Coercion bounded_prod_bilattices_to_bounded_bilattices : bounded_prod_bilattice >-> bounded_bilattice .
End bounded_prod_bilattices.

Section representation_theorems.
  Definition prod_bilattices_are_interlaced {X1 X2 : hSet} {l1 : lattice X1} {l2 : lattice X2} (b : prod_bilattice X1 X2 l1 l2) : is_interlaced b .
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

    Lemma property1 {X : hSet} : ∏ (b : interlaced_bilattice X) (x y : X) , (∑ r : X, tle b x r × kle b r y) -> kle b x (meet b y x).
    Proof.
      intros ? x y [? [p1 p2]].
      set (w := (meet _ y x)); rewrite <- (Lmin_le_eq_r _ _ _ p1).
      use (interlacing_meet_k _ _ _ _ p2).
    Defined.

    Lemma property1_dual {X:hSet}: ∏ (b : interlaced_bilattice X) (x y : X) , (∑ r : X, kle b x r × tle b r y) -> tle b x (consensus b y x).
    Proof.
      intro b'.
      use (property1 (make_interlaced_bilattice (dual_bilattice_is_interlaced b'))).
    Defined.

    Lemma property1_dual_opp_t {X:hSet}: ∏ (b : interlaced_bilattice X) (x y : X) , (∑ r : X, kle b x r × tle b y r) -> tle b (consensus b y x) x.
    Proof.
      intros ? x y [? [p1 p2]].
      set (w := (consensus _ y x)); rewrite <- (Lmin_le_eq_r _ _ _ p1).
      use (interlacing_consensus_t _ _ _ _ p2).
    Defined.

    Lemma property2 {X : hSet} : ∏ (b : interlaced_bilattice X) (x y : X) , (∑ r : X, tle b x r × kle b r y) -> tle b x (consensus b y x).
    Proof.
      intros b' ? ? [? [p1 p2]].
      set (pp := property1 _ _ _ (_,,p1,,p2)).
      rewrite (iscomm_meet) in pp.
      use (property1_dual _ _ _ (_,, pp,, Lmin_le_r (tlattice b') _ _)).
    Defined.

    Lemma property2_opp_t {X : hSet} : ∏ (b : interlaced_bilattice X) (x y : X), (∑ r : X, tle b r x × kle b r y) -> tle b (consensus b y x) x.
    Proof.
      intros b x y [r [p1 p2]].
      assert (p1' :  tle (make_interlaced_bilattice (t_opp_bilattice_is_interlaced b)) x r).
      {
        rewrite <- p1, iscomm_Lmin.
        use Lmax_absorb.
      }
      set (t := consensus b y x).
      assert (p : Lmax (tlattice b) t x = x).
      {
        rewrite iscomm_Lmax.
        exact (property2 (make_interlaced_bilattice (t_opp_bilattice_is_interlaced b)) x y (r,,p1',,p2)).
      }
      rewrite <- p.
      use Lmin_absorb.
    Defined.

  Definition leftRel {X : hSet} (b : interlaced_bilattice X) : hrel X := λ x y : X, eqset (join b x y) (consensus b x y)  .
  Definition isEq_leftRel {X : hSet} (b : interlaced_bilattice X) : iseqrel (leftRel b).
  Proof.
    assert (property1_op : ∏ (b : interlaced_bilattice X) (x y : X) , (∑ r : X, tle b r x × kle b y r) -> kle b (join b y x) x).
    {
      intros b' ? ? [? [p1 p2]].
      set (bop := make_interlaced_bilattice (opp_bilattice_is_interlaced b')).
      set (H := property1 bop _ _ (_,,(Lmax_le_eq_l _ _ _ p1),, (Lmax_le_eq_l _ _ _ p2))).
      use (Lmax_le_eq_l _ _ _ H).
    }
    assert (property2_dual : ∏ (b : interlaced_bilattice X) (x y : X) , (∑ r : X, kle b x r × tle b r y) -> kle b x (meet b y x)).
    {
      intro b'.
      use (property2 (make_interlaced_bilattice (dual_bilattice_is_interlaced b'))).
    }

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
      -- use (top_interlacing_consensus_t (Lmax_le_l _ x z) (Lmax_le_r _ x z)).
    - intro. unfold leftRel, consensus. rewrite Lmin_id. unfold join. rewrite Lmax_id. reflexivity.
    - intros ? ? H. unfold leftRel. rewrite iscomm_join, iscomm_consensus. exact H.
  Defined.

  Definition leftEq {X : hSet} (b : interlaced_bilattice X) : eqrel X := make_eqrel (leftRel b) (isEq_leftRel b).

  Definition rightRel {X : hSet} (b : interlaced_bilattice X) : hrel X := λ x y : X, eqset (meet b x y) (consensus b x y)  .

  Definition isEq_rightRel {X : hSet} (b : interlaced_bilattice X) : iseqrel (rightRel b) :=
    isEq_leftRel (make_interlaced_bilattice (t_opp_bilattice_is_interlaced b)).

  Definition rightEq {X : hSet} (b : interlaced_bilattice X) : eqrel X := make_eqrel (rightRel b) (isEq_rightRel b).

  Definition iscomp_consensus_leftRel {X : hSet} (b : interlaced_bilattice X) : iscomprelrelfun2 (leftEq b) (leftEq b) (consensus b).
  Proof.
    intros x y w z H1 H2.
    use (isantisymm_Lle (klattice b) (join _ (consensus _ x w) (consensus _ y z)) ((consensus _ (consensus _ x w) (consensus _ y z)))).
    - rewrite (isassoc_consensus _ x w (consensus _ y z)),
        (iscomm_consensus _ y z),
        <- (isassoc_consensus _ w z y),
        (iscomm_consensus _ (consensus _ w z) y),
        <- (isassoc_consensus _ x y (consensus _ w z)).
      use Lmin_le_case.
      -- rewrite <- H1.
         use (double_interlacing_join_k (Lmin_le_l _ x w) (Lmin_le_r _ z y)).
      -- rewrite <- H2.
         use (double_interlacing_join_k (Lmin_le_r _ x w) (Lmin_le_l _ z y)).
    - use (bottom_interlacing_join_k (Lmin_le_l _ (consensus _ x w) (consensus _ y z)) (Lmin_le_r _ (consensus _ x w) (consensus _ y z))).
  Defined.

  Definition iscomp_gullibility_leftRel {X : hSet} (b : interlaced_bilattice X) : iscomprelrelfun2 (leftEq b) (leftEq b) (gullibility b).
  Proof.
    intros x y w z H1 H2.
    use (isantisymm_Lle (tlattice b) (join _ (gullibility _ x w) (gullibility _ y z)) ((consensus _ (gullibility _ x w) (gullibility _ y z)))).
    - use Lmax_le_case.
      -- rewrite iscomm_consensus.
         use (property2 _ (gullibility _ x w) (gullibility _ y z)).
         exists (gullibility b (join b x y) (join b w z)).
         split.
         ---use (double_interlacing_gullibility_t (Lmax_le_l _ x y) (Lmax_le_l _ w z)).
         --- rewrite H1, H2.
             use Lmax_le_case.
             ---- use (istrans_Lle _ _ y _).
                  ----- use Lmin_le_r.
                  ----- use Lmax_le_l.
             ---- use (istrans_Lle _ _ z _).
                  ----- use Lmin_le_r.
                  ----- use Lmax_le_r.
      -- use (property2 _ (gullibility _ y z) (gullibility _ x w)).
         exists (gullibility b (join b x y) (join b w z)).
         split.
         --- use (double_interlacing_gullibility_t (Lmax_le_r _ _ _) (Lmax_le_r _ _ _)).
         --- rewrite H1, H2.
             use Lmax_le_case.
             ---- use (istrans_Lle _ _ x _).
                  ----- use Lmin_le_l.
                  ----- use Lmax_le_l.
             ---- use (istrans_Lle _ _ w _).
                  ----- use Lmin_le_l.
                  ----- use Lmax_le_r.
    - use (top_interlacing_consensus_t (Lmax_le_l _ _ _) (Lmax_le_r _ _ _)).
  Defined.

  Definition iscomp_consensus_rightRel {X : hSet} (b : interlaced_bilattice X) : iscomprelrelfun2 (rightEq b) (rightEq b) (consensus b) :=
    iscomp_consensus_leftRel (make_interlaced_bilattice (t_opp_bilattice_is_interlaced b)).
  Definition iscomp_gullibility_rightRel {X : hSet} (b : interlaced_bilattice X) : iscomprelrelfun2 (rightEq b) (rightEq b) (gullibility b) :=
    iscomp_gullibility_leftRel (make_interlaced_bilattice (t_opp_bilattice_is_interlaced b)).
  Definition iscomp_meet_rightRel {X : hSet} (b : interlaced_bilattice X) : iscomprelrelfun2 (rightEq b) (rightEq b) (meet b).
  Proof.
    intros ? ? ? ? H1 H2.
    use (!iscomp_consensus_rightRel (make_interlaced_bilattice (dual_bilattice_is_interlaced b)) _ _ _ _ (!H1) (!H2)).
  Defined.

  Definition iscomp_join_leftRel {X : hSet} (b : interlaced_bilattice X) : iscomprelrelfun2 (leftEq b) (leftEq b) (join b) :=
    iscomp_meet_rightRel (make_interlaced_bilattice (t_opp_bilattice_is_interlaced b)).

  Definition leftRel_meet_consensus {X : hSet} (b : interlaced_bilattice X) (x y : X): leftRel b (meet b x y) (consensus b x y).
  Proof.
    use (isantisymm_Lle (tlattice b)).
    - use Lmax_le_case.
      -- rewrite (iscomm_consensus _ (meet _ _ _) _ ) .
         use property2.
         exists (consensus b x y).
         split.
         --- use (bottom_interlacing_consensus_t (Lmin_le_l _ _ _) (Lmin_le_r _ _ _)).
         --- use isrefl_Lle.
      -- use property1_dual.
         exists (meet b x y).
         split.
         --- use (bottom_interlacing_meet_k (Lmin_le_l _ _ _) (Lmin_le_r _ _ _)).
         --- use isrefl_Lle.
    - use (top_interlacing_consensus_t (Lmax_le_l _ _ _) (Lmax_le_r _ _ _)).
  Defined.

  Definition iscomp_meet_leftRel {X : hSet} (b : interlaced_bilattice X) : iscomprelrelfun2 (leftEq b) (leftEq b) (meet b).
  Proof.
    intros x y z w ? ?.
    use (eqreltrans (leftEq b) _ (consensus b x z) _ (leftRel_meet_consensus _ _ _)).
    use (eqreltrans (leftEq b) _ (consensus b y w) _ (iscomp_consensus_leftRel _ _ _ _ _ _ _)).
    - assumption.
    - assumption.
    - use eqrelsymm. use leftRel_meet_consensus.
  Defined.

  Definition iscomp_join_rightRel {X : hSet} (b : interlaced_bilattice X) : iscomprelrelfun2 (rightEq b) (rightEq b) (join b) :=
    iscomp_meet_leftRel (make_interlaced_bilattice (t_opp_bilattice_is_interlaced b)).

  Definition rightRel_join_consensus {X : hSet} (b : interlaced_bilattice X) (x y : X) : rightRel b (join b x y) (consensus b x y)
    := leftRel_meet_consensus (make_interlaced_bilattice (t_opp_bilattice_is_interlaced b)) x y.

  Definition rightRel_meet_gullibility {X : hSet} (b : interlaced_bilattice X) (x y : X) : rightRel b (meet b x y) (gullibility b x y).
  Proof.
    use (isantisymm_Lle (tlattice b)).
    - use (bottom_interlacing_consensus_t (Lmin_le_l _ _ _) (Lmin_le_r _ _ _)).
    - use Lmin_le_case.
      -- rewrite iscomm_consensus.
         use property1_dual_opp_t.
         exists (gullibility b x y).
         split.
         --- exact (top_interlacing_meet_k (Lmax_le_l _ _ _) (Lmax_le_r _ _ _)).
         --- use isrefl_Lle.
      -- use property2_opp_t .
         exists (meet b x y).
         split.
         --- exact (bottom_interlacing_gullibility_t (Lmin_le_l _ _ _) (Lmin_le_r _ _ _)).
         --- use isrefl_Lle.
  Defined.

  Definition leftRel_join_gullibility {X : hSet} (b : interlaced_bilattice X) (x y : X) : leftRel b (join b x y) (gullibility b x y) :=
    rightRel_meet_gullibility (make_interlaced_bilattice (t_opp_bilattice_is_interlaced b)) x y.

  Definition iscommsetquotfun2 {X: hSet} {R : eqrel X} (f : binop X) (is : iscomprelrelfun2 R R f) (p : iscomm f) : iscomm (setquotfun2 R R f is).
  Proof.
    use (setquotuniv2prop _ (λ x y ,  @eqset (setquotinset _) ((setquotfun2 _ _ _ is) x y) ((setquotfun2 _ _ _ _) y x) )).
    intros x y.
    cbn.
    rewrite p.
    reflexivity.
  Defined.

  Definition isassocsetquotfun2 {X : hSet} {R : eqrel X} (f : binop X) (is : iscomprelrelfun2 R R f) (p : isassoc f) : isassoc (setquotfun2 R R f is).
  Proof.
    set (ff := setquotfun2 _ _ _ is).
    intros x0 y0 z0.
    use (setquotuniv3prop _ (λ x y z, @eqset (setquotinset _) (ff (ff z x) y) (ff z (ff x y)))).
    intros x y z.
    cbn.
    rewrite p.
    reflexivity.
  Defined.

  Definition leftLattice {X : hSet} (b : interlaced_bilattice X) : lattice (setquotinset (leftRel b)).
  Proof.
    set (iscc := iscomp_consensus_leftRel b).
    set (iscg := iscomp_gullibility_leftRel b).
    set (cc := setquotfun2 (leftEq b) (leftEq b) (consensus b) iscc).
    set (gg := setquotfun2 (leftEq b) (leftEq b) (gullibility b) iscg).
    exists cc, gg.
    do 4 (try split).
    - use (isassocsetquotfun2 (consensus b) iscc (isassoc_Lmin (klattice b))).
    - use (iscommsetquotfun2 (consensus b) iscc (iscomm_consensus b)).
    - use (isassocsetquotfun2 (gullibility b) iscg (isassoc_Lmax (klattice b))).
    - use (iscommsetquotfun2 (gullibility b) iscg (iscomm_gullibility b)).
    - use (setquotuniv2prop _ (λ x y, @eqset (setquotinset _) (cc x (gg x y)) x)).
      intros x y.
      cbn.
      rewrite (consensus_gullibility_absorb b).
      reflexivity.
    - use (setquotuniv2prop _ (λ x y, @eqset (setquotinset _) (gg x (cc x y)) x)).
      intros x y.
      cbn.
      rewrite (gullibility_consensus_absorb b).
      reflexivity.
  Defined.

  Definition rightLattice {X : hSet} (b : interlaced_bilattice X) : lattice (setquotinset (rightRel b)) :=
    leftLattice (make_interlaced_bilattice (t_opp_bilattice_is_interlaced b)).

  Definition leftAndRightIsId {X : hSet} (b : interlaced_bilattice X) (x y : X) (p1 : leftRel b x y) (p2 : rightRel b x y) : x = y.
  Proof.
    set (p := p1 @ !p2).
    use (isantisymm_Lle (tlattice b)).
    - use (istrans_Lle (tlattice _) x (join b x y) y (Lmax_le_l _ _ _)).
      rewrite p.
      use Lmin_le_r.
    - use (istrans_Lle (tlattice _) y (join b x y) x (Lmax_le_r _ _ _)).
      rewrite p.
      use Lmin_le_l.
  Defined.

  Definition interlaced_bilattices_are_prod {X : hSet} (b : interlaced_bilattice X) : ∑ (X1 X2 : hSet) (l1 : lattice X1) (l2 : lattice X2) , prod_bilattice X1 X2 l1 l2 :=
    setquotinset (leftRel b),, setquotinset (rightRel b),,leftLattice b,,rightLattice b,,make_prod_bilattice (leftLattice b) (rightLattice b).

  Definition XisLeftCrossRight {X : hSet} (b : interlaced_bilattice X) : weq X (prod_bilattice_carrier (setquotinset (leftRel b)) (setquotinset (rightRel b))) .
  Proof.
    (** First, move calculation from equivalence classes to representatives **)
    exists (λ x, setquotpr (leftEq b) x,, setquotpr (rightEq b) x).
    intro y; destruct y as [yL yR].
    set (TL := λ yL, λ yR : setquotinset (rightRel b), hfiber (λ x : X, setquotpr (leftEq b) x,, setquotpr (rightEq b) x) (yL,, yR)).
    use (setquotunivprop (leftEq b) (λ yL, make_hProp (iscontr (TL yL yR)) (isapropiscontr (TL yL yR)))).
    intro y1.
    set (TR := λ yR, TL (setquotpr (leftEq b) y1) yR).
    use (setquotunivprop (rightEq b) (λ yR, make_hProp (iscontr (TR yR)) (isapropiscontr (TR yR)))).
    intro y2.

    (** Then, define the center of contraction  **)
    set (c := consensus b (meet b y1 (gullibility b y1 y2)) (join b y2 (gullibility b y1 y2))).
    assert (HL : setquotpr (leftEq b) c = setquotpr (leftEq b) y1).
    {
      use weqpathsinsetquot.
      use (eqreltrans _ _ (meet b (meet b y1 (gullibility b y1 y2)) (join b y2 (gullibility b y1 y2))) _ ).
      {
        use eqrelsymm.
        use leftRel_meet_consensus.
      }
      use (eqreltrans _ _ (meet b (meet b y1 (join b y1 y2)) (join b y2 (join b y1 y2))) _ ).
      {
        use iscomp_meet_leftRel.
        - use iscomp_meet_leftRel.
          -- use eqrelrefl.
          -- use eqrelsymm.
             use leftRel_join_gullibility.
        - use iscomp_join_leftRel.
          -- use eqrelrefl.
          -- use eqrelsymm.
             use leftRel_join_gullibility.
      }
      rewrite meet_join_absorb,
        iscomm_join,
        isassoc_join,
        join_id,
        meet_join_absorb.
      use eqrelrefl.
    }
    assert (HR : setquotpr (rightEq b) c = setquotpr (rightEq b) y2).
    {
      use weqpathsinsetquot.
      use (eqreltrans _ _ (join b (meet b y1 (gullibility b y1 y2)) (join b y2 (gullibility b y1 y2))) _ ).
      {
        use eqrelsymm.
        use rightRel_join_consensus.
      }
      use (eqreltrans _ _ (join b (meet b y1 (meet b y1 y2)) (join b y2 (meet b y1 y2))) _ ).
      {
        use iscomp_join_rightRel.
        - use iscomp_meet_rightRel.
          -- use eqrelrefl.
          -- use eqrelsymm.
             use rightRel_meet_gullibility.
        - use iscomp_join_rightRel.
          -- use eqrelrefl.
          -- use eqrelsymm.
             use rightRel_meet_gullibility.
      }
      rewrite (iscomm_meet _ y1 (meet _ _ _)),
        (iscomm_meet _ y1 y2),
        isassoc_meet,
        meet_id,
        join_meet_absorb,
        iscomm_join,
        join_meet_absorb.
      use eqrelrefl.
    }
    exists (c,,pathsdirprod HL HR).

    (** and prove that it is a center of contraction **)
    intro t.
    use total2_paths_f.
    - use (! leftAndRightIsId _ _ _
             (invmap (weqpathsinsetquot _ _ _) (HL @ ! (maponpaths pr1 (pr2 t))))
             (invmap (weqpathsinsetquot _ _ _) (HR @ ! (maponpaths dirprod_pr2 (pr2 t))))
          ).
    - use (proofirrelevance_hProp (
               @eqset
                 (make_hSet _ (isaset_dirprod (isasetsetquot (leftEq b)) (isasetsetquot (rightEq b))))
                 (setquotpr (leftEq b) c,, setquotpr (rightEq b) c)
                 (setquotpr (leftEq b) y1,, setquotpr (rightEq b) y2)
          )).
  Defined.

  (*
  Definition weq_interlaced_prod : weq (∑ (X : hSet), interlaced_bilattice X) (∑ (X1 X2 : hSet) (l1 : lattice X1) (l2 : lattice X2) , prod_bilattice X1 X2 l1 l2).
  Proof.
    use (Equivalence_to_weq).
    use (makeEquivalence).
    - intro b.
      exact (interlaced_bilattices_are_prod (pr2 b)).
    - intro b.
      exists (prod_bilattice_carrier (pr1 b) (pr1 (pr2 b))).
      exact (make_interlaced_bilattice (prod_bilattices_are_interlaced (pr2 (pr2 (pr2 (pr2 b)))))).
    -
  Defined.
*)
End representation_theorems.

Section bilattice_FOUR.
  Definition bool_lattice : lattice boolset .
  Proof.
    exists (λ b1 b2 : boolset, if b1 then b2 else false), (λ b1 b2 : boolset, if b1 then true else b2).
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

  Check prod_bilattices_are_interlaced FOUR : is_interlaced FOUR .

  Definition is_distributive_FOUR : is_distributive_bilattice FOUR .
  Proof.
    repeat apply make_dirprod; intros [x1 x2] [y1 y2] [z1 z2]; induction x1, x2, y1, y2, z1, z2; trivial.
  Defined.

End bilattice_FOUR.
