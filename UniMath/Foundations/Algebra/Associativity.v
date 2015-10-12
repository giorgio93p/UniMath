Require Export UniMath.Foundations.Sequences.
Require Export UniMath.Foundations.Algebra.Monoids_and_Groups.
Unset Automatic Introduction.

(* confirm that [stnsum] and [stnprod] are associative in the same way as the parser *)

Local Notation "●" := (idpath _).

Goal ∀ n, 0+n = n.
Proof. reflexivity. Defined.

Goal ∀ n, n+0 = n.
Proof. try reflexivity. Abort.

Goal ∀ n, n*1 = n.
Proof. try reflexivity. Abort.

Goal ∀ n, 1*n = n.              (* this should be made to work *)
Proof. try reflexivity. Abort.

Goal ∀ (f : stn 3 -> nat), stnsum f = f(0,,●) + f(1,,●) + f(2,,●).
Proof. reflexivity. Defined.

Goal ∀ (f : stn 3 -> nat), stnprod f = f(0,,●) * f(1,,●) * f(2,,●).
Proof. try reflexivity. Abort.

Goal ∀ (f : stn 3 -> nat), stnprod f = 1 * f(0,,●) * f(1,,●) * f(2,,●).
Proof. reflexivity. Defined.

(* demonstrate for the reader that the Coq parser is left-associative with "*" *)

Open Scope multmonoid.

Goal ∀ (M:monoid) (x y z:M), x*y*z = (x*y)*z.
Proof. reflexivity. Defined.

Goal ∀ (M:monoid) (x y z:M), x*y*z = x*(y*z).
Proof. try reflexivity. apply assocax. Defined.

(* demonstrate for the reader that the Coq parser is left-associative with "+" *)

Open Scope addmonoid.

Goal ∀ (M:monoid) (x y z:M), x+y+z = (x+y)+z.
Proof. reflexivity. Defined.

Goal ∀ (M:monoid) (x y z:M), x+y+z = x+(y+z).
Proof. try reflexivity. apply assocax. Defined.

Close Scope addmonoid.

(* so we define iterated products in the same way now, with left associativity: *)

Definition sequenceProduct {M:monoid} : Sequence M -> M.
Proof.
  intros ? [n x].
  induction n as [|n sequenceProduct].     
  { exact 1. }
  { exact (sequenceProduct (pr2 (drop (S n,,x) (negpathssx0 _))) * x (lastelement _)). }
Defined.

Definition doubleProduct {M:monoid} : Sequence (Sequence M) -> M.
Proof.
  intros ? [n x].
  induction n as [|n doubleProduct].     
  { exact 1. }
  { exact ((doubleProduct (x ∘ dni_allButLast _) * sequenceProduct (x (lastelement _)))). }
Defined.

(* verify that our associativity matches that of the parser, with an extra "1" *)

Goal ∀ (M:monoid) (f:stn 3 -> M), sequenceProduct(3,,f) = 1 * f(O,,●) * f(S O,,●) * f(S(S O),,●).
Proof. reflexivity. Defined.

Goal ∀ (M:monoid) (f:stn 3 -> Sequence M),
       doubleProduct(3,,f) =
          1 * sequenceProduct (f(O,,●))
            * sequenceProduct (f(S O,,●))
            * sequenceProduct (f(S(S O),,●)).
Proof. reflexivity. Defined.

(* some rewriting rules *)

Definition sequenceProductStep {M:monoid} {n} (x:stn (S n) -> M) :
  sequenceProduct (S n,,x) = sequenceProduct (n,,x ∘ dni_allButLast _) * x (lastelement _).
Proof. intros. reflexivity. Defined.

Definition sequenceProductCheck {M:monoid} (x:Sequence M) (m:M) :
  sequenceProduct (append x m) = sequenceProduct x * m.
Proof. intros ? [n x] ?.
       unfold append.
       rewrite sequenceProductStep.
       unfold funcomp.
       unfold lastelement.
       induction (natlehchoice4 n n (natgthsnn (S n))) as [p|q].
       { contradicts (isirreflnatlth n) p. }
       { apply (maponpaths (λ a, a * m)).
         apply (maponpaths (λ x, sequenceProduct (n,,x))).
         apply funextfun; intros [i b].
         simpl.
         induction (natlehchoice4 i n (natlthtolths i n b)) as [r|s].
         { simpl. apply maponpaths. apply maponpaths. apply isasetbool. }
         { contradicts (natlthtoneq _ _ b) s. }}
Defined.

Lemma doubleProductStep {M:monoid} {n} (x:stn (S n) -> Sequence M) :
  doubleProduct (S n,,x) = doubleProduct (n,,x ∘ dni_allButLast _) * sequenceProduct (x (lastelement _)).
Proof. intros. reflexivity. Defined.

(* The general associativity theorem. *)

Theorem associativityOfProducts {M:monoid} (x:Sequence (Sequence M)) :
  sequenceProduct (flatten x) = doubleProduct x.
Proof.
  (* this proof comes from the Associativity theorem, Bourbaki, Algebra, Theorem 1, page 4. *)
  intros ? [n x].
  induction n as [|n IHn].
  { reflexivity. }
  { rewrite flattenStep, doubleProductStep.
    generalize (x (lastelement _)) as z.
    generalize (x ∘ dni_allButLast _) as y.
    intros y [m z].
    induction m as [|m IHm].
    { change (sequenceProduct (0,, z)) with (unel M). rewrite runax.
      change (concatenate (flatten (n,, y)) (0,, z)) with (flatten (n,, y)).
      exact (IHn y). }
    { rewrite sequenceProductStep, concatenateStep.
      generalize (z (lastelement m)) as w; generalize (z ∘ dni_allButLast _) as v; intros.
      rewrite <- assocax.
      rewrite sequenceProductCheck.
      apply (maponpaths (λ u, u*w)).
      apply IHm. } }
Defined.
