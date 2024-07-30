From Coq Require Import ssreflect ssrfun ZArith.
From HB Require Import structures.
Require Import Unicode.Utf8.
Require Import Bool.Bool.
Require Import Coq.Logic.ClassicalFacts.
(*Commutative Monoids*)

HB.mixin Record CMonoid_of M := {
  id : M;
  add : M -> M -> M;
  addrA : associative add;
  addrC : commutative add;
  addl0 : left_id id add;
}.

HB.structure Definition CMonoid := { M of CMonoid_of M }.

(*Interval Structure*)

HB.mixin Record Interval_of I:= {
  zero : I;
  join : I -> I -> I;
  joinrA : associative join;
  joinrC : commutative join;
  joinl0 : left_id zero join;

  one : I;
  meet : I -> I -> I;
  meetrA : associative meet;
  meetrC : commutative meet;
  meetl1 : left_id one meet;

  inv : I -> I;
  inv_inv : ∀ i, inv (inv i) = i;
  inv_de_morgan_l : ∀ p q, inv (join p q) = meet (inv p) (inv q);
}.

HB.structure Definition Interval := { I of Interval_of I}.

Lemma id_unique: ∀ {T: Type} (f: T -> T -> T) (i1 i2: T),
(∀ s, f s i1 = s) -> (∀ s, f i2 s = s) -> (i1=i2).
Proof.
  intros.
  rewrite <- (H i2). rewrite H0. auto.
Qed.

Notation "0" := zero.
Notation "1" := one.
(* Infix "|" := join (at level 10). *)
(* Infix "&" := meet (at level 10). *)
Notation "!" := inv.

HB.builders Context (I: Type) (f : Interval_of I).
  HB.instance Definition join_CMonoid := CMonoid_of.Build I zero join joinrA joinrC joinl0.
  HB.instance Definition meet_CMonoid := CMonoid_of.Build I one meet meetrA meetrC meetl1.
HB.end.

Theorem inv_de_morgan_r: ∀ {A: Interval.type} (p q: A), !(meet p q) = join (!p) (!q).
Proof.
intros.
rewrite <- inv_inv. rewrite inv_de_morgan_l. rewrite! inv_inv. reflexivity.
Qed.

Lemma inv0isid: ∀ {I: Interval.type} (i:I), meet i (!(0:I)) = i.
Proof.
intros.
rewrite <- (inv_inv i) at 2. rewrite <- (joinl0 (!i)). 
rewrite inv_de_morgan_l. rewrite inv_inv. apply meetrC.
Qed.

Theorem inv_1_0: ∀ {I: Interval.type}, (1:I) = !(0:I).
Proof.
intros. simpl. symmetry. apply (id_unique meet (!(0:I)) (1:I) inv0isid meetl1).
Qed.

Corollary inv_0_1: ∀ {I: Interval.type}, (0:I) = !(1:I).
intros. rewrite <- inv_inv. rewrite inv_1_0. rewrite! inv_inv. auto.
Qed.

HB.instance Definition boolean_is_intv := Interval_of.Build bool
false orb orb_assoc orb_comm orb_false_l 
true andb andb_assoc andb_comm andb_true_l
negb negb_involutive negb_orb.

(*Barycentric Space*)

HB.mixin Record Baryspace_of (I : Interval.type) A:= {
  barysum : I -> A -> A -> A;
  barysum0 : ∀ a b, barysum 0 a b = a;
  barysumid : ∀ a p, barysum p a a = a;
  barysuminv : ∀ a b p, barysum p a b = barysum (!p) b a;
  barysumassoc: ∀ a b c p q r s, 
    s = (meet p q) -> meet p (!q) = meet r (!s) ->  
      barysum p a (barysum q b c) = barysum s (barysum r a b) c;
}.

HB.structure Definition Baryspace I := { A of Baryspace_of I A}.

Lemma barysum1 {I : Interval.type} {B: Baryspace.type I} (a b: B): barysum 1 a b = b.
intros. rewrite barysuminv. rewrite <- inv_0_1. apply barysum0. 
Qed.

HB.mixin Record _BaryIntv_of I of Interval_of I := {
    IsB: Baryspace_of.axioms_ I I
}.

HB.structure Definition _BaryIntv := { I of _BaryIntv_of I & Interval_of I}.

(* Inductive BarycentricInterval (I: BInterval.type)  := 
  | One (p: I)(H: p = 1)
  | Zero (p: I)(H: p = 0)
  | Other (p: I).

Lemma ibs1 {I: BInterval.type} (p r s: I) 
  (H1: p = 1) (H2: s = 0): barysum p (r: _BaryIntv.sort I) s = 0.
rewrite H1. rewrite H2. apply barysum1. Qed.
Lemma ibs2 {I: BInterval.type} (p r s: I) 
  (H1: p = 1) (H2: s = 1): barysum p (r: _BaryIntv.sort I) s = 1.
rewrite H1. rewrite H2. apply barysum1. Qed.
Lemma ibs3 {I: BInterval.type} (p r s: I) 
  (H1: p = 0) (H2: r = 0): barysum p (r: _BaryIntv.sort I) s = 0.
rewrite H1. rewrite H2. apply barysum0. Qed.
Lemma ibs4 {I: BInterval.type} (p r s: I) 
  (H1: p = 0) (H2: r = 1): barysum p (r: _BaryIntv.sort I) s = 1.
rewrite H1. rewrite H2. apply barysum0. Qed.
Lemma ibs5 {I: BInterval.type} (p r s: I) 
  (H1: r = 1) (H2: s = 1): barysum p (r: _BaryIntv.sort I) s = 1.
rewrite H1. rewrite H2. apply barysumid. Qed.
Lemma ibs6 {I: BInterval.type} (p r s: I) 
  (H1: r = 0) (H2: s = 0): barysum p (r: _BaryIntv.sort I) s = 0.
rewrite H1. rewrite H2. apply barysumid. Qed.


Definition IntervalBarysum {I: BInterval.type} (p r s: BarycentricInterval I) := 
match s with
  | Zero _ _s Hs => match p with 
    | One _ _p Hp => Zero (barysum p r s) (ibs1 p r s Hp Hs)
    | Zero _ _p Hp => match r with 
      | Zero _ _r Hr => Zero (barysum p r s) (ibs3 p r s Hp Hr)
      | One _ _r Hr => One (barysum p r s) (ibs4 p r s Hp Hr)
      | Other _ _r => Other (barysum p r s) end
    | Other _  _p => match r with
      | Zero _ _r Hr => Zero (barysum p r s) (ibs6 p r s Hr Hs)
      | One _ _r Hr => Other (barysum p r s)
      | Other _ _r => Other (barysum p r s) end
    end
  | One _ _s Hs => match p with 
    | One _ _p Hp => One (barysum p r s) (ibs2 p r s Hp Hs) 
    | Zero _ _p Hp => match r with 
      | Zero _ _r Hr => Zero (barysum p r s) (ibs3 p r s Hp Hr)
      | One _ _r Hr => One (barysum p r s) (ibs4 p r s Hp Hr)
      | Other _ _r => Other (barysum p r s) end
    | Other _ _p => match r with
      | Zero _ _r Hr => Other (barysum p r s)
      | One _ _r Hr => One (barysum p r s) (ibs5 p r s Hr Hs)
      | Other _ _r => Other (barysum p r s) end
    end
end. 
 *)

Module BIntv.
#[non_forgetful_inheritance]
HB.instance Definition I_is_bary {I : _BaryIntv.type} := (IsB:Baryspace_of.axioms_ I I).

HB.mixin Record BInterval_of I of _BaryIntv_of I of Interval_of I:= {
  inv_bary_dist: ∀(p q r: _BaryIntv.sort I), !(barysum r p q) = barysum r (!p) (!q);
  meet_bary_dist: ∀(p q r s: _BaryIntv.sort I), (meet s (barysum r p q)) = barysum r (meet s p) (meet s q);
  cancel: ∀(p p' q: _BaryIntv.sort I), q<>0 -> meet p q = meet p' q -> p = p';
  meet_sum0: ∀(r s: _BaryIntv.sort I), (meet r s) = barysum r (0: _BaryIntv.sort I) s;

  bracket: I -> I -> I -> I;
  bracket_basic: ∀ r s t: _BaryIntv.sort I, meet (bracket t r s) (barysum t r s) = meet t s;
  bracket_assoc1: ∀ (A: Baryspace.type I) (x y z: A) (r s: I),
    barysum s (barysum r x y) z = barysum (join r s) x (barysum (bracket s r 1 ) y z);
  bracket_assoc2: ∀ (A: Baryspace.type I) (x y z: A) (r s: I),
    barysum r x (barysum s y z)  = barysum  (meet r s) (barysum (bracket r 1 (!s)) x y) z;
  bracket_inv: ∀ r s t, !(bracket t r s) = bracket (!t) s r;
  bracket_dist: ∀ a b r s t, bracket t (meet a r) (meet b s) = bracket (bracket t a b) r s;

  (*to be decided*)
  sum_zero_dist: ∀ p q r: _BaryIntv.sort I, barysum p q r = 0 -> meet p r = 0;
  sum_zero_dist': ∀ p q r: _BaryIntv.sort I, barysum p q r = 0 -> meet (!p) q = 0;
  bracket_zero: ∀ a b c, meet a c = 0 -> bracket a b c = 0;
}.

HB.structure Definition BInterval := { I of BInterval_of I &}.

Theorem meet_0_absorb: ∀ {I: BInterval.type} (a:I), meet (0:I) a = (0:I).
Proof.
intros. rewrite meet_sum0. rewrite barysum0. reflexivity.
Qed.

Corollary join_1_absorb: ∀ {I: BInterval.type} (a:I), join (1:I) a = (1:I).
Proof.
intros. rewrite <- (inv_inv (join (1 : I) a)). rewrite inv_de_morgan_l. 
rewrite <- inv_0_1. rewrite meet_0_absorb. rewrite inv_1_0. reflexivity.
Qed.

Theorem join_sum1: ∀ (I: BInterval.type) (r s: _BaryIntv.sort I), (join r s) = barysum r s (1: _BaryIntv.sort I).
Proof.
intros. rewrite <- (inv_inv (join r s)). rewrite inv_de_morgan_l. 
rewrite meet_sum0. rewrite inv_bary_dist. rewrite <- barysuminv. rewrite inv_1_0. 
rewrite inv_inv. reflexivity. Qed.

Theorem join_bary_dist: ∀(I: BInterval.type) (p q r s: _BaryIntv.sort I), (join s (barysum r p q)) = barysum r (join s p) (join s q).
Proof.
intros. rewrite <- (inv_inv (join s (barysum r p q))). 
rewrite inv_de_morgan_l. rewrite inv_bary_dist. rewrite meet_bary_dist.
rewrite <- !inv_de_morgan_l. rewrite inv_bary_dist. rewrite !inv_inv.
reflexivity.
Qed.

Example test1 (I : BInterval.type) (p: _BaryIntv.sort I):= barysum p p p.
Example test2 (I : BInterval.type) (p: Interval.sort I) (A: Baryspace.type I) (a: A):= barysum p a a. 
Example test3 (I : BInterval.type) (p: I) (A: Baryspace.type I) (a: A) := 
  barysum (barysum p (p: _BaryIntv.sort I) (p: _BaryIntv.sort I)) a a.

Lemma bracket_id: ∀ (I: BInterval.type) (a b: I), a <> 0 -> bracket b a a = b.
Proof.
intros. 
specialize (bracket_basic a a b). 
rewrite barysumid. intros. apply cancel in H0. 
apply H0. apply H.
Qed.

Lemma bracket_1: ∀ (I: BInterval.type) (p q: I), (bracket p 0 q) = 1.
intros.
rewrite <- (inv_inv (bracket p 0 q)). rewrite bracket_inv. 
rewrite bracket_zero. rewrite meetrC. rewrite meet_0_absorb.
reflexivity.
rewrite inv_1_0. reflexivity.
Qed.

Lemma bracket_0: ∀ (I: BInterval.type) (r s: I), r <> 0 -> bracket 0 r s = 0.
Proof.
intros. specialize (bracket_basic r s 0). rewrite barysum0. rewrite meet_0_absorb.
rewrite <- (meet_0_absorb r) at 1. intros. apply cancel in H0.
apply H0. apply H.
Qed.

Lemma bracket_0_1: ∀ (I: BInterval.type) (p: I), p <> 0 -> bracket p 0 1 = 1.
Proof.
intros. specialize (bracket_basic 0 1 p). rewrite <- meet_sum0. rewrite (meetrC p 1). 
rewrite meetl1. intros. apply (cancel _ _ p). apply H. rewrite meetl1. apply H0.
Qed.

Lemma bracket_1_0: ∀ (I: BInterval.type) (p: I), p <> 1 -> bracket p 1 0 = 0.
Proof.
intros.
assert (!p <> 0). {
  unfold not. intros. apply H. rewrite inv_0_1 in H0. rewrite <- (inv_inv p).
  rewrite <- (inv_inv 1). f_equal. apply H0. 
} 
rewrite <- (inv_inv p).
assert (bracket (! (! p)) 1 0 = !(bracket (!p) 0 1)). {
  rewrite bracket_inv. reflexivity.
}
rewrite H1. rewrite inv_0_1. rewrite <- inv_0_1 at 1. f_equal.
apply bracket_0_1. apply H0.
Qed.

Definition barysumI {I: BInterval.type} (t r s: I): (I) :=
  barysum t (r:_BaryIntv.sort I) s.

Lemma bracket_decomp1_0: ∀ (I:BInterval.type) p q r s (x y z: _BaryIntv.sort I),
  barysum p x (barysum q y z) = 0 ->
  s = meet p q -> meet p (!q) = meet r (!s) ->  
  meet (bracket r x y) (!(bracket s (barysum r x y) z)) = 
    meet (bracket p x (barysum q y z)) (!(bracket q y z)).
Proof.
  intros.
  assert (barysum s (barysum r x y) z = 0) as HSR.
  {
    rewrite <- H. symmetry. apply barysumassoc. apply H0. apply H1.
  }
  apply sum_zero_dist in H as H'1. apply sum_zero_dist' in H as H'2.
  apply sum_zero_dist in HSR as HSR'1. apply sum_zero_dist' in HSR as HSR'2.
  rewrite !bracket_inv. rewrite (bracket_zero p). apply H'1.
  rewrite (bracket_zero (!s)). apply HSR'2. rewrite meet_0_absorb. rewrite meetrC. rewrite meet_0_absorb.
  reflexivity.
Qed.

Lemma bracket_decomp2_0: ∀ (I:BInterval.type) p q r s (x y z: _BaryIntv.sort I),
  barysum p x (barysum q y z) = 0 ->
  s = meet p q -> meet p (!q) = meet r (!s) ->  
    (bracket s (barysum r x y) z) = 
      meet (bracket p x (barysum q y z)) (bracket q y z).
Proof.
  intros.
  assert (barysum s (barysum r x y) z = 0) as HSR.
  {
    rewrite <- H. symmetry. apply barysumassoc. apply H0. apply H1.
  }
  apply sum_zero_dist in H as H'1. apply sum_zero_dist' in H as H'2.
  apply sum_zero_dist in HSR as HSR'1. apply sum_zero_dist' in HSR as HSR'2.
  rewrite (bracket_zero s). apply HSR'1. rewrite (bracket_zero p). apply H'1.
  rewrite meet_0_absorb.
  reflexivity.
Qed.

(*Here I took the liberty of forcing that a=0 is decidable*)
Axiom eq0_i_decidable: ∀(I:BInterval.type) (a: I), a = (0:I) \/ a <> (0:I).

Theorem meet0: ∀(I:BInterval.type) (a b: I), meet a b = 0 -> a = 0 \/ b = 0.
Proof.
intros.
destruct (eq0_i_decidable I a). left. assumption.
right. rewrite <- (meet_0_absorb a) in H. rewrite (meetrC a) in H. 
apply cancel in H. apply H. apply H0.
Qed.

Theorem bracket_zero': ∀ {I:BInterval.type} (a b c d:I), meet a c = 0 -> meet (bracket a b d) c = 0.
Proof.
intros.
apply meet0 in H as H1. destruct H1. 
- rewrite H0. rewrite bracket_zero. apply meet_0_absorb. apply meet_0_absorb.
- rewrite H0. rewrite meetrC. apply meet_0_absorb.
Qed.



Lemma bracket_decomp1_: ∀ (I:BInterval.type) p q r s (x y z: _BaryIntv.sort I),
  barysum p x (barysum q y z) <> 0 ->
  s = meet p q -> meet p (!q) = meet r (!s) ->  
  meet (bracket r x y) (!(bracket s (barysum r x y) z)) = 
    meet (bracket p x (barysum q y z)) (!(bracket q y z)).
Proof.
  intros.
  rewrite !bracket_inv. 
  assert (barysum p x (barysum q y z) = barysumI s (barysum r x y) z).
  {
    unfold barysumI.
    apply (barysumassoc (x:_BaryIntv.sort I)). apply H0. apply H1.
  } 
  assert (meet (meet (bracket r x y)
  (bracket (! s) z (barysum r x y))) (barysum p x (barysum q y z)) = meet (meet (!s) r) y).
  {
    rewrite H2. rewrite <- meetrA. unfold barysumI. rewrite (barysuminv _ _ s). rewrite bracket_basic.
    rewrite (meetrC (!s) (barysum r x y)). rewrite meetrA. rewrite bracket_basic. 
    rewrite meetrC. rewrite meetrA. reflexivity.
  }
  assert (meet (meet (bracket p x (barysum q y z))
  (bracket (! q) z y)) (barysum p x (barysum q y z)) = meet (meet (!s) r) y).
  {
    rewrite (meetrC (bracket p x (barysum q y z))). rewrite <- meetrA.
    rewrite bracket_basic. rewrite barysuminv. rewrite meetrC. rewrite <- (meetrA p).
    rewrite (meetrC (barysum (! q) z y)). rewrite bracket_basic. rewrite meetrA. 
    rewrite H1. rewrite (meetrC r). reflexivity.
  }
  rewrite <- H4 in H3. apply cancel in H3. apply H3. apply H.
Qed.

Lemma bracket_decomp2_: ∀ (I:BInterval.type) p q r s (x y z: _BaryIntv.sort I),
  barysum p x (barysum q y z) <> 0 -> s = meet p q -> meet p (!q) = meet r (!s) ->  
    (bracket s (barysum r x y) z) = 
      meet (bracket p x (barysum q y z)) (bracket q y z).
Proof.
  intros.
  assert (barysum p x (barysum q y z) = barysumI s (barysum r x y) z).
  {
    unfold barysumI.
    apply (barysumassoc (x:_BaryIntv.sort I)). apply H0. apply H1.
  } 
  assert (meet (bracket s (barysum r x y) z) (barysum p x (barysum q y z)) = meet s z).
  {
    rewrite H2. unfold barysumI. apply bracket_basic.
  }
  assert (meet (meet (bracket p x (barysum q y z)) (bracket q y z)) (barysum p x (barysum q y z)) = meet s z).
  {
    rewrite (meetrC _ (bracket q y z)). rewrite <- meetrA. rewrite bracket_basic.
    rewrite (meetrC p). rewrite meetrA. rewrite bracket_basic. rewrite meetrC. 
    rewrite H0. rewrite meetrA. reflexivity.
  }
  rewrite <- H4 in H3. apply cancel in H3. apply H3. apply H.
Qed.



Theorem bracket_decomp1: ∀ (I:BInterval.type) p q r s (x y z: _BaryIntv.sort I),
  s = meet p q -> meet p (!q) = meet r (!s) ->  
  meet (bracket r x y) (!(bracket s (barysum r x y) z)) = 
    meet (bracket p x (barysum q y z)) (!(bracket q y z)).
Proof.
  intros. destruct (eq0_i_decidable I (barysum p x (barysum q y z))).
  apply bracket_decomp1_0; assumption.
  apply bracket_decomp1_; assumption.
Qed.

Theorem bracket_decomp2: ∀ (I:BInterval.type) p q r s (x y z: _BaryIntv.sort I),
  s = meet p q -> meet p (!q) = meet r (!s) ->  
    (bracket s (barysum r x y) z) = 
      meet (bracket p x (barysum q y z)) (bracket q y z).
Proof.
  intros. destruct (eq0_i_decidable I (barysum p x (barysum q y z))).
  apply bracket_decomp2_0; assumption.
  apply bracket_decomp2_; assumption.
Qed.

Theorem barysum_2_0: ∀ (I: BInterval.type) (A: Baryspace.type I) 
  (x x' y y': A) (r s t: I), barysumI t r s = 0 -> 
  barysum t (barysum r x y) (barysum s x' y')
    = barysum (barysumI t r s) (barysum (bracket t (!r) (!s)) x x') (barysum (bracket t r s) y y').
Proof.
  intros. 
  rewrite H. rewrite barysum0. 
  rewrite (barysuminv x y r). rewrite bracket_assoc1.
  rewrite (bracket_assoc2 A x x' y'). 
  rewrite (barysuminv _ _ (meet (bracket t (! r) 1) s)). 
  rewrite (bracket_assoc2 A y).
  rewrite (barysuminv _ _ (meet (join (! r) t)(!(meet (bracket t (! r) 1)s)))).

  assert ((bracket (bracket t (! r) 1) 1 (! s)) = bracket t (!r) (!s)).
  {
    rewrite <- bracket_dist. rewrite (meetrC (!r) 1). rewrite !meetl1. reflexivity.
  }
  rewrite H0.
  assert (((!(meet (join (! r) t)(!(meet(bracket t (! r) 1)s))))) = 0).
  {
    rewrite <- (inv_inv t) at 1. rewrite <- inv_de_morgan_r. rewrite (meetrC r). 
    rewrite (sum_zero_dist' t r s). apply H. rewrite <- inv_1_0.  rewrite meetl1.
    rewrite inv_inv. rewrite bracket_zero'. apply (sum_zero_dist t r s). apply H.
    reflexivity.
  }
  rewrite H1. rewrite barysum0. reflexivity.
Qed.

Theorem barysum_2_: ∀ (I: BInterval.type) (A: Baryspace.type I) 
  (x x' y y': A) (r s t: I), barysumI t r s <> 0 -> 
  barysum t (barysum r x y) (barysum s x' y')
    = barysum (barysumI t r s) (barysum (bracket t (!r) (!s)) x x') (barysum (bracket t r s) y y').
Proof. 
  intros.
  rewrite (barysuminv x y r). rewrite bracket_assoc1.
  rewrite (bracket_assoc2 A x x' y'). 
  rewrite (barysuminv _ _ (meet (bracket t (! r) 1) s)). 
  rewrite (bracket_assoc2 A y).
  rewrite (barysuminv _ _ (meet (join (! r) t)(!(meet (bracket t (! r) 1)s)))).
  assert (!(meet (join (! r) t) (!(meet (bracket t (! r) 1) s)) )= barysumI t r s).
  {
    rewrite meet_sum0. rewrite inv_bary_dist.
    rewrite inv_inv. rewrite meet_sum0. rewrite <- inv_1_0.
    rewrite <- (bracket_assoc1 (_BaryIntv.sort I) 1). rewrite <- barysuminv.
    rewrite <- (meet_sum0 r). rewrite meetrC. rewrite meetl1. reflexivity.
  }
  rewrite H0.
  assert ((bracket (bracket t (! r) 1) 1 (! s)) = bracket t (!r) (!s)).
  {
    rewrite <- bracket_dist. rewrite (meetrC (!r) 1). rewrite !meetl1. reflexivity.
  }
  rewrite H1.
  rewrite inv_inv.
  assert ((bracket (join (! r) t) 1 (meet (bracket t (! r) 1)s)) = bracket t r s).
  {
    rewrite join_sum1. 
    assert (
      meet (bracket (barysum t(! r: _BaryIntv.sort I) 1) 1 (meet (bracket t (! r) 1) s)) 
      (barysum (barysum t (! r:_BaryIntv.sort I) 1) (1:_BaryIntv.sort I) (meet (bracket t (! r) 1) s)) = meet t s).
    {
      rewrite bracket_basic. rewrite meetrA. rewrite (meetrC (barysumI t (! r) 1)). 
      rewrite bracket_basic. rewrite (meetrC t 1). rewrite meetl1. reflexivity.
    } 
    rewrite meet_sum0 in H0. rewrite inv_bary_dist in H0. rewrite inv_inv in H0.
    rewrite joinrC in H0. rewrite join_sum1 in H0. rewrite <- inv_1_0 in H0. rewrite H0 in H2.
    assert (meet t s = meet (bracket t r s) (barysumI t r s)). symmetry. apply bracket_basic.
    rewrite H3 in H2. apply cancel in H2. rewrite <- (join_sum1 (I) (!r) (t)). rewrite joinrC. 
    rewrite join_sum1. apply H2. apply H.
  }
  rewrite H2. reflexivity.
Qed.

Theorem barysum_2: ∀ (I: BInterval.type) (A: Baryspace.type I) 
  (x x' y y': A) (t r s: I), barysum t (barysum r x y) (barysum s x' y')
    = barysum (barysumI t r s) (barysum (bracket t (!r) (!s)) x x') (barysum (bracket t r s) y y').
Proof.
intros.
destruct (eq0_i_decidable I (barysumI t r s)).
apply barysum_2_0; assumption.
apply barysum_2_; assumption.
Qed.

Inductive SumBarySpace {I: BInterval.type} (A B: Baryspace.type I) :=
| Tuple (a: A) (p: I) (b: B).


Notation "( a , b , c )" := (Tuple _ _ a b c).

Definition sum_barysum {I: BInterval.type} {A B: Baryspace.type I} (t: I)
  (p1 p2 : SumBarySpace A B) := 
match p1 with
| (x, r, y) => match p2 with 
| (x', s, y') => (barysum (bracket t (!r) (!s)) x x', (barysumI t r s), (barysum (bracket t r s) y y'))
end end.

Lemma sum_barysum0: ∀ {I: BInterval.type} {A B: Baryspace.type I} (p1 p2 : SumBarySpace A B),
  sum_barysum 0 p1 p2 = p1.
Proof.
intros.
destruct p2. destruct p1. unfold sum_barysum. 
rewrite !bracket_zero. apply meet_0_absorb. apply meet_0_absorb. 
unfold barysumI. f_equal; apply barysum0. 
Qed.

Lemma sum_barysumid: ∀ {I: BInterval.type} {A B: Baryspace.type I}  (p1 : SumBarySpace A B) (t: I),
  sum_barysum t p1 p1 = p1.
Proof.
intros.
destruct p1. unfold sum_barysum. unfold barysumI. rewrite !barysumid. reflexivity.
Qed.

Lemma sum_barysuminv: ∀ {I: BInterval.type} {A B: Baryspace.type I} (p1 p2 : SumBarySpace A B) (t: I) ,
  sum_barysum t p1 p2 = sum_barysum (!t) p2 p1.
Proof.
intros.
destruct p2. destruct p1. simpl. unfold barysumI. 
f_equal; try rewrite <- (bracket_inv _ _ (t)); rewrite barysuminv; reflexivity.
Qed.

Lemma sum_barysumassoc: ∀{I: BInterval.type} {A B: Baryspace.type I} (a b c: SumBarySpace A B) (p q r s: I),
s = (meet p q) -> meet p (!q) = meet r (!s) ->  
      sum_barysum p a (sum_barysum q b c) = sum_barysum s (sum_barysum r a b) c.
Proof.
intros.
destruct a,b,c.
unfold sum_barysum. 
assert (barysumI p p0 (barysumI q p1 p2) = barysumI s (barysumI r p0 p1) p2).
{
  unfold barysumI.
  apply (barysumassoc (p0:_BaryIntv.sort I)). apply H. apply H0.
} 
f_equal. 
- unfold barysumI. rewrite !inv_bary_dist. apply barysumassoc.
apply bracket_decomp2. apply H. apply H0.
symmetry. apply bracket_decomp1. apply H. apply H0.
- apply H1.
- unfold barysumI. apply barysumassoc.
apply bracket_decomp2. apply H. apply H0.
symmetry. apply bracket_decomp1. apply H. apply H0.
Qed.

HB.instance Definition sum_baryspace_barycentric {I: BInterval.type} (A B: Baryspace.type I) := 
 Baryspace_of.Build 
  I (SumBarySpace A B) sum_barysum sum_barysum0 sum_barysumid sum_barysuminv sum_barysumassoc.

End BIntv.
Import BIntv.

(* quotienting the space *)
From Coq Require Import Arith Relations Program Logic.

Definition compatible (T R : Type) (eqv : T -> T -> Prop)
  (f : T -> R) := forall x y : T, eqv x y -> f x = f y.

Record type_quotient (T : Type) (eqv : T -> T -> Prop)
  (Hequiv : equiv T eqv) := {
  quo :> Type;
  class :> T -> quo;
  quo_comp : forall (x y : T), eqv x y -> class x = class y;
  quo_comp_rev : forall (x y : T), class x = class y -> eqv x y;
  quo_lift : forall (R : Type) (f : T -> R),
    compatible _ _ eqv f -> quo -> R;
  quo_lift_prop : forall (R : Type) (f : T -> R) (Hf : compatible _ _ eqv f),
    forall (x : T),  (quo_lift _ f Hf) (class x) = f x;
  quo_surj : forall (c : quo), 
    exists x : T, c = class x
}.

(*The existence of such quotient structure is given by an axiom,
as in Cyril Cohen's work.
*)

Axiom quotient : forall (T : Type) (eqv : T -> T -> Prop) (p: equiv T eqv), 
  (type_quotient T eqv p).

Arguments quo {T} {eqv} {Hequiv}.
Arguments class {T} {eqv} {Hequiv}.
Arguments quo_lift {T} {eqv} {Hequiv} _ {R}.

Check quo_lift.

Record BEquiv {I : BInterval.type} {A : Baryspace.type I} := instBequiv{
  R : A -> A -> Prop;
  Equiv : equiv _ R;
  Compat : ∀ (x y x' y': A) (p: I), R x x' -> R y y' -> R (barysum p x y) (barysum p x' y');
  Qs := quotient A R Equiv
}.

Inductive SumBaryR {I : BInterval.type} {A B: Baryspace.type I} : (SumBarySpace A B) ->  (SumBarySpace A B) -> Prop := 
  | Refl (p: I) (a: A) (b: B): SumBaryR (a,p,b) (a,p,b)
  | A0 (a: A) (b b': B): SumBaryR (a,0,b) (a,0,b')
  | B1 (a a': A) (b: B): SumBaryR (a,1,b) (a',1,b).

Lemma sum_barysum_expl: ∀ {I : BInterval.type} {A B: Baryspace.type I} (p p0 p1: I) (a a0: A) (b b0:B), barysum p (a, p0, b) (a0, p1, b0) = sum_barysum p (a, p0, b) (a0, p1, b0).
reflexivity. Qed.

Lemma sum_baryr_compat: ∀ {I : BInterval.type} {A B: Baryspace.type I} (x y x' y': SumBarySpace A B ) (p: I), SumBaryR x x' -> SumBaryR y y' -> SumBaryR (barysum p x y) (barysum p x' y').
Proof.
  intros.
  inversion H.
  - inversion H0; rewrite !sum_barysum_expl; unfold sum_barysum.
    + apply Refl.
    + rewrite (bracket_zero p p0 0).
      rewrite meetrC. apply meet_0_absorb. rewrite !barysum0. apply Refl.
    + rewrite <- inv_0_1. 
      rewrite (bracket_zero p (inv p0) 0). rewrite meetrC. apply meet_0_absorb.
      rewrite !barysum0. apply Refl.
  - inversion H0; rewrite !sum_barysum_expl; unfold sum_barysum. 
    + rewrite !bracket_1. rewrite !barysum1. apply Refl.
    + unfold barysumI. rewrite barysumid. apply A0.
    + rewrite <- inv_0_1. rewrite <- inv_1_0. rewrite bracket_zero.
      rewrite meetrC. apply meet_0_absorb. rewrite !barysum0.
      rewrite bracket_1. rewrite !barysum1. apply Refl.
  - inversion H0; rewrite !sum_barysum_expl; unfold sum_barysum. 
    + rewrite <- inv_0_1. rewrite bracket_1. rewrite !barysum1. apply Refl.
    + rewrite <- inv_0_1. rewrite <- inv_1_0. rewrite (bracket_zero p 1 0).
      rewrite meetrC. apply meet_0_absorb. rewrite !bracket_1.
      rewrite !barysum1. rewrite !barysum0. apply Refl.
    + unfold barysumI. rewrite barysumid. apply B1.
Qed.
  

Lemma sum_baryr_eqv : ∀ {I : BInterval.type} {A B: Baryspace.type I}, equiv (SumBarySpace A B) SumBaryR.
Proof.
Admitted.
(* intros.
unfold equiv. split; try split.
+ unfold reflexive. intros. destruct x. apply Refl.
+ unfold transitive. intros. destruct x,y,z. inversion H.
  - apply H0. 
  - inversion H0.
    ++ rewrite <- H12. rewrite <- H6. apply A0.
    ++ apply A0.
    ++ 
  - inversion H0. 
    ++ rewrite <- H12. rewrite <- H6. apply B1.
    ++ 
    ++ apply B1.
+ unfold symmetric. intros. inversion H.
  - apply Refl.
  - apply A0.
  - apply B1. *)

Definition quot_sum_space {I : BInterval.type} (A B: Baryspace.type I) := quotient (SumBarySpace A B) SumBaryR sum_baryr_eqv.

Definition sum_bary_bequiv {I : BInterval.type} (A B: Baryspace.type I) := 
  instBequiv I (SumBarySpace A B) SumBaryR sum_baryr_eqv sum_baryr_compat.

(*
The barycentric sum on the quotient space A/~ is defined 
by composing the class function with the barycentric sum on A 
and then lifting it twice
i.e. lift lift (class . barysum)
*)

Definition quot_sum_compat {I: BInterval.type} {A: Baryspace.type I} (be: BEquiv) : Prop := 
    ∀ (x y x' y': A) (p: I), (R be) x x' -> (R be) y y' -> (R be) (barysum p x y) (barysum p x' y').

Definition quot_sum_part {I: BInterval.type} {A: Baryspace.type I} (be: BEquiv) (p: I): 
  (A -> A -> Qs be):=
    fun a1 a2 => (class (Qs be)) (barysum p a1 a2).

Arguments quot_sum_part (I) (A): clear implicits.

Lemma quot_sum_part1_compat {I: BInterval.type} {A: Baryspace.type I}
  (be: BEquiv) (p: I): 
    compatible _ _ (R be) (quot_sum_part I A be p). 
Proof.
unfold compatible. 
intros. apply functional_extensionality. intros. 
unfold quot_sum_part. unfold quot_sum_compat in H. 
apply quo_comp. apply (Compat be). apply H. destruct (Equiv be). 
apply H0. 
Qed.

Definition quot_sum_lift1 {I: BInterval.type} {A: Baryspace.type I} (be: BEquiv) (p: I): 
    (Qs be) -> A -> (Qs be)  := 
      quo_lift _ (quot_sum_part I A be p) (quot_sum_part1_compat be p).

Definition quot_sum_part2 (I: BInterval.type) (A: Baryspace.type I) 
    (be: BEquiv) (p: I) 
    (ac: (Qs be)): A -> (Qs be) := 
        (quot_sum_lift1 be p) ac.

Lemma quot_sum_part2_compat {I: BInterval.type} {A: Baryspace.type I} 
  (be: BEquiv) (p: I) (ac: Qs be): 
    compatible _ _ (R be) (quot_sum_part2 I A be p ac). 
Proof.
unfold compatible.
intros. 
unfold quot_sum_part2. 
unfold quot_sum_lift1. unfold quot_sum_part. specialize (quo_surj _ _ _ (Qs be) ac) as Hs.
destruct Hs. rewrite H0. 
rewrite (quo_lift_prop _ _ _ (Qs be) (A->(Qs be)) _ (quot_sum_part1_compat be p)). 
unfold quot_sum_part. apply quo_comp. apply (Compat be). 
- specialize (Equiv be) as He. destruct He. apply H1. 
- apply H.
Qed.

Arguments BEquiv (I) (A): clear implicits.

Definition quotBarysum {I: BInterval.type} {A: Baryspace.type I} 
    (be: BEquiv I A) (p: I): 
      (Qs be) -> (Qs be) -> (Qs be) := 
        fun xc => quo_lift _ (quot_sum_part2 I A be p xc) (quot_sum_part2_compat be p xc).

(*
The barycentric sum on the quotient space has the property that
[x] +_r [y] = [x +_r y]
*)

Lemma quotBarysum_corrresponds {I: BInterval.type} {A: Baryspace.type I}
  (be: BEquiv I A) (p: I) (a b: A):
    (Qs be) (barysum p a b) = quotBarysum be p (Qs be a) (Qs be b).
Proof.
unfold quotBarysum. unfold quot_sum_part2. unfold quot_sum_lift1. unfold quot_sum_part. 
rewrite (quo_lift_prop _ _ _ (Qs be) (Qs be) _ (quot_sum_part2_compat be p (Qs be a))). 
unfold quot_sum_part2. unfold quot_sum_lift1. unfold quot_sum_part.
rewrite (quo_lift_prop _ _ _ (Qs be) (A->(Qs be)) _ (quot_sum_part1_compat be p)). 
unfold quot_sum_part. reflexivity.
Qed.

Definition quot_add0 {I: BInterval.type} {A: Baryspace.type I}
 (be: BEquiv I A): ∀ (ac bc: Qs be),
    quotBarysum be 0 ac bc = ac.
Proof. 
intros.
specialize (quo_surj _ _ _ (Qs be) ac) as H1.
specialize (quo_surj _ _ _ (Qs be) bc) as H2.
destruct H1, H2. rewrite H H0. 
rewrite <- quotBarysum_corrresponds. rewrite barysum0.
reflexivity.
Qed.

Definition quot_addid {I: BInterval.type} {A: Baryspace.type I} (be: BEquiv I A): 
  ∀ (ac: Qs be) (p: I),
    quotBarysum be p ac ac = ac.
Proof. 
intros.
specialize (quo_surj _ _ _ (Qs be) ac) as H1.
destruct H1. rewrite H. 
rewrite <- quotBarysum_corrresponds. rewrite barysumid.
reflexivity.
Qed.

Definition quot_addinv {I: BInterval.type} {A: Baryspace.type I}
  (be: BEquiv I A): ∀ (ac bc: Qs be) (p: I),
    quotBarysum be p ac bc = quotBarysum be (inv p) bc ac.
Proof.
intros.
specialize (quo_surj _ _ _ (Qs be) ac) as H1.
specialize (quo_surj _ _ _ (Qs be) bc) as H2.
destruct H1, H2. rewrite H H0. 
rewrite <- !quotBarysum_corrresponds. f_equal. 
apply barysuminv.
Qed.

Definition quot_addassoc {I: BInterval.type} {A: Baryspace.type I} 
  (be: BEquiv I A): ∀ (ac bc cc: Qs be) (p q r s: I),
    s = (meet p q) -> meet p (inv q) = meet r (inv s) ->  
    quotBarysum be p ac (quotBarysum be q bc cc) = 
      quotBarysum be s (quotBarysum be r ac bc) cc.
Proof.
intros.
specialize (quo_surj _ _ _ (Qs be) ac) as H2.
specialize (quo_surj _ _ _ (Qs be) bc) as H3.
specialize (quo_surj _ _ _ (Qs be) cc) as H4.
destruct H2, H3, H4. rewrite H1 H2 H3. 
rewrite <- !quotBarysum_corrresponds. f_equal. apply barysumassoc;
assumption.
Qed.

Definition quot_is_bary {I: BInterval.type} {A: Baryspace.type I} {be: BEquiv I A} := Baryspace_of.Build 
I (Qs be) (quotBarysum be) (quot_add0 be) (quot_addid be) (quot_addinv be) (quot_addassoc be). 

Definition SumSpace {I: BInterval.type} (A B: Baryspace.type I) := Baryspace_of.axioms_ I (sum_bary_bequiv A B).

Definition homomorphic {I: BInterval.type} {A B: Baryspace.type I}
  (phi: A -> B) : Prop := ∀ p x y, barysum p (phi x) (phi y) = phi (barysum p x y).

Definition sum_to_AB {I: BInterval.type} {A B X: Baryspace.type I} 
  (phi: Qs (sum_bary_bequiv A B) -> X) :  (A -> X).
