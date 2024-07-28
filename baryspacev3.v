From Coq Require Import ssreflect ssrfun ZArith.
From HB Require Import structures.
Require Import Unicode.Utf8.
Require Import Bool.Bool.

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

Lemma bracket_1: ∀ (I: BInterval.type) (r s: I), r <> 0 -> bracket 0 r s = 0.
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

Theorem barysum_2: ∀ (I: BInterval.type) (A: Baryspace.type I) 
  (x x' y y': A) (r s t: I), barysumI t r s <> 0 -> barysumI t r s <> 1 -> 
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
  rewrite H1.
  assert ((bracket (bracket t (! r) 1) 1 (! s)) = bracket t (!r) (!s)).
  {
    rewrite <- bracket_dist. rewrite (meetrC (!r) 1). rewrite !meetl1. reflexivity.
  }
  rewrite H2.
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
    rewrite meet_sum0 in H1. rewrite inv_bary_dist in H1. rewrite inv_inv in H1.
    rewrite joinrC in H1. rewrite join_sum1 in H1. rewrite <- inv_1_0 in H1. rewrite H1 in H3.
    assert (meet t s = meet (bracket t r s) (barysumI t r s)). symmetry. apply bracket_basic.
    rewrite H4 in H3. apply cancel in H3. rewrite <- (join_sum1 (I) (!r) (t)). rewrite joinrC. 
    rewrite join_sum1. apply H3. apply H.
  }
  rewrite H3. reflexivity.
Qed.

End BIntv.

