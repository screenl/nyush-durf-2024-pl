From Coq Require Import ssreflect ssrfun ZArith.
From HB Require Import structures.
Require Import Unicode.Utf8.
Require Import Bool.Bool.

HB.mixin Record CMonoid_of M := {
  id : M;
  add : M -> M -> M;
  addrA : associative add;
  addrC : commutative add;
  addl0 : left_id id add;
}.

HB.structure Definition Monoid := { M of CMonoid_of M }.
HB.instance Definition Z_CMonoid := CMonoid_of.Build Z
    0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.

Print Z_CMonoid.
(* 
HB.mixin Record JMonoid_of M := {
  zero : M;
  join : M -> M -> M;
  joinrA : associative join;
  joinrC : commutative join;
  joinl0 : left_id zero join;
}.

HB.structure Definition JMonoid := { M of JMonoid_of M }.

HB.mixin Record MMonoid_of M := {
  one : M;
  meet : M -> M -> M;
  meetrA : associative meet;
  meetrC : commutative meet;
  meetl0 : left_id one meet;
}.

HB.structure Definition MMonoid := { M of MMonoid_of M }.

HB.mixin Record Interval_of I of JMonoid_of I of MMonoid_of I:= {
  inv : I -> I;
  inv_inv : ∀ i, inv (inv i) = i;
  inv_de_morgan_l : ∀ p q, inv (join p q) = meet (inv p) (inv q);
}. *)

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
Infix "+" := add.
Infix "|" := join (at level 10).
Infix "&" := meet (at level 10).
Notation "!" := inv.

Definition impl {I : Interval.type} (p q: I) := (!p) | q.
Infix "⇒" := impl (at level 10).

HB.builders Context (I: Type) (f : Interval_of I).
  HB.instance Definition join_CMonoid := CMonoid_of.Build I zero join joinrA joinrC joinl0.
  HB.instance Definition meet_CMonoid := CMonoid_of.Build I one meet meetrA meetrC meetl1.
HB.end.

Theorem inv_de_morgan_r: ∀ {A: Interval.type} (p q: A), !(p & q) = (!p) | (!q).
Proof.
intros.
rewrite <- inv_inv. rewrite inv_de_morgan_l. rewrite! inv_inv. reflexivity.
Qed.

Lemma inv0isid: ∀ {I: Interval.type} (i:I), i & (!(0:I)) = i.
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

HB.mixin Record Baryspace_of A:= {
  I : Interval.type;
  barysum : I -> A -> A -> A;
  barysum1 : ∀ a b, barysum 1 a b = a;
  barysumid : ∀ a p, barysum p a a = a;
  barysuminv : ∀ a b p, barysum p a b = barysum (!p) b a;
  barysumassoc: ∀ a b c p q r s, 
    p = s & r -> s = p | q -> q ⇒ p = s ⇒ r ->  
      barysum p a (barysum q b c) = barysum s (barysum r a b) c;
}.

HB.structure Definition Baryspace := { A of Baryspace_of A}.

(*Example: 2-to-1 mux is convex algebra*)

Definition badd (p: bool) (a b: nat) := if p then a else b.

Lemma badd1: ∀a b, badd true a b = a.
Proof. auto. Qed.

Lemma baddid: ∀a p, badd p a a = a.
Proof. destruct p; auto. Qed.

Lemma baddinv: ∀a b p, badd p a b = badd (!p) b a.
Proof. destruct p; auto. Qed.

Lemma baddassoc: ∀ a b c p q r s,
  p = s && r -> s = p || q -> (!q) || p = (!s) || r ->
    badd p a (badd q b c) = badd s (badd r a b) c.
Proof.
destruct p; auto;
destruct q; auto;
destruct s; auto;
destruct r; simpl; intros; auto;
discriminate. Qed.

HB.instance Definition badd_is_bary := Baryspace_of.Build
nat bool badd badd1 baddid baddinv baddassoc.

(*P is P-barycentric ?*)

Definition P_add_P {I : Interval.type} (p a b: I) := (a & p) | (b & (!p)).

Lemma P_add_P_1 {I : Interval.type} (a b: I): P_add_P 1 a b = a.
Proof.
intros. unfold P_add_P. rewrite meetrC. rewrite <- inv_0_1. rewrite (meetrC b). 
rewrite meetl1. Abort.

Lemma P_add_P_id {I : Interval.type} (a p: I): P_add_P p a a = a.
Proof.
intros. unfold P_add_P. Abort.

(* HB.instance Definition P_is_P_barycentric {I : Interval.type} := 
  Baryspace_of.Build I I P_add_P . 
  
  This does not work.
  
  *)





