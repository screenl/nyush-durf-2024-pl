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

(*Barycentric Space*)

HB.mixin Record Baryspace_of (I : Interval.type) A := {
  barysum : I -> A -> A -> A;
  barysum1 : ∀ a b, barysum 1 a b = a;
  barysumid : ∀ a p, barysum p a a = a;
  barysuminv : ∀ a b p, barysum p a b = barysum (!p) b a;
  barysumassoc: ∀ a b c p q r s, 
    p = s & r -> s = p | q -> q ⇒ p = s ⇒ r ->  
      barysum p a (barysum q b c) = barysum s (barysum r a b) c;
}.

HB.structure Definition Baryspace I := { A of Baryspace_of I A}.

Lemma barysum0 {I : Interval.type} {B: Baryspace.type I} (a b: B): barysum 0 a b = b.
intros. rewrite barysuminv. rewrite <- inv_1_0. apply barysum1. 
Qed.

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
bool nat badd badd1 baddid baddinv baddassoc.

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
  
  This does not work with the current formulation.*)

(*Product of baryspaces is barycentric*)

Definition prodBarysum {I: Interval.type} {A B: Baryspace.type I} : (I->A*B->A*B->A*B) := 
  fun p p1 p2 => match p1 with
    | (a1,b1) => match p2 with
    | (a2,b2) => (barysum p a1 a2, barysum p b1 b2)
    end
  end.

Lemma prod_add1 {I: Interval.type} {A B: Baryspace.type I}: ∀ (p1 p2: A*B),
  prodBarysum 1 p1 p2 = p1.
Proof.
  intros.
  destruct p1. destruct p2. simpl. 
  rewrite !barysum1. reflexivity.
Qed.

Lemma prod_addid {I: Interval.type} {A B: Baryspace.type I}: ∀  (p1: A*B) (p:I),
  prodBarysum p p1 p1 = p1.
Proof.
  intros. destruct p1. simpl.
  rewrite !barysumid. reflexivity.
Qed.

Lemma prod_addinv {I: Interval.type} {A B: Baryspace.type I}: ∀ (p1 p2: A*B) (p:I) ,
  prodBarysum p p1 p2 = prodBarysum (!p) p2 p1.
Proof.
  intros. destruct p1. destruct p2. simpl. 
  rewrite <- !barysuminv. reflexivity.
Qed.

Lemma prod_addassoc {I: Interval.type} {A B: Baryspace.type I}: 
    ∀ (a b c: A*B) p q r s, 
    p = s & r -> s = p | q -> q ⇒ p = s ⇒ r ->  
      prodBarysum p a (prodBarysum q b c) = prodBarysum s (prodBarysum r a b) c.
Proof.
  intros. destruct a, b, c. simpl. 
  f_equal; apply barysumassoc; assumption. 
Qed.

HB.instance Definition prod_is_bary {I: Interval.type} {A B: Baryspace.type I} := Baryspace_of.Build
I (prod A B) prodBarysum prod_add1 prod_addid prod_addinv prod_addassoc.


Check Baryspace.on (prod nat nat).