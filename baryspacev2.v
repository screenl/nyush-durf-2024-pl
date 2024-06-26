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
  destruct p1, p2. simpl. 
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
  intros. destruct p1, p2. simpl. 
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

(*
For every equivalence relation ~ on a barycentric space A on I
such that x ~ x' and y ~ y' implies x +_p y ~ x' +_p y'.
There is a barycentric space A / ~ on I.
*)

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

Axiom quotient : forall (T : Type) (eqv : T -> T -> Prop) (p: equiv T eqv), 
  (type_quotient T eqv p).

Arguments quo {T} {eqv} {Hequiv}.
Arguments class {T} {eqv} {Hequiv}.
Arguments quo_lift {T} {eqv} {Hequiv} _ {R}.

Check quo_lift.

Record BEquiv {I : Interval.type} {A : Baryspace.type I} := instBequiv{
  R : A -> A -> Prop;
  Equiv : equiv _ R;
  Compat : ∀ (x y x' y': A) (p: I), R x x' -> R y y' -> R (barysum p x y) (barysum p x' y');
  Qs := quotient A R Equiv
}.

(*
The barycentric sum on the quotient space A/~ is defined 
by composing the class function with the barycentric sum on A 
and then lifting it twice
i.e. lift lift (class . barysum)
*)

Definition quot_sum_compat {I: Interval.type} {A: Baryspace.type I} (be: BEquiv) : Prop := 
    ∀ (x y x' y': A) (p: I), (R be) x x' -> (R be) y y' -> (R be) (barysum p x y) (barysum p x' y').

Definition quot_sum_part {I: Interval.type} {A: Baryspace.type I} (be: BEquiv) (p: I): 
  (A -> A -> Qs be):=
    fun a1 a2 => (class (Qs be)) (barysum p a1 a2).

Arguments quot_sum_part (I) (A): clear implicits.

Lemma quot_sum_part1_compat {I: Interval.type} {A: Baryspace.type I}
  (be: BEquiv) (p: I): 
    compatible _ _ (R be) (quot_sum_part I A be p). 
Proof.
unfold compatible. 
intros. apply functional_extensionality. intros. 
unfold quot_sum_part. unfold quot_sum_compat in H. 
apply quo_comp. apply (Compat be). apply H. destruct (Equiv be). 
apply H0. 
Qed.

Definition quot_sum_lift1 {I: Interval.type} {A: Baryspace.type I} (be: BEquiv) (p: I): 
    (Qs be) -> A -> (Qs be)  := 
      quo_lift _ (quot_sum_part I A be p) (quot_sum_part1_compat be p).

Definition quot_sum_part2 (I: Interval.type) (A: Baryspace.type I) 
    (be: BEquiv) (p: I) 
    (ac: (Qs be)): A -> (Qs be) := 
        (quot_sum_lift1 be p) ac.

Lemma quot_sum_part2_compat {I: Interval.type} {A: Baryspace.type I} 
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

Definition quotBarysum {I: Interval.type} {A: Baryspace.type I} 
    (be: BEquiv I A) (p: I): 
      (Qs be) -> (Qs be) -> (Qs be) := 
        fun xc => quo_lift _ (quot_sum_part2 I A be p xc) (quot_sum_part2_compat be p xc).


(*
The barycentric sum on the quotient space has the property that
[x] +_r [y] = [x +_r y]
*)

Lemma quotBarysum_corrresponds {I: Interval.type} {A: Baryspace.type I}
  (be: BEquiv I A) (p: I) (a b: A):
    (Qs be) (barysum p a b) = quotBarysum be p (Qs be a) (Qs be b).
Proof.
unfold quotBarysum. unfold quot_sum_part2. unfold quot_sum_lift1. unfold quot_sum_part. 
rewrite (quo_lift_prop _ _ _ (Qs be) (Qs be) _ (quot_sum_part2_compat be p (Qs be a))). 
unfold quot_sum_part2. unfold quot_sum_lift1. unfold quot_sum_part.
rewrite (quo_lift_prop _ _ _ (Qs be) (A->(Qs be)) _ (quot_sum_part1_compat be p)). 
unfold quot_sum_part. reflexivity.
Qed.

Definition quot_add1 {I: Interval.type} {A: Baryspace.type I}
 (be: BEquiv I A): ∀ (ac bc: Qs be),
    quotBarysum be 1 ac bc = ac.
Proof. 
intros.
specialize (quo_surj _ _ _ (Qs be) ac) as H1.
specialize (quo_surj _ _ _ (Qs be) bc) as H2.
destruct H1, H2. rewrite H H0. 
rewrite <- quotBarysum_corrresponds. rewrite barysum1.
reflexivity.
Qed.

Definition quot_addid {I: Interval.type} {A: Baryspace.type I} (be: BEquiv I A): 
  ∀ (ac: Qs be) (p: I),
    quotBarysum be p ac ac = ac.
Proof. 
intros.
specialize (quo_surj _ _ _ (Qs be) ac) as H1.
destruct H1. rewrite H. 
rewrite <- quotBarysum_corrresponds. rewrite barysumid.
reflexivity.
Qed.

Definition quot_addinv {I: Interval.type} {A: Baryspace.type I}
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

Definition quot_addassoc {I: Interval.type} {A: Baryspace.type I} 
  (be: BEquiv I A): ∀ (ac bc cc: Qs be) (p q r s: I),
    p = s & r -> s = p | q -> q ⇒ p = s ⇒ r ->  
    quotBarysum be p ac (quotBarysum be q bc cc) = 
      quotBarysum be s (quotBarysum be r ac bc) cc.
Proof.
intros.
specialize (quo_surj _ _ _ (Qs be) ac) as H2.
specialize (quo_surj _ _ _ (Qs be) bc) as H3.
specialize (quo_surj _ _ _ (Qs be) cc) as H4.
destruct H2, H3, H4. rewrite H2 H3 H4. 
rewrite <- !quotBarysum_corrresponds. f_equal. apply barysumassoc;
assumption.
Qed.

Definition quot_is_bary {I: Interval.type} {A: Baryspace.type I} (be: BEquiv I A) := Baryspace_of.Build 
I (Qs be) (quotBarysum be) (quot_add1 be) (quot_addid be) (quot_addinv be) (quot_addassoc be). 


(* Definition quot_sum_compat {I: Interval.type} {A: Baryspace.type I} {eqv : A -> A -> Prop}
  {Hequiv : equiv A eqv} (qs: type_quotient A eqv Hequiv) : Prop := 
    ∀ (x y x' y': A) (p: I), eqv x x' -> eqv y y' -> eqv (barysum p x y) (barysum p x' y').

Definition quot_sum_part {I: Interval.type} {A: Baryspace.type I} {eqv : A -> A -> Prop}
  {Hequiv : equiv A eqv} (qs: type_quotient A eqv Hequiv) (p: I): (A -> A -> qs) :=
  fun a1 a2 => (class qs) (barysum p a1 a2).

Lemma quot_sum_part1_compat {I: Interval.type} {A: Baryspace.type I} {eqv : A -> A -> Prop}
  {Hequiv : equiv A eqv} {qs: type_quotient A eqv Hequiv} (p: I): 
    quot_sum_compat qs -> compatible _ _ eqv (quot_sum_part qs p). 
Proof.
unfold compatible. 
intros. apply functional_extensionality. intros. 
unfold quot_sum_part. unfold quot_sum_compat in H. 
apply quo_comp. apply H. apply H0. destruct Hequiv. 
apply r. 
Qed.


Definition quot_sum_lift1 {I: Interval.type} {A: Baryspace.type I} {eqv : A -> A -> Prop}
  {Hequiv : equiv A eqv} (qs: type_quotient A eqv Hequiv) (Hcomp: quot_sum_compat qs) (p: I): 
    qs -> A -> qs := 
      quo_lift _ (quot_sum_part qs p) (quot_sum_part1_compat p Hcomp).

Definition quot_sum_part2 {I: Interval.type} {A: Baryspace.type I} {eqv : A -> A -> Prop}
  {Hequiv : equiv A eqv} {qs: type_quotient A eqv Hequiv} (Hcomp: quot_sum_compat qs) (p: I) 
    (ac: qs): A -> qs := 
        (quot_sum_lift1 qs Hcomp p) ac.

Lemma quot_sum_part2_compat {I: Interval.type} {A: Baryspace.type I} {eqv : A -> A -> Prop}
  {Hequiv : equiv A eqv} {qs: type_quotient A eqv Hequiv} (Hcomp: quot_sum_compat qs) (p: I) (ac: qs): 
    compatible _ _ eqv (quot_sum_part2 Hcomp p ac). 
Proof.
unfold compatible.
intros. 
unfold quot_sum_part2. 
unfold quot_sum_lift1. unfold quot_sum_part. specialize (quo_surj _ _ _ qs ac) as Hs.
destruct Hs. rewrite H0. 
rewrite (quo_lift_prop _ _ _ qs (A->qs) _ (quot_sum_part1_compat p Hcomp)). 
unfold quot_sum_part. apply quo_comp. apply Hcomp. 
- destruct Hequiv. apply r. 
- apply H.
Qed.

Definition quotBarysum {I: Interval.type} {A: Baryspace.type I} {eqv : A -> A -> Prop} {Hequiv : equiv A eqv}
  {qs: type_quotient A eqv Hequiv} (Hcomp: quot_sum_compat qs): 
    (I -> qs -> qs ->qs) := 
      fun p xc => quo_lift _ (quot_sum_part2 Hcomp p xc) (quot_sum_part2_compat Hcomp p xc).

Lemma quotBarysum_corrresponds {I: Interval.type} {A: Baryspace.type I} {eqv : A -> A -> Prop} {Hequiv : equiv A eqv}
  {qs: type_quotient A eqv Hequiv} (Hcomp: quot_sum_compat qs) (p: I) (a b: A):
    qs (barysum p a b) = quotBarysum Hcomp p (qs a) (qs b).
Proof.
unfold quotBarysum. unfold quot_sum_part2. unfold quot_sum_lift1. unfold quot_sum_part. 
rewrite (quo_lift_prop _ _ _ qs (qs) _ (quot_sum_part2_compat Hcomp p (qs a))). 
unfold quot_sum_part2. unfold quot_sum_lift1. unfold quot_sum_part.
rewrite (quo_lift_prop _ _ _ qs (A->qs) _ (quot_sum_part1_compat p Hcomp)). 
unfold quot_sum_part. reflexivity.
Qed.

Definition quot_add1 {I: Interval.type} {A: Baryspace.type I} {eqv : A -> A -> Prop} {Hequiv : equiv A eqv}
  {qs: type_quotient A eqv Hequiv} (Hcomp: quot_sum_compat qs): ∀ (ac bc: qs),
    (quotBarysum Hcomp) 1 ac bc = ac.
Proof. 
intros.
specialize (quo_surj _ _ _ qs ac) as H1.
specialize (quo_surj _ _ _ qs bc) as H2.
destruct H1, H2. rewrite H H0. 
rewrite <- quotBarysum_corrresponds. rewrite barysum1.
reflexivity.
Qed.

Definition quot_addid {I: Interval.type} {A: Baryspace.type I} {eqv : A -> A -> Prop} {Hequiv : equiv A eqv}
  {qs: type_quotient A eqv Hequiv} (Hcomp: quot_sum_compat qs): ∀ (ac: qs) (p: I),
    (quotBarysum Hcomp) p ac ac = ac.
Proof. 
intros.
specialize (quo_surj _ _ _ qs ac) as H1.
destruct H1. rewrite H. 
rewrite <- quotBarysum_corrresponds. rewrite barysumid.
reflexivity.
Qed.

Definition quot_addinv {I: Interval.type} {A: Baryspace.type I} {eqv : A -> A -> Prop} {Hequiv : equiv A eqv}
  {qs: type_quotient A eqv Hequiv} (Hcomp: quot_sum_compat qs): ∀ (ac bc: qs) (p: I),
    (quotBarysum Hcomp) p ac bc = (quotBarysum Hcomp) (inv p) bc ac.
Proof.
intros.
specialize (quo_surj _ _ _ qs ac) as H1.
specialize (quo_surj _ _ _ qs bc) as H2.
destruct H1, H2. rewrite H H0. 
rewrite <- !quotBarysum_corrresponds. f_equal. 
apply barysuminv.
Qed.

Definition quot_addassoc {I: Interval.type} {A: Baryspace.type I} {eqv : A -> A -> Prop} {Hequiv : equiv A eqv}
  {qs: type_quotient A eqv Hequiv} (Hcomp: quot_sum_compat qs): ∀ (ac bc cc: qs) (p q r s: I),
    p = s & r -> s = p | q -> q ⇒ p = s ⇒ r ->  
    (quotBarysum Hcomp) p ac ((quotBarysum Hcomp) q bc cc) = (quotBarysum Hcomp) s ((quotBarysum Hcomp) r ac bc) cc.
Proof.
intros.
specialize (quo_surj _ _ _ qs ac) as H2.
specialize (quo_surj _ _ _ qs bc) as H3.
specialize (quo_surj _ _ _ qs cc) as H4.
destruct H2, H3, H4. rewrite H2 H3 H4. 
rewrite <- !quotBarysum_corrresponds. f_equal. apply barysumassoc;
assumption.
Qed.

Definition quot_is_bary {I: Interval.type} {A: Baryspace.type I} {eqv : A -> A -> Prop} {Hequiv : equiv A eqv}
  {qs: type_quotient A eqv Hequiv} (Hcomp: quot_sum_compat qs) := Baryspace_of.Build 
I qs (quotBarysum Hcomp) (quot_add1 Hcomp) (quot_addid Hcomp) (quot_addinv Hcomp) (quot_addassoc Hcomp). 
 *)

