From HB Require Import structures.
From Coq Require Import ssreflect ZArith.
Require Import Unicode.Utf8.

HB.mixin Record IntervalOf A := {
    one : A;
    zero : A;
    inv : A -> A;
    mul : A -> A -> A;
    mulrA : ∀ x y z, mul x (mul y z) = mul (mul x y) z;
    mulrC : ∀ x y, mul x y = mul y x;
    mul1r : ∀ x, mul one x = x;
    mul0r : ∀ x, mul zero x = zero;
    inv10 : inv zero = one;
    invinv : ∀ x, inv (inv x) = x;
}.


HB.structure Definition IntervalStructure := { A of IntervalOf A }.


Notation "0" := zero.
Notation "1" := one. 
Infix "*" := mul.
Notation "~" := inv (at level 100).


HB.mixin Record BaryspaceOf A := {
    I: IntervalStructure.type;
    barysum: I -> A -> A -> A;
    add0 : ∀ a b, barysum 0 a b = a;
    addid : ∀ a p, barysum p a a = a;
    addinv : ∀ a b p, barysum p a b = barysum (~p) b a;
    addassoc: ∀ a b c p q r s, 
        ((s = p*q) ∧ (p * (~q) = r * (~s))) ->  barysum p a (barysum q b c) = barysum s (barysum r a b) c;
}.

HB.structure Definition Baryspace := {A of BaryspaceOf A}.

Lemma inv01 {I: IntervalStructure.type}: ~(1:I) = 0.
rewrite <- invinv. rewrite inv10. reflexivity. Qed.

Lemma add1 {B: Baryspace.type} (a b: B): barysum 1 a b = b.
intros. rewrite addinv. rewrite inv01. apply add0. Qed.

