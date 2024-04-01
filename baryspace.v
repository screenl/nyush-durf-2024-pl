From HB Require Import structures.
From Coq Require Import ssreflect ZArith.

HB.mixin Record IntervalOf A := {
    one : A;
    zero : A;
    inv : A -> A;
    mul : A -> A -> A;
    mulrA : forall x y z, mul x (mul y z) = mul (mul x y) z;
    mulrC : forall x y, mul x y = mul y x;
    mul1r : forall x, mul one x = x;
    mul0r : forall x, mul zero x = zero;
    inv10 : inv zero = one;
    invinv : forall x, inv (inv x) = x;
}.


HB.structure Definition IntervalStructure := { A of IntervalOf A }.

Notation "0" := zero.
Notation "1" := one. 
Infix "*" := mul.
