From Coq Require Import Arith Relations Program.
Require Import Unicode.Utf8.

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
        forall (x : T), (compose (quo_lift _ f Hf) class) x = f x;
    quo_surj : forall (c : quo), 
        exists x : T, c = class x
}.

Axiom quotient : forall (T : Type) (eqv : T -> T -> Prop) (p: equiv T eqv), 
    (type_quotient T eqv p).
