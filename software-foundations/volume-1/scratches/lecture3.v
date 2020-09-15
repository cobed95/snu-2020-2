Notation "x && y" := (andb x y).

Check (negb true)
    : bool.

Compute negb true.

Print negb.

Inductive rgb : Type :=
    | red
    | green
    | blue.

Check red.
Check green.
Check blue.

Inductive color : Type :=
    | black
    | white
    | primary (p : rgb).

Check black.
Check white.
Check primary red.
Check primary green.
Check primary blue.

Check primary.
Compute primary.

Definition monochrome (c : color) : bool :=
    match c with
    | black => true
    | white => true
    | primary _ => false
    end.

Definition isred (c : color) : bool :=
    match c with
    | black => false
    | white => false
    | primary red => true
    | primary _ => false
    end.

Compute monochrome (primary blue).
Compute monochrome white.

Module Playground.
    Definition b : rgb := blue.
    Check b.
End Playground.

Definition b : bool := true.

Check Playground.b : rgb.
Check b : bool.

Module TuplePlayground.

Inductive bit : Type := 
    | B0
    | B1.

Check B0.
Check B1.

Inductive nybble : Type :=
    | bits (b0 b1 b2 b3 : bit).

Check bits B0 B0 B0 B0.
Check bits B0 B0 B0 B1.

Check (bits B1 B0 B1 B0)
    : nybble.

Check bits.

Definition all_zero (nb : nybble) : bool :=
    match nb with
        | bits B0 B0 B0 B0 => true
        | bits _ _ _ _ => false
    end.

Compute (all_zero (bits B1 B0 B1 B0)).
Compute (all_zero (bits B0 B0 B0 B0)).

End TuplePlayground.

Module NatPlayground.

Inductive nat : Type :=
    | O
    | S (n: nat).

Check (O : nat).
Check S O.
Check S (S (S (S (S O)))).

(* Below is an empty set *)
Inductive sylly : Type :=
    | A (n: sylly).

(* Calculus of Construction = Inductive + Function *)
(* Calculus of Inductive Contruction = Inductive + Function + CoInductive *)

Inductive nat' : Type :=
    | stop
    | tick (foo : nat').

Check stop.
Check tick stop.
Check tick (tick stop).

Definition pred (n : nat) : nat :=
    match n with
        | O => O
        | S n' => n'
    end.

Compute pred O.
Compute pred (S O).
Compute pred (S (S O)).

End NatPlayground.

Check O.
Check (S O).
Check (S (S O)).


Definition minustwo (n : nat) : nat :=
    match n with
        | O => O
        | S O => O
        | S (S n') => n'
    end.

Compute minustwo 0.