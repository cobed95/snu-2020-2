Compute (fix evenb (n: nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
    end) 11 .

(* Computation is either reducing fixpoint expressions or match expressions *)
(* fixpoint + match is turing complete *)

Definition evenb_verbose : nat -> bool :=
    (fix evenb_verbose (n: nat) : bool :=
        match n with
        | O => true
        | S O => false
        | S (S n') => evenb_verbose n'
        end).

Fixpoint evenb (n: nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
    end.

Print evenb.
Compute evenb 101.

(* Functions should be mathematically well-defined (should terminate) *)

Check(exists f: nat -> nat,
          forall n, if evenb n 
                    then 2 * (f n) = n
                    else f n = n * 3 + 1).

Module NatPlayground2.

Fixpoint plus (n: nat) (m: nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

Check(fix plus (n m : nat) : nat :=
    match n with
    | 0 => m
    | S n' => S (plus n' m)
    end).

Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O, _ => O
    | _, O => n
    | S n', S m' => minus n' m'
    end.

Fixpoint exp (base power : nat) : nat :=
    match power with
    | O => 1
    | S p => mult base (exp p)
    end.

End NatPlayground2.
