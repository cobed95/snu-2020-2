(* Programming = computing about data
Mathematics = reasoning about sets *)

(* Curry-Howard Isomorphism: proofs and programs have one-to-one correspondence *)

Definition plus_0_n_0 : forall n : nat, 0 + n = n :=
    fun n => @eq_refl nat n.
(* 
    for all n: nat, 0 + n = n) === 
    the set of all proofs for (for all natural numbers n, 0 + n is equal to n
    proving theorem === proving that the above set is not empty
                    === providing evidence 

*)

(* forall n : ... is a dependent function type *)
(* 
    forall quantification in math === dependent function space.

    f: A -> B               <-- Function type
    f: forall (n: A), B[n]  <-- Dependent function type
    
    Output type is dependent on input value.
    
    ex) Consider a dependent function (n: nat) -> vector of size n.
        Depending on n, the return type varies. 
        (0) -> vector of size 0.
        (10) -> vector of size 10.

    ex) mult_matrix :
            (n: nat) -> 
                (m: nat) -> 
                    (l: nat) -> 
                        matrix nat n m -> 
                            matrix nat m l -> 
                                matrix nat n l
*)

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
    (* Proof synthesis *)
    (* intentionally equal *)
    intros n. simpl. reflexivity.
Qed.

(* 
    intros n === fix n
    simpl === reduce expression

    Under condition Variable n : nat,
    Compute 0 + n computes to n,
    but Compute n + 0 does not.
    Because n is inevaluable.

    plus 0 n
    ===
    match 0 with
    | 0 => n
    | S n' => S (plus n' n)
    end

    Above expression can be further reduced 
    because first arg is 0 and can be matched

    but plus n 0 
    ===
    match n with
    | 0 => 0
    | S n' => S (plus n' 0)
    end

    will not be reduced.
*)


Print plus_0_n.

Print eq.
(* === forall (n : A), (forall m: B[n], C[n,m]) *)

Theorem plus_n_0 : forall n : nat, n + 0 = n.
Proof.
    (* We need a much more complex proof here, *)
    (* because plus(+) recurses on the first argument. *)
    (* provably equal *)
    intros. induction n.
    - simpl. reflexivity.
    - simpl. rewrite IHn. reflexivity.
Qed.

(*
    Above is equivalent to...
    (fun n: nat =>
        (fix F (n0 : nat) : n0 + 0 = N0 :=
            match n0 as n1 return (n1 + 0 = n1) with
            | 0 => eq_refl
            | S n1 => eq_ind_r (fun n2 : nat => S n2 = S n1) eq_refl (F n1)
            end) n))
*)