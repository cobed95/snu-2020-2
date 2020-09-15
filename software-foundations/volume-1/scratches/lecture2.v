Inductive day : Type :=
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday.

Inductive foo : Type :=
| me
| you.

Definition exp1 : foo := me.

Compute (
match (match exp1 with me => monday | you => friday end) with 
| monday => 0
| tuesday => 1
| wednesday => 2
| thursday => 3
| friday => 4
| saturday => 5
| sunday => 6
end).

Check (foo -> day).

Check ((fun x : foo => 
match x with
| me => monday
| you => friday
end) : foo -> day).

Definition foo2day : foo -> day :=
    (fun x : foo => 
    match x with
    | me => monday
    | you => friday
    end).

Check (foo2day me).
Compute (foo2day me).
Compute (foo2day you).

Definition next_weekday (d : day) : day := 
    match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
    end.

Print next_weekday.

Definition andb : bool -> (bool -> bool) := 
    fun (b1: bool) =>
        fun (b2: bool) => 
            match b1 with
            | true => b2
            | false => false
            end.

Compute (andb true).
Compute (andb false).

Definition andbtuple (b : bool * bool) : bool :=
    match b with
    | (b1, b2) => 
        match b1 with
        | true => b2
        | false => false
        end
    end.