
Inductive AP: Set := 
| p: AP
.

Inductive form :=
| proposition: AP -> form
| and: form -> form -> form
| not: form -> form
| EX: form -> form
| AX: form -> form
| EU: form -> form -> form
| AU: form -> form -> form
.

Record model := MODEL {
  state  :> Type;
  trans  : state -> state -> Prop;
  label  : AP -> state -> Prop;
  serial : forall w:state, exists v, trans w v
}.



Module Check.

From Coq Require Export String.
Parameter MISSING:Type.
Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.



Ltac destruct_bool_and_rewrite b H1 H2 :=
  destruct b; [ rewrite H1; eauto | rewrite H2; eauto ].
End Check.


Require Import Nat. 
Require Import String.
Ltac reduce_and_try_to_solve := tryif simpl then fail else idtac "good".
Ltac la := 
  multimatch goal with
  (* | |- ?X = ?X => idtac "wow" *)
  | |- ?H = ?H => idtac "waw"
  | _ => fail
  end .

Ltac lo := 
match goal with
| |- context G [nat] => let x := context G [nat] in idtac x
end.  


Theorem easy: forall n:nat, n=n .
Proof.
  intros H.
  la.
  auto.
Qed.

Print Logic.not.
Locate "~".





Require Import CTL_def_copy.



