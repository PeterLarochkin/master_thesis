Require Import MC_CTL2.
Require Import List. Import ListNotations.
Require Import Lia.

(* Ltac solve_fV init_ := (*solve satisfies model (fV ?) (?st) problem *)
  repeat split;
  let pre := fresh "pre" in
  intro pre; 
  rewrite init_ in pre; 
  (discriminate)+auto
. *)
Ltac solve_fV init_ :=
  repeat split;
  let pre := fresh "pre" in
  intro pre;
  (
    compute in init_; 
    rewrite init_ in pre; 
    discriminate
  ) 
  +
  (
    repeat (
      (left; reflexivity) 
      + 
      (right; reflexivity) 
      + 
      right)
  ).

Ltac solve_fOr init_ tac1 tac2  := 
(left; solve [tac1 init_](*;progress auto*)) + (right; solve[ tac2 init_ ](*; progress auto*)) 
.

Ltac solve_fAnd tac1 tac2 init_ :=
split; [> tac1 init_ | tac2 init_].






Fixpoint make_disjucntion_for_state_to{A} (s2: A)(states_in: list A) := 
match states_in with
| head :: nil => s2 = head
| head :: tail => s2 = head \/ (make_disjucntion_for_state_to s2 tail)
| nil => False
end
.

Fixpoint make_prop{A B} (s1:A )( s2:B) (list_connections: list (A * (list B))):Prop := 
match list_connections with 
| (b1,b2)::nil => (s1 = b1 -> (make_disjucntion_for_state_to s2 b2))
| (b1,b2)::tail => (s1 = b1 -> (make_disjucntion_for_state_to s2 b2)) /\ (make_prop s1 s2 tail)
| nil => False  
end 
.
Definition to_Prop{A B}(list_connections: list (B * (list A))): B -> A -> Prop :=
(fun s1 s2 => make_prop s1 s2 list_connections).


Inductive   square' : Set :=  one_square' | two_square' | three_square' | four_square' .
Definition  trans_square' := to_Prop [
  (one_square', [two_square'; three_square';four_square']);
  (two_square', [two_square']);
  (three_square', [three_square']);
  (four_square', [four_square'])
].


Definition  label_square' := to_Prop [
(one_square', [0;1;2;3;5]);
(two_square', [1;3;4;5;6;12]); 
(three_square', [1;10;12]); 
(four_square', [2;12])].



Definition  serial_square': forall w:square', exists (v:square'), trans_square' w v.
intros.
case w.
eexists two_square';repeat split; intro;try discriminate;left;auto.
eexists two_square';repeat split; intro;try discriminate; auto.
eexists three_square';repeat split; intro;try discriminate; auto.
eexists four_square';repeat split; intro;try discriminate; auto.
Defined.

Definition init_square' := fun st => st = one_square'.
Definition model_square': sts :=  {| 
  state   := square'; 
  trans   := trans_square'; 
  init    := init_square'; 
  label   := fun a b => label_square' b a; 
  serial  := serial_square' 
|}.


Theorem F0: 
forall st: state model_square', 
(init model_square') st -> 
satisfies (model_square') (fV 5) st.
Proof.
  intro st.
  intro init_.
  solve_fV init_.
Defined.


(* Ltac solve_fAX init_ tac1 := 
  let next_state := fresh "next_state" in 
  intro next_state;
  let trans_to_new_state := fresh "trans_to_new_state" in 
  intro trans_to_new_state;
  compute in trans_to_new_state;
  repeat (
    let a := fresh "a" in
    let b := fresh "b" in
    destruct trans_to_new_state as (a&b);
    ((apply a in init_)+(apply b in init_));
    (
      lazymatch type of init_ with 
      | _ \/ _ => repeat(destruct init_ as [init_|init_])
      | _ => idtac
      end
    ));
  tac1 init_. *)

Ltac solve_fAX init_ tac1 := 
  let next_state := fresh "next_state" in 
  intro next_state;
  let trans_to_next_state := fresh "trans_to_next_state" in 
  intro trans_to_next_state;
  compute in trans_to_next_state;
  let rec loop conj_hyp init_ :=
    lazymatch type of conj_hyp with
    | _ /\ _ => 
      let a := fresh "a" in let b := fresh "b" in
      destruct conj_hyp as (a & b);
      (apply a in init_) + (apply b in init_) + (loop b)
    | _ => 
      idtac
    end
  in
  (* init_ is disj *)
  loop trans_to_next_state init_;
  repeat (
    lazymatch type of init_ with
    | _ \/ _  =>
      destruct init_ as [init_ | init_]
    | _ => 
      idtac
    end
  );
  tac1 init_
.


Theorem F2: 
forall st: state model_square', 
(init model_square') st -> 
satisfies (model_square') (fAX (fV 12)) st.
Proof.
intro st.
intro init_l.
compute.
solve_fAX init_l solve_fV.
Qed.

Theorem F1: 
forall st: state model_square', 
(init model_square') st -> 
satisfies (model_square') (fAX (fOr (fV 1) (fOr (fV 1) (fV 2)))) st.
Proof.
intro st.
intro init_l.
let sol := 
    let sol_or := 
    (fun init_ => solve_fOr init_ solve_fV solve_fV)
    in
    (fun init_ => solve_fOr init_ solve_fV sol_or)
in
solve_fAX init_l sol.
Qed.







