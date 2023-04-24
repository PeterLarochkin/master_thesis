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
(four_square', [ 2;12])].



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


Ltac unsplit H1 H2 H12 :=
lazymatch type of H1 with
| ?t1 => 
  lazymatch type of H2 with 
  | ?t2 => 
    assert (H12: t1 /\ t2);
    [
      split; [
        apply H1 
        |
        apply H2
      ]
      | 
      idtac
    ]
  end
end  
.



Ltac next_state_gen i is_path_pi first_state :=
  let is_path_pi_i := fresh "is_path_pi_i" in
  pose proof (is_path_pi i) as is_path_pi_i;
  compute in is_path_pi_i;
  let a := fresh "a" in
  let b := fresh "b" in
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
  loop is_path_pi_i first_state;
  repeat (
    lazymatch type of first_state with
    | _ \/ _  =>
      destruct first_state as [first_state | first_state]
    | _ => 
      idtac
    end
  ).
  Theorem usefull4: forall m n, S m = n -> m = n - 1.
  lia.
  Defined.
  Definition usefull: forall m n:nat, S m <= n -> S m = n \/ S m <= n - 1.
  lia.
  Defined. 
  
  Definition usefull2: forall m n:nat, S m = S n -> m = n .
  lia.
  Defined.
  Definition usefull3: forall m n:nat, m <= n -> m - 1 <= n - 1.
  lia.
  Defined.
Ltac proof_ex_sat i seq tac1 tac2:= 
  eexists i; compute; [
  let m := fresh "m" in intro m; 
  let lt_m := fresh "lt_m" in intro lt_m;
  let a := fresh "a" in
  let b := fresh "b" in
  destruct seq as (a&b);
  let rec loop i sequence lt_m := 
    lazymatch type of sequence with 
    | _ /\ _ =>
        let head := fresh "head" in
        let tail := fresh "tail" in
        destruct sequence as (head & tail);
        apply usefull in lt_m;destruct lt_m as [lt_m| lt_m]; compute in lt_m; [
          apply usefull4 in lt_m; compute in lt_m ;rewrite lt_m;
          tac1 head
          |
          (loop (i-1) tail lt_m)
        ] 
    | _ => 
          apply usefull in lt_m;destruct lt_m as [lt_m| lt_m]; compute in lt_m; [
          apply usefull4 in lt_m; compute in lt_m ;rewrite lt_m;
          tac1 sequence
          |
          (lia)
        ]
    end
    in
    loop i b lt_m
    | 
    let a := fresh "a" in
    let b := fresh "b" in
    destruct seq as (a&b);
    tac2 a
  ].

Ltac loop1 i n is_path_pi last_stop prev_acc (*write_here*) tac1 tac2 :=
  (
    tryif (assert (i=n); [solve [lia] | auto])
    then 
      (* assert(write_here:=prev_acc) *)
      fail
    else
      let new := fresh "first_state" in
      assert(new:=last_stop);
      next_state_gen i is_path_pi new;
      (* let new_acc := fresh "new_acc" in *)
      let H := fresh "H" in
      unsplit new prev_acc H;
      (solve [(proof_ex_sat i prev_acc tac1 tac2)]) +
      (loop1 (i+1) n is_path_pi new H (*write_here*) tac1 tac2)
  ).

Ltac solve_fAU n init_l tac1 tac2:= 
let pi := fresh "pi" in
intro pi;
let is_path_pi := fresh "is_path_pi" in
intro is_path_pi;
let first_state := fresh "first_state" in
intro first_state;
rewrite init_l in first_state;
let acc := fresh "seq" in
loop1 0 n is_path_pi first_state first_state (*acc*) tac1 tac2
.

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

Ltac solver n init_l := 
  let rec applicator f  :=
    lazymatch f with
    | fAX ?f_1 => 
      fun init_ => 
        let tac_1 := (applicator f_1) in 
        solve_fAX init_ tac_1
    | fOr ?f_1 ?f_2 => 
      fun init_ => 
        let tac_1 := (applicator f_1) in
        let tac_2 := (applicator f_2) in 
        solve_fOr init_ tac_1 tac_2
    | fAnd ?f_1 ?f_2 => 
        fun init_ => 
          let tac_1 := (applicator f_1) in
          let tac_2 := (applicator f_2) in 
          solve_fAnd init_ tac_1 tac_2    
    | fAU ?f_1 ?f_2 => 
          fun init_ => 
            let tac_1 := (applicator f_1) in
            let tac_2 := (applicator f_2) in 
            solve_fAU n init_ tac_1 tac_2    
    | fV ?n => (fun init_ => solve_fV init_) 
    end in 
lazymatch goal with
| [|- satisfies ?model_ ?f ?state_] => 
  lazymatch f with
  | fAX ?f_1 => 
    let tac1 := applicator f_1 in
    solve_fAX init_l tac1
  | fOr ?f_1 ?f_2 => 
    let tac1 := applicator f_1 in
    let tac2 := applicator f_2 in
    solve_fOr init_l tac1 tac2
  | fAnd ?f_1 ?f_2 => 
    let tac1 := applicator f_1 in
    let tac2 := applicator f_2 in
    solve_fAnd init_l tac1 tac2
  | fAU ?f_1 ?f_2 => 
    let tac1 := applicator f_1 in
    let tac2 := applicator f_2 in
    solve_fAU n init_l tac1 tac2
  | fV ?n => solve_fV init_l 
  end 
end.

Goal  
forall st: state model_square', 
(init model_square') st -> 
satisfies (model_square') (fAX (fOr (fV 1) (fOr (fV 1) (fV 2)))) st.
Proof.
intro st.
intro init_l.
solver 6 init_l.
Defined.
