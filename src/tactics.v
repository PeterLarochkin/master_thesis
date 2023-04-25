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

Ltac solve_fAnd init_ tac1 tac2 :=
split; [> tac1 init_ | tac2 init_].

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
          (solve [tac1 head])
          |
          (loop (i-1) tail lt_m)
        ] 
    | _ => 
          apply usefull in lt_m;destruct lt_m as [lt_m| lt_m]; compute in lt_m; [
          apply usefull4 in lt_m; compute in lt_m ;rewrite lt_m;
          (solve [tac1 sequence])
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
    (solve [tac2 a])
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
(eexists 0; [lia | solve [tac2 first_state]] )
+
(let acc := fresh "seq" in
loop1 0 n is_path_pi first_state first_state (*acc*) tac1 tac2)
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
  solve [tac1 init_]
.

Ltac solver n init_l := 
  let rec applicator f  :=
    lazymatch f with
    | fAX ?f_1 => 
        let tac init_ := 
          let tac_1 := (applicator f_1) in 
          solve_fAX init_ tac_1
        in
        tac
    | fOr ?f_1 ?f_2 => 
        let tac init_ := 
          let tac_1 := (applicator f_1) in
          let tac_2 := (applicator f_2) in 
          solve_fOr init_ tac_1 tac_2
        in 
        tac
    | fAnd ?f_1 ?f_2 => 
        let tac init_ := 
          let tac_1 := (applicator f_1) in
          let tac_2 := (applicator f_2) in 
          solve_fAnd init_ tac_1 tac_2    
        in 
        tac
    | fAU ?f_1 ?f_2 => 
          let tac init_ := 
            let tac_1 := (applicator f_1) in
            let tac_2 := (applicator f_2) in 
            solve_fAU n init_ tac_1 tac_2
          in 
          tac
    | fV ?n => solve_fV
    end in 
lazymatch goal with
| [|- satisfies ?model_ ?f ?state_] => 
    let tac := applicator f in 
    tac init_l
end.