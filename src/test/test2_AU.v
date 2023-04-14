Require Import MC_CTL2.
Require Import List. Import ListNotations.
Require Import Lia.

Ltac solve_fV init_ := (*solve satisfies model (fV ?) (?st) problem *)
  repeat split;
  let pre := fresh "pre" in
  intro pre; 
  rewrite init_ in pre; 
  (discriminate)+auto
.

Ltac solve_fOr init_ tac1 tac2  := 
(left; progress tac1 init_;progress auto) + (right; progress tac2 init_; progress auto) 
.

Ltac solve_fAX init_l tac1 := 
  let next_state := fresh "next_state" in 
  intro next_state;
  let trans_to_new_state := fresh "trans_to_new_state" 
  in 
  intro trans_to_new_state;
  compute in trans_to_new_state;
  repeat (
    let a := fresh "a" in
    let b := fresh "b" in
    destruct trans_to_new_state as (a&b);
    ((apply a in init_l)+(apply b in init_l));
    (
      lazymatch type of init_l with 
      | _ \/ _ => repeat( destruct init_l as [init_l|init_l])
      | _ => idtac
      end
    ));
    tac1 init_l.

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



Ltac solve_AU n max_of_state init_l solve_subformula1 solve_subformula2 := 
let solve_AU max_of_state :=
    let path_pi := fresh "path_pi" in
    intro path_pi;
    let is_path_pi := fresh "is_path_pi" in
    intro is_path_pi;
    let first_state:= fresh "first_state" in
    intro first_state;
    compute;
    let (*rec*) sol_AU n :=
    (* tryif (let h:= fresh "h" in assert(h: n <= max_of_state); [progress auto | auto])
    then *)
    (
        eexists n (*n*); 
        [
            auto;
            let m := fresh "m" in
            let le_m := fresh "le_m" in
            intro m;
            intro le_m;
            (
            let rec solve_rec le_m := 
                apply usefull in le_m; (*compute in le_m;*)
                destruct le_m as [ le_m | le_m];
                [>
                (apply usefull2 in le_m) + lia (* for cases S m = 0*);
                rewrite init_l in first_state;
                try (rewrite <- le_m in first_state;
                solve_subformula1 first_state);
                let rec loop_to_needed_m i m :=
                    tryif (let h:= fresh "h" in assert(h: i < m); [progress auto | auto])
                    then 
                        let is_path_pi_i := fresh "is_path_pi_i" in
                        pose proof (is_path_pi i) as is_path_pi_i;
                        compute in is_path_pi_i;
                        repeat (
                            let a := fresh "a" in
                            let b := fresh "b" in
                            destruct is_path_pi_i as (a&b);
                            ((apply a in first_state)+(apply b in first_state));
                            (
                            lazymatch type of first_state with 
                            | _ \/ _ => (repeat destruct first_state as [first_state|first_state])
                            | _ => idtac
                            end
                            );
                            loop_to_needed_m (i + 1) m)
                    else 
                        idtac
                in
                lazymatch type of le_m with 
                | _ = ?k => loop_to_needed_m 0 k
                | _ => idtac
                end
                ;
                rewrite <- le_m in first_state;
                solve_subformula1 first_state
                
                |
                (compute in le_m;
                lia) +  
                (solve_rec le_m) + auto
                ]
            in
            (solve_rec le_m)
            )
            
        |
        auto;
        rewrite init_l in first_state;
        let rec loop_to_needed_m i m :=
            tryif (let h:= fresh "h" in assert(h: i < m); [progress auto | auto])
            then 
                let is_path_pi_i := fresh "is_path_pi_i" in
                pose proof (is_path_pi i) as is_path_pi_i;
                compute in is_path_pi_i;
                repeat (
                    let a := fresh "a" in
                    let b := fresh "b" in
                    destruct is_path_pi_i as (a&b);
                    ((apply a in first_state)+(apply b in first_state));
                    (repeat (
                    lazymatch type of first_state with 
                    | _ \/ _ => (destruct first_state as [first_state|first_state])
                    | _ => idtac
                    end
                    ));
                    loop_to_needed_m (i + 1) m)
            else 
                idtac
        in
        loop_to_needed_m 0 n;
        solve_subformula2 first_state
        ]
    )
    (* +
    sol_AU (n + 1)
    else 
    fail "solve_AU: with" n*)
    in 
    sol_AU n
in
solve_AU max_of_state.


Inductive square : Set :=  
| one_square 
| two_square
| three_square
| four_square 
| five_square
| six_square .
Definition  trans_square := to_Prop [
(one_square, [two_square; five_square]);
(two_square, [three_square; five_square]);
(three_square, [four_square] );
(four_square, [four_square]);
(five_square, [three_square; six_square]);
(six_square , [six_square])
].


Definition  label_square := to_Prop [
(one_square, [0]);
(two_square, [0]);
(three_square, [0]);
(four_square, [1]);
(five_square, [0]);
(six_square ,[1])
].

Definition  serial_square: forall w:square, exists (v:square), trans_square w v.
intros.
case w.
eexists two_square;repeat split; intro;try discriminate;left;auto.
eexists three_square;repeat split; intro;try discriminate;left;auto.
eexists four_square;repeat split; intro;try discriminate;left;auto.
eexists four_square;repeat split; intro;try discriminate;left;auto.
eexists three_square;repeat split; intro;try discriminate;left;auto.
eexists six_square;repeat split; intro;try discriminate;left;auto.
Defined.

Definition init_square := fun st => st = one_square.
Definition model_square: sts :=  {| 
  state   := square; 
  trans   := trans_square; 
  init    := init_square; 
  label   := fun a b => label_square b a; 
  serial  := serial_square 
|}.

Ltac unsplit H1 H2 H12 :=
lazymatch type of H1 with
| ?t1 => 
  lazymatch type of H2 with 
  | ?t2 => 
    assert (H12: t1 /\ t2)
  end
end  
.


Ltac next_state_gen i is_path_pi first_state :=
  let is_path_pi_i := fresh "is_path_pi_i" in
  pose proof (is_path_pi i) as is_path_pi_i;
  compute in is_path_pi_i;
  let a := fresh "a" in
  let b := fresh "b" in
  destruct is_path_pi_i as (a&b);
  ((compute in a; apply a in first_state)+(apply b in first_state));
  (repeat (
  lazymatch type of first_state with 
  | _ \/ _ => (destruct first_state as [first_state|first_state])
  | _ => idtac
  end
  )).

Ltac proof_ex_sat i seq tac1 tac2:= 
  eexists i; compute; [
  
  let m := fresh "m" in intro m; let lt_m := fresh "lt_m" in  intro lt_m;
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

Ltac loop1 i n is_path_pi last_stop prev_acc write_here tac1 tac2 :=
  (
    tryif (assert (i=n); [progress lia | auto])
    then 
      assert(write_here:=prev_acc)
    else
      let new := fresh "first_state" in
      assert(new:=last_stop)
      ;
      next_state_gen i is_path_pi new;
      let new_acc := fresh "new_acc" in
      let H := fresh "H" in
      unsplit new prev_acc H; auto;
      ((proof_ex_sat i prev_acc tac1 tac2);solve[auto]) +
      (loop1 (i+1) n is_path_pi new H write_here tac1 tac2)
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
loop1 0 n is_path_pi first_state first_state acc tac1 tac2
.
Theorem F1: 
forall st: state model_square, 
(init model_square) st -> 
satisfies (model_square) (fAU (fOr(fV 0)(fV 1)) (fAX (fV 1))) st.
Proof.
intro st.
intro init_l.
let tac2 := fun init_ => solve_fAX init_ solve_fV in
let tac1 := fun init_ => solve_fOr init_ solve_fV solve_fV in
solve_fAU 6 init_l tac1 tac2.
Defined.

Theorem F2: 
forall st: state model_square, 
(init model_square) st -> 
satisfies (model_square) (fAU (fAX (fOr (fV 0)(fV 1))) (fAX (fV 1))) st.
Proof.
intro st.
intro init_l.
let tac := fun init_ => solve_fOr init_ solve_fV solve_fV in
let tac1 := fun init_ => solve_fAX init_ tac in
let tac2 := fun init_ => solve_fAX init_ solve_fV in
solve_fAU 6 init_l tac1 tac2.
Defined.
