Require Import MC_CTL2.
Require Import List. Import ListNotations.
Require Import Lia.
(* Print and. *)
Ltac solve_fV init_ := (*solve satisfies model (fV ?) (?st) problem *)
  repeat split;
  let pre := fresh "pre" in
  intro pre; 
  rewrite init_ in pre; 
  (discriminate)+auto
.

Ltac solve_fOr tac1 tac2 init_ := 
(left; progress tac1 init_;progress auto) + (right; progress tac2 init_; progress auto) 
.

Goal True.
repeat fail.

Ltac solve_fAX tac1 init_l := 
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



Ltac through_edges m is_path_pi first_state :=
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
        ((compute in a; apply a in first_state)+(apply b in first_state));
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
loop_to_needed_m 0 m.

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



Ltac right_case i H is_path_pi first_state tac:= 
  through_edges i is_path_pi first_state;
  right;
  (* rewrite init_l in first_state; *)
  compute in H;
  rewrite H;
  tac first_state
.
Ltac left_case i is_path_pi first_state init_l tac:= 
  left;
  (* rewrite init_l in first_state; *)
  
  eexists i;[
    lia 
    |
    compute;
    through_edges i is_path_pi first_state;
    tac first_state
  ] 
.

Theorem us:forall {model:sts}, forall st:state model, exists st': state model, st = st'.
Proof.
  intros.
  eexists st.
  auto.
Qed.

Theorem  su(k:nat): forall n, n > k -> n = S k \/ n > S k.
Proof.
  lia. 
Qed.

Theorem si (n:nat):n=0 \/ n >0 .
Proof.
  lia.
Qed.



Definition from_trans_to_Prop3{A}(list_connections: list (A * (list A))): A -> A -> Prop :=
(fun s1 s2 =>
  let fix make_disjucntion_for_state_to (states_in: list A) := 
  match states_in with
  | head :: nil => s2 = head
  | head :: tail => s2 = head \/ (make_disjucntion_for_state_to tail)
  | nil => False
  end
  
  in
  let fix make_prop (list_connections: list (A * (list A))):Prop :=
    match list_connections with 
    | (b1,b2)::nil => (s1 = b1 -> (make_disjucntion_for_state_to b2))
    | (b1,b2)::tail => (s1 = b1 -> (make_disjucntion_for_state_to b2)) /\ (make_prop tail)
    | nil => False
    end in 
  make_prop list_connections).
Definition from_label_to_Prop3{A}(list_connections: list (A * (list nat))): nat -> A -> Prop :=
(fun s1 s2 =>
  let fix make_disjucntion_for_state_to (states_in: list nat) := 
  match states_in with
  | head :: nil => s1 = head
  | head :: tail => s1 = head \/ (make_disjucntion_for_state_to tail)
  | nil => False
  end
  in
  let fix make_prop (list_connections: list (A * (list nat))):Prop :=
    match list_connections with 
    | (b1,b2)::nil => (s2 = b1 -> (make_disjucntion_for_state_to b2))
    | (b1,b2)::tail => (s2 = b1 -> (make_disjucntion_for_state_to b2)) /\ (make_prop tail)
    | nil => False
    end in 
  make_prop list_connections).
Definition from_init_to_Prop{A}(list_init: list A):A->Prop :=
  (fun s =>
    let fix make_prop (list_init: list A):Prop :=
      match list_init with 
      | b::nil => s = b
      | b::tail => (s = b) \/ (make_prop tail)
      | nil => False
      end in 
    make_prop list_init) 
.
Inductive   square' : Set :=  one_square' | two_square' | three_square' | four_square' | five_square'.
Definition  trans_square' := from_trans_to_Prop3 [
  (one_square', [two_square'; three_square']);
  (two_square', [two_square'; three_square']);
  (three_square', [four_square']);
  (four_square', [five_square']);
  (five_square', [five_square'])
].

Definition  label_square' := from_label_to_Prop3 [
  (one_square', [0]);
  (two_square', [0;1]); 
  (three_square', [0]); 
  (four_square', [0;1]);
  (five_square', [2])].

Definition  serial_square': forall w:square', exists (v:square'), trans_square' w v.
intros.
case w.
eexists two_square';repeat split; intro;try discriminate;left;auto.
eexists two_square';repeat split; intro;try discriminate; auto.
eexists four_square';repeat split; intro;try discriminate; auto.
eexists five_square';repeat split; intro;try discriminate; auto.
eexists five_square';repeat split; intro;try discriminate; auto.
Defined.

Definition init_square' := from_init_to_Prop [one_square'].
Definition model_square': sts :=  {| 
  state   := square'; 
  trans   := trans_square'; 
  init    := init_square'; 
  label   := label_square'; 
  serial  := serial_square' 
|}.

Ltac solve_fAR init_l max_of_state tac1 tac2 := 
  let path_pi := fresh "path_pi" in
  intro path_pi;
  let is_path_pi := fresh "is_path_pi" in
  intro is_path_pi;
  let first_state := fresh "first_state" in
  intro first_state;
  rewrite init_l in first_state;
  let n :=  fresh "n" in
  intro n;
  (right; compute; solve [auto])+
  let H := fresh "H" in
  pose proof (si n) as H;
  destruct H as [H | H]; [
    right_case 0 H is_path_pi first_state tac2
    |
    
    let rec sol H i m :=
    tryif (let h:= fresh "h" in assert(h: i < m); [progress auto | auto])
    then
      ( (left_case i is_path_pi first_state init_l tac1;progress auto) +
      let H0 := fresh "H0" in
      pose proof (su i n H) as H0;
      destruct H0 as [H0 | H0]; [
        compute in H0;
        right_case (i+1) H0 is_path_pi first_state tac2
        | 
          sol H0 (i+1) m
      ])
    else 
      idtac
    in
    sol H 0 max_of_state
  ]
.




 
Theorem name'{A B:nat ->Prop}:(forall n:nat, (A n) /\ (B n) ) -> (forall k:nat, (B k) ).
Proof.
  intros.
  pose proof (H k).
  destruct H0.
  auto.
Qed.

Theorem name''{A B:nat ->Prop}:(forall n:nat, (A n) /\ (B n) ) -> (forall k:nat, (A k) ).
Proof.
  intros.
  pose proof (H k).
  destruct H0.
  auto.
Qed.

Theorem name{X}{k}{a:X}: forall (p: nat -> X), 
  (forall (n:nat) , p n = a -> p (S n) = a) -> 
  (p k = a) ->(forall d, d > k -> p d = a).
Proof.
  intros.
  induction d.
  induction k.
  lia.
  lia.
  pose proof (H d).
  assert (S d > k -> d > k \/ d = k).
  lia.
  apply H2.
  apply H3 in H1.
  destruct H1.
  apply IHd.
  apply H1.
  rewrite H1.
  auto.
Qed.

Theorem name'''{m:sts}: forall s: (state m), exists2 k, s = k & k = s.
intros.
eexists s.
auto.
Qed.
Theorem F1: 
forall st: state model_square', 
(init model_square') st -> 
satisfies (model_square') (fAR (fAX (fV 2))  ((fV 0))) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l.
  
  (* compute in init_l. *)
  (* let tac1 := fun init_ => solve_fAX solve_fV init_ in
  let tac2 := fun init_ => solve_fV init_ in
  solve_fAR init_l 4 tac1 tac2. *)
  let path_pi := fresh "path_pi" in
  intro path_pi;
  let is_path_pi := fresh "is_path_pi" in
  intro is_path_pi;
  let first_state := fresh "first_state" in
  intro first_state;
  rewrite init_l in first_state;
  let n :=  fresh "n" in
  intro n.
  
  
  (* destruct (path_pi n). *)
  (* 
  simple case 
  pose proof (name''' (path_pi n)).
  destruct H.
  destruct x. *)
  (* proof stuck
      compute in is_path_pi.
    pose proof( name' is_path_pi).
    compute in H0.
    pose proof( name'' H0).
    compute in H1.
    through_edges 1 is_path_pi first_state.
    pose proof( name path_pi H1 first_state).
    pose proof (H2 n).
    assert (n>0 -> n = 1 \/ n > 1).
    lia.
    apply H4 in H.
    destruct H.
    rewrite <- H in first_state.
    right.
    solve_fV first_state.
    apply H3 in H.
    right.
    solve_fV H. *)


  let H := fresh "H" in
  pose proof (si n) as H.
  destruct H as [H | H].
  {
    right_case 0 H is_path_pi first_state solve_fV.
  }
  {
    next_state_gen (0) is_path_pi first_state.
    {
      let H0 := fresh "H0" in
      pose proof (su 0 n H) as H0;
      destruct H0 as [H0 | H0].
      {
          right_case 0 H0 is_path_pi first_state solve_fV.
      }
      {
        let H00 := fresh "H0" in
        pose proof (su (0+1) n H0) as H00;
        destruct H00 as [H00 | H00].
        {
          next_state_gen (1) is_path_pi first_state.
          {
            right_case 1 H1 is_path_pi first_state solve_fV.
          }
          {
            right_case 1 H1 is_path_pi first_state solve_fV.
          }
        }
        {
          let H' := fresh "H0" in
          pose proof (su (0+1+1) n H1) as H';
          destruct H' as [H' | H'].
          {
            
            next_state_gen (1) is_path_pi first_state.
            assert (first_state':= first_state).
            next_state_gen (2) is_path_pi first_state.
            right_case (1+1+1) H2 is_path_pi first_state solve_fV.
            right_case (1+1+1) H2 is_path_pi first_state solve_fV.
            next_state_gen (2) is_path_pi first_state.
            right_case (1+1+1) H2 is_path_pi first_state solve_fV.
            (* left. eexists 2. lia.
            let tac1 := fun init_ => solve_fAX solve_fV init_ in 
            tac1 first_state. *)
          }
          {
            give_up.


          }


        }
      }
    }
        next_state_gen (0+1) is_path_pi first_state.
        {

        compute in is_path_pi.
        }
        {

        }
        
        {

        }
        {

        }

      }

    }
    {

    }








    (* let tac1 := fun init_ => solve_fAX solve_fV init_ in
    left_case 0 is_path_pi first_state init_l tac1. progress auto. *)
    let H0 := fresh "H0" in
    pose proof (su 0 n H) as H0;
    destruct H0 as [H0 | H0].
    {
      right_case (0+1) H0 is_path_pi first_state solve_fV.
    }
    {
      (* let tac1 := fun init_ => solve_fAX solve_fV init_ in
      left_case (0+1) is_path_pi first_state init_l tac1; progress auto. *)
      let H00 := fresh "H0" in
      pose proof (su (0+1) n H0) as H00;
      destruct H00 as [H00 | H00].
      {
        right_case (0+1+1) H1 is_path_pi first_state solve_fV.
      }
      {
        
        let H000 := fresh "H0" in
        pose proof (su (0+1+1) n H1) as H000;
        destruct H000 as [H000 | H000].
        {
          assert (first_state':= first_state).
          through_edges (3) is_path_pi first_state.
          right_case (3) H2 is_path_pi first_state solve_fV.
          right_case (3) H2 is_path_pi first_state solve_fV.
          right_case (3) H2 is_path_pi first_state solve_fV.
          through_edges (2) is_path_pi first_state'.
          left.
          eexists 2.
          lia.
          (* right_case (3) H2 is_path_pi first_state solve_fV. *)
          
          (* rewrite init_l in first_state; *)
          
          eexists i;[
            lia 
            |
            compute;
            through_edges i is_path_pi first_state;
            tac first_state
          ]. 
          let tac1 := fun init_ => solve_fAX solve_fV init_ in
          left_case (3) is_path_pi first_state init_l tac1.
          right_case (3) H2 is_path_pi first_state solve_fV.

        }
      
      }
    }

  }

Defined.

