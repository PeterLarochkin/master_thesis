Require Import MC_CTL2.
Require Import List. Import ListNotations.
Require Import Lia.


Definition from_trans_to_Prop{A}(list_connections: list (A*A)): A -> A -> Prop :=
(fun s1 s2 =>
  let fix make_prop (list_connections: list (A*A)):Prop :=
    match list_connections with 
    | (b1,b2)::nil => (s1 = b1 -> (s2 = b2))
    | (b1,b2)::tail => (s1 = b1 -> (s2 = b2)) /\ (make_prop tail)
    | nil => False
    end in 
  make_prop list_connections).

Definition from_label_to_Prop{A}(list_label: list (A*nat)):nat -> A -> Prop:=
  (fun v s =>
    let fix make_prop (list_label: list (A*nat)):Prop :=
      match list_label with 
      | (b,n)::nil => (s = b -> v = n)
      | (b,n)::tail => (s = b -> v = n) /\ (make_prop tail)
      | nil => False
      end in 
    make_prop list_label).

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

(* FIVE STATES *)
Inductive   fifth : Set :=  one_fi | two_fi | three_fi | four_fi| five_fi.
Definition  trans_fifth := from_trans_to_Prop3 [
  (one_fi, [two_fi]);
  (two_fi, [three_fi; four_fi]);
  (three_fi, [four_fi]);
  (four_fi, [five_fi]); 
  (five_fi, [one_fi])
].

Definition  label_fifth := from_label_to_Prop3 [(one_fi, [0]); (two_fi, [0]); (three_fi, [0]); (four_fi, [0; 1; 2]); (five_fi, [0])].

Definition  serial_fifth: forall w:fifth, exists (v:fifth), trans_fifth w v.
intro; case w.
eexists two_fi; compute; repeat split; intro; discriminate.
eexists four_fi; compute. repeat split. intro. discriminate. intro. right. auto.
intro; discriminate.
intro; discriminate.
eexists four_fi; compute. repeat split. intro. discriminate.
intro. discriminate.
intro. discriminate.
intro. discriminate.
eexists five_fi; compute. repeat split; intro; discriminate.
eexists one_fi; compute. repeat split; intro; discriminate.
Defined.


Definition init_fifth := from_init_to_Prop [one_fi].
Definition model_fifth: sts :=  {| 
  state   := fifth; 
  trans   := trans_fifth; 
  init    := init_fifth; 
  label   := label_fifth; 
  serial  := serial_fifth 
|}.

Ltac test_ltb_m_n' m n:=
assert (m < n);progress auto
.

Goal forall A B C:Prop, ((A->B)/\(A->C)) <->(A-> (B/\C)).
intros.
split.
intros.
destruct H.
split.
apply H in H0. auto.
apply H1 in H0. auto.
intros.
split.
intro. apply H in H0. destruct  H0.
auto.
intro.
apply H in H0.
destruct H0.
auto.
Qed.




Ltac SOLVE_FV' init_l := (*solve satisfies model (fV ?) (?st) probleb *)
  lazymatch type of init_l with 
  | _ = _ =>
    repeat split;
    let pre := fresh "pre" in
    intro pre; 
    rewrite init_l in pre;
    let rec loop_through_disj := 
      lazymatch goal with 
      | |- _ \/ _ => ((left; progress auto)) + (right; loop_through_disj)
      | _ => (auto;try discriminate)
      end
    in
    loop_through_disj
  | _ => repeat split; intro ; auto
  end
.

Theorem F2_AR: forall st: state model_fifth, 
(init model_fifth) st -> 
satisfies (model_fifth) (fAR (fV 0) (fV 0)) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l. compute in init_l.
  let path_pi := fresh "path_pi" in
  intro path_pi.
  let is_path_pi := fresh "is_path_pi" in
  intro is_path_pi.
  let first_state := fresh "first_state" in
  intro first_state.
  let nth_of_path := fresh "nth_of_path" in
  intro nth_of_path.
  left.
  {
    induction nth_of_path.
    {
      eexists 0.
      lia.
      rewrite init_l in first_state.
      SOLVE_FV' first_state.
    }
    {
      induction IHnth_of_path as [h1 h2 h3];
      eexists h1;[  auto|
      destruct (path_pi h1);
      SOLVE_FV' (path_pi h1)]. 
    }  
  }
  (* right.
  {
    destruct (path_pi nth_of_path);
    SOLVE_FV' (path_pi nth_of_path).
  } *)
Admitted.

Theorem F2_IMP: forall st: state model_fifth, 
(init model_fifth) st -> 
satisfies (model_fifth) (fImp (fV 1) (fV 0)) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l. compute in init_l.
  compute.
  intro.
  repeat (split;try(intro; auto)).
Defined.





Inductive   square : Set :=  one_square | two_square | three_square | four_square.
Definition  trans_square := from_trans_to_Prop3 [
  (one_square, [two_square]);
  (two_square, [three_square]);
  (three_square, [four_square]);
  (four_square, [one_square])
].

Definition  label_square := from_label_to_Prop3 [
  (one_square, [0]);
  (two_square, [0]); 
  (three_square, [0;1;2]); 
  (four_square, [2])].

Definition  serial_square: forall w:square, exists (v:square), trans_square w v.
intro; case w;
[
  eexists two_square |
  eexists three_square |
  eexists four_square |
  eexists one_square 
];repeat split;intro;discriminate.
Defined.


Definition init_square := from_init_to_Prop [one_square].
Definition model_square: sts :=  {| 
  state   := square; 
  trans   := trans_square; 
  init    := init_square; 
  label   := label_square; 
  serial  := serial_square 
|}.



Ltac SOLVE_AX2'' init_l solve_subformula1 := 
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
solve_subformula1 init_l.

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
Ltac SOLVE_AU2'' n max_of_state init_l solve_subformula1 solve_subformula2 := 
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
solve_AU max_of_state .

Ltac contradict_FV sat_hyp init_l := 
repeat (
  let a := fresh "a" in 
  let b := fresh "b" in 
  destruct sat_hyp as (a&b);
  (apply a in init_l) + (apply b in init_l); discriminate
).

Ltac contradict_FV' sat_hyp := 
(* repeat (
  let a := fresh "a" in 
  let b := fresh "b" in 
  destruct sat_hyp as (a&b);
  (apply a in init_l) + (apply b in init_l); discriminate
) *)
auto
.

Theorem F2_AU': forall st: state model_square, 
(init model_square) st -> 
satisfies (model_square) (fAU ((fV 0)) ((fV 1))) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l.
  let fv := fun init_ => SOLVE_FV' init_ 
  in
  SOLVE_AU2'' 2 4 init_l fv fv.
Defined.

Theorem cl(n m :nat)(H:n<>m):forall A:Prop, (A -> n = m) -> ~ A.
Proof.
  intros.
  compute.
  intros.
  apply H0 in H1.
  contradiction.
Qed.


Ltac SOLVE_FV'' init_l := (*solve satisfies model (fV ?) (?st) probleb *)
  lazymatch type of init_l with 
  | _ = _ =>
    (repeat split);
    let pre := fresh "pre" in
    intro pre; 
    rewrite init_l in pre;
    let rec loop_through_disj := 
      lazymatch goal with 
      | |- _ \/ _ => ((left; progress auto)) + (right; loop_through_disj)
      | _ => (auto;try discriminate)
      end
    in
    loop_through_disj
  | _ => repeat split; intro ; auto
  end
.


Ltac solve_fV init_ := (*solve satisfies model (fV ?) (?st) problem *)
  repeat split;
  let pre := fresh "pre" in
  intro pre; 
  rewrite init_ in pre; 
  (discriminate)+auto
.

Ltac solve_fOr tac1 tac2 init_ := 
(left; progress tac1 init_) + (right; progress tac2 init_) 
.


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

Theorem F1_And: 
forall st: state model_square, 
st = three_square-> 
satisfies (model_square) (fAnd (fAnd (fV 1) (fV 0))(fAX (fV 2))) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l. compute in init_l.
  let tac1 := fun init_ => solve_fAnd solve_fV solve_fV init_ in
  let tac2 := fun init_ => solve_fAX solve_fV init_ in
  solve_fAnd tac1 tac2 init_l.
  split;[
    solve_fV init_l 
    |
    solve_fV init_l 
  ].
  solve_fAnd solve_fV solve_fV init.
  let tac1 := fun init => solve_fAnd solve_fV solve_fV init in 
  let tac2 := fun init => solve_fAX solve_fV init in 
  solve_fAnd (tac1) (tac2) init_l.

  let tac2 := fun init_ => solve_fAX init_ solve_fV
  in
  solve_fOr init_l solve_fV tac2.
  compute in init_l.
  right.
  solve_fV init_l.
Defined.

  













Theorem F1_AR: 
forall st: state model_square, 
(init model_square) st -> 
satisfies (model_square) (fAR ((fV 1)) ((fV 0))) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l.
  (* compute. *)
  let path_pi := fresh "path_pi" in
  intro path_pi.
  let is_path_pi := fresh "is_path_pi" in
  intro is_path_pi.
  let first_state := fresh "first_state" in
  intro first_state.
  
  (* compute. *)
  intro n.
  induction n.








  {
    right.
    rewrite init_l in first_state.
    let solve_subformula1 := fun init_ => SOLVE_FV' init_ 
    in
    solve_subformula1 first_state.
  }
  {
    compute.
    left.
    eexists n.
    lia.
    split.
    
    (* compute. *)
    destruct IHn as [IHn | IHn].
    {
      compute.
      left.
      destruct IHn as [m' leq_m_n sat_hyp].
      eexists m'. 
      lia.
      auto.
    }
    {

      compute in IHn.

      destruct IHn.
      destruct H0.
      destruct H1.
      apply cl in H2.
      2:auto.
      pose proof (is_path_pi n).
      compute in H3.
      destruct H3.
      destruct H4.
      destruct H5.
      destruct (path_pi n).
      pose proof (H3 eq_refl).
      right.
      SOLVE_FV' H7.
      pose proof (H4 eq_refl).
      right.
      SOLVE_FV' H7.
      pose proof (H1 eq_refl).
      destruct H7.
      pose proof (H5 eq_refl).
      assert (n=0 \/ n >0). lia.
      assert (n>0 -> S (n - 1) = n). lia.
      destruct H9.
      right. rewrite H9.
      rewrite init_l in first_state.
      pose proof (is_path_pi 0).
      destruct H11. apply H11 in first_state.
      SOLVE_FV' first_state.
      apply H10 in H9.
      
      pose proof (is_path_pi ((n-1))).
      destruct H11.
      destruct H12.
      destruct H13.
      destruct (path_pi (n - 1)).
      pose proof (H11 eq_refl).
      rewrite H9 in H15.
      pose proof (is_path_pi n).
      destruct H16.
      destruct H17.
      apply H17 in H15. rewrite H8 in H15.
      discriminate.
      pose proof (H12 eq_refl).
      rewrite H9 in H15.
      left.
      eexists n.
      lia.
      SOLVE_FV' H15.
      pose proof (H13 eq_refl).
      rewrite H9 in H15.
      destruct H13.
      left.
      exists n. lia.
      
      
      
      
      compute.
      eexists n.
      lia.
      compute.
      SOLVE_FV' H7.

      right.
      compute.
      auto.
    }
  }
Qed.