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




Inductive   square' : Set :=  one_square' | two_square' | three_square' | four_square'.
Definition  trans_square' := from_trans_to_Prop3 [
  (one_square', [two_square']);
  (two_square', [three_square']);
  (three_square', [four_square']);
  (four_square', [four_square'])
].

Definition  label_square' := from_label_to_Prop3 [
  (one_square', [3]);
  (two_square', [0;1]); 
  (three_square', [1]); 
  (four_square', [0;2;3])].

Definition  serial_square': forall w:square', exists (v:square'), trans_square' w v.
intros.
case w.
eexists two_square';repeat split; intro;try discriminate.
eexists three_square';repeat split; intro;try discriminate; auto.
eexists four_square';repeat split; intro;try discriminate; auto.
eexists four_square';repeat split; intro;try discriminate; auto.
Defined.


Definition init_square' := from_init_to_Prop [one_square'].
Definition model_square': sts :=  {| 
  state   := square'; 
  trans   := trans_square'; 
  init    := init_square'; 
  label   := label_square'; 
  serial  := serial_square' 
|}.

Ltac contradict_fV sat_hyp init_l := 
let rec loop H init_:= 
  lazymatch type of H with
  | _ /\ _ =>
    let H1 := fresh "H1" in 
    let H2 := fresh "H2" in
    destruct H as (H1&H2);
    ((apply H1 in init_; repeat destruct init_ as [init_|init_]; discriminate) +
    (apply H2 in init_; repeat destruct init_ as [init_|init_]; discriminate) +
    loop H2 init_)
  | _ => (apply H in init_; repeat destruct init_ as [init_|init_]; discriminate)
  end
in
loop sat_hyp init_l.


Theorem F1_neg: 
forall st: state model_square', 
st = four_square' -> 
satisfies (model_square') (fImp ((fV 1)) (fF)) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l.
  intro sat_hyp.
  contradict_fV sat_hyp init_l.
Defined.

Ltac contradict_fAX model_l st_l sat_hyp init_l tac:= 
  (* rewrite init_l in sat_hyp. *)
  (* compute in sat_hyp. *)
  pose proof ((serial model_l) st_l) as ser;
  destruct ser as [v' hyp];
  assert (hyp':=hyp);
  (* compute in hyp. *)
  let rec loop sat_hyp hyp hyp' init_:= 
  lazymatch type of hyp' with
  | _ /\ _ =>
    let H1:= fresh "H1" in
    let H2:= fresh "H2" in
    destruct hyp' as (H1&H2);
    (apply H1 in init_; repeat destruct init_ as [init_|init_];apply sat_hyp in hyp; tac hyp init_) +
    (apply H2 in init_; repeat destruct init_ as [init_|init_];apply sat_hyp in hyp; tac hyp init_) +
    loop sat_hyp hyp H2 init_
  | _ => (apply hyp' in init_; repeat destruct init_ as [init_|init_];apply sat_hyp in hyp; tac hyp init_) 
  end
  in
  loop sat_hyp hyp hyp' init_l.


Theorem F1'_neg: 
forall st: state model_square', 
st = four_square' -> 
satisfies (model_square') (fImp (fAX (fV 1)) (fF)) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l.
  intro sat_hyp.
  contradict_fAX model_square' st_l sat_hyp init_l contradict_fV.
Defined.
  



Theorem F1''_neg: 
forall st: state model_square', 
st = four_square' -> 
satisfies (model_square') (fNeg (fAX(fV 1)) ) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l.
  intro sat_hyp.
  compute.
  contradict_fAX model_square' st_l sat_hyp init_l contradict_fV.
Defined.
(* Print ex. *)










Theorem F1'''_neg: 
forall st: state model_square', 
st = one_square' -> 
satisfies (model_square') (fNeg (fNeg (fV 3)) ) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l.
  intro sat_hyp.
  apply sat_hyp.
  SOLVE_FV' init_l.
Qed.

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



Ltac contradict_fV' init_l := 
  let H := fresh "H" in
  intro H;
  contradict_fV H init_l
.


Theorem F1''''_neg: 
forall st: state model_square', 
st = one_square' -> 
satisfies (model_square') ((fAX(fNeg (fV 3)))) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l.
  solve_fAX contradict_fV' init_l .
Defined.


Theorem F2'_neg: 
forall st: state model_square', 
st = one_square' -> 
satisfies (model_square') ((fNeg (fAX (fV 3)))) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l.
  intro sat_hyp.
  contradict_fAX model_square' st_l sat_hyp init_l contradict_fV.
Defined.




Theorem F2''_neg: 
forall st: state model_square', 
st = one_square' -> 
satisfies (model_square') ((fNeg (fAU (fV 0)(fV 2)))) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l.
  intro sat_hyp.

  
  

  pose proof (H 0).
  apply H to 0.
  assert (H: nat->square') .
  give_up.


  
  


  





