Require Import MC_CTL.
Require Import List. Import ListNotations. 


Definition from_trans_to_Prop{A}(list_connections: list (A*A)): A -> A -> Prop :=
(fun s1 s2 =>
  let fix make_prop (list_connections: list (A*A)):Prop :=
    match list_connections with 
    | (b1,b2)::nil => (s1 = b1 -> s2 = b2)
    | (b1,b2)::tail => (s1 = b1 -> s2 = b2) /\ (make_prop tail)
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


Inductive   bool : Set :=  true : bool | false : bool.
Definition  trans_bool := from_trans_to_Prop [(false, true);(true, false)].
Definition  label_bool := from_label_to_Prop [(false, 0); (true,1)].
Definition  serial_bool: forall w:bool, exists (v:bool), trans_bool w v.
intros. case w;[> eexists false | eexists true]. all:compute; split. all:auto.
Defined.

Definition init_bool := from_init_to_Prop [false].
Definition model_bool: sts :=  {| state := bool; trans := trans_bool; init:= init_bool; label := label_bool; serial := serial_bool |}.

(* Theorem ff: forall st: state model_bool, 
(init model_bool) st -> 
satisfies (model_bool) (fF) st.
Proof.
  intro. intro. unfold satisfies.  discriminate.
Qed. *)

Theorem f1v: forall st: state model_bool, 
(init model_bool) st -> 
satisfies (model_bool) (fV 0) st.
Proof.
  intro st_l. intro init_l.  
    compute. split. 
    { auto. } 
    { intro cur_st_l. compute in init_l. rewrite init_l in cur_st_l. discriminate. }
Qed.

Theorem f1f: forall st: state model_bool, 
(init model_bool) st -> 
satisfies (model_bool) (fF) st.
Proof.
  intro. intro. unfold satisfies. compute in H.   
Admitted.

Theorem f1imp: forall st: state model_bool, 
(init model_bool) st -> 
satisfies (model_bool) (fImp (fV 1) (fV 1)) st.
Proof.
  intro. intro. compute. compute in H. intro.
  auto. 
Qed.

Theorem f1ax: forall st: state model_bool, 
(init model_bool) st -> 
satisfies (model_bool) (fAX (fV 1)) st.
Proof.
  intro. intro. compute. intro. intro. compute in H.
  split. 
  { destruct H0. intro. apply H0 in H. rewrite H in H2. discriminate.  }
  { destruct H0. auto.  }
Qed.
Require Import Lia.



Ltac sample a := 
  let is_path_l := fresh "is_path_l" in
  let begin_l := fresh "begin_l" in
  let st_l := fresh "st_l" in
  let init_l := fresh "init_l" in
  intro st_l; 
  intro init_l;
  intro path_l;
  intro is_path_l;
  intro begin_l;
  
  rewrite init_l in begin_l;
  
  pose proof (is_path_l 1) as is_path_st_l;
  compute in is_path_st_l;
  compute;
  eexists a;
  [>
  let proof_by_induction := 
    let m:= fresh "m" in
    intro m;
    induction m; 
    [
      let base :=  
        intro; split; 
        [
          let case1 := auto 
          in 
          case1
        |
          let case2 := 
            let beging_moment_l := fresh "beging_moment_l" in
            intro beging_moment_l; rewrite begin_l in beging_moment_l; discriminate 
          in 
          case2
        ] in 
      base
    |
      let inductive_transition :=
      intro;  split;
      [ 
        auto 
      |
        intro beging_moment_l ]
      in inductive_transition; lia 
      ] in 
      proof_by_induction
      |
      split; 
      [
        let path_case1 := fresh "path_case1" in
        intro path_case1; 
        pose proof (is_path_l 0) as somety;
        destruct somety as (s1 & s2);
        apply s1 in begin_l;
        rewrite begin_l in path_case1;
        discriminate
        |
        auto
      ]
  ].





Ltac intosAU a := 
  let is_path_l := fresh "is_path_l" in
  let begin_l := fresh "begin_l" in
  let st_l := fresh "st_l" in
  let init_l := fresh "init_l" in
  let path_l := fresh "path_l" in
  intro st_l; compute in st_l;
  intro init_l; compute in init_l;
  intro path_l;compute in path_l;
  intro is_path_l; compute in is_path_l;
  intro begin_l; compute in begin_l;compute
  (* pose proof (is_path_l 1) as is_path_st_l.
  compute in is_path_st_l. *)
.

Theorem f1au: forall st: state model_bool, 
(init model_bool) st -> 
satisfies (model_bool) (fAU (fV 0) (fV 1)) st.
Proof.
  intosAU 0.
  rewrite init_l in begin_l. compute in begin_l.
  compute.
  eexists 1. 
  {
    let m:= fresh "m" in
    intro m.
    induction m. 
    {
      
        intro. split. 
        {
          let case1 := auto 
          in 
          case1.
        }{
          let case2 := 
            let beging_moment_l := fresh "beging_moment_l" in
            intro beging_moment_l; rewrite begin_l in beging_moment_l; discriminate 
          in 
          case2.
        }
    }{
      
      intro.  split.
      { 
        auto.
      }{
        intro beging_moment_l. lia. 
      }
       
    } 
      
  }{
  split. 
    {
    let path_case1 := fresh "path_case1" in
    intro path_case1. 
    pose proof (is_path_l 0) as somety.
    destruct somety as (s1 & s2).
    apply s1 in begin_l.
    rewrite begin_l in path_case1.
    discriminate.
    }{
    auto.
    }
  }
Defined.

Theorem f1ar: forall st: state model_bool, 
(init model_bool) st -> 
satisfies (model_bool) (fAR (fF) (fV 0)) st.
Proof.
  compute.
  intro. intro.

  intro path_l.
  intro moment_l.
  intro begin_l.
  intro moment_n.
Admitted.


Theorem f1ax_au_0or1_1: forall st: state model_bool, 
(init model_bool) st -> 
satisfies (model_bool) (fAX (fAU (fV 1)(fV 0))) st.
Proof.

  intro st. intro init. 
  (* fAX *)
  {
    (* compute. *)
    intro st_l. intro tr_l. compute in tr_l.
    (* fAU *)
    (* {
        intro path_l.
        intro moment_l.
        intro is_path_l.
        compute.
        eexists 1.
        (* proof fv *)
        {
          intro m.
          intro le_m.
          unfold satisfies.  compute. right. compute in init. split. destruct st. discriminate.
        }
        (* proof fv *)
        {
          unfold satisfies.  compute. left.  split.
        } 
    } *)
  }
Admitted.
