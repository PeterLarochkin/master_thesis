Require Import MC_CTL.




Inductive   bool : Set :=  true : bool | false : bool.
Definition  trans_bool (s1 s2:bool):Prop := ~ (s1 = s2).
Definition  label_bool(v: nat)(s:bool):Prop := (s = false  /\  v = 0) \/ (s = true /\ v = 1).
Definition  serial_bool: forall w:bool, exists (v:bool), trans_bool w v.
intros. case w ;[> eexists false | eexists true]; compute; discriminate.
Defined.

Definition init_bool(s: bool):Prop := s = false.
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
  intro. intro. unfold satisfies.  compute. left. split. apply H. reflexivity. 
Qed.

Theorem f1f: forall st: state model_bool, 
(init model_bool) st -> 
satisfies (model_bool) (fF) st.
Proof.
  intro. intro. unfold satisfies. compute in H.  
Admitted.

Theorem f1imp: forall st: state model_bool, 
(init model_bool) st -> 
satisfies (model_bool) (fImp (fV 1) (fF)) st.
Proof.
  intro. intro. compute. compute in H. intro. destruct H0. destruct H0.  discriminate. destruct H0. rewrite H0 in H. discriminate.
Qed.

Theorem f1ax: forall st: state model_bool, 
(init model_bool) st -> 
satisfies (model_bool) (fAX (fV 1)) st.
Proof.
  intro. intro. 
  
  compute.
  intro st_l. intro tr_l. compute in H. rewrite H in tr_l. right. split. 2:auto. destruct st_l. auto. 
  assert (easy: false = false). auto. apply tr_l  in easy. refine (match easy with end).
Defined.
Require Import Lia.
Theorem f1au: forall st: state model_bool, 
(init model_bool) st -> 
satisfies (model_bool) (fAU (fV 0) (fV 0)) st.
Proof.
  intro. intro.
  intro path_l.
  intro moment_l.
  intro begin_l.
  
  compute in moment_l.
  compute.
  
  eexists 0.
  (* proof fv *)
  {
    intro m.
    intro le_m.

     unfold satisfies.  compute. left. compute in H. split. 2:auto. rewrite <- H.  rewrite <- begin_l. apply f_equal.
     try lia.
  }
  (* proof fv *)
  {
     unfold satisfies.  compute. left.  split. compute in H. rewrite H in begin_l. rewrite begin_l. all:auto.
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

