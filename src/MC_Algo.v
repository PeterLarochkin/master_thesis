Require Import MC_CTL.


Inductive   bool : Set :=  true : bool | false : bool.
Definition  trans_bool (s1 s2:bool):Prop := ~ (s1 = s2).
Definition  label_bool(v: nat)(s:bool):Prop := (s = false /\ v = 0) \/ (s = true /\ v = 1).
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
  intro. intro. unfold satisfies.  compute. auto.
  (* apply H. reflexivity.  *)
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
  destruct H0. 
  { left. apply H0. }
  { right. apply H0. }
Qed.

Theorem f1ax: forall st: state model_bool, 
(init model_bool) st -> 
satisfies (model_bool) (fAX (fV 1)) st.
Proof.
  intro. intro. compute. intro. intro. compute in H. destruct v.
  right; auto. apply H0 in H. contradiction. 
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

     unfold satisfies.  compute. left. lia.
  }
  (* proof fv *)
  {
     unfold satisfies.  compute. left.  split. compute in H. rewrite -> H in begin_l. all:auto.
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

#[global]
Hint Resolve S : core.

#[global]
Hint Resolve ex_intro2 : core.
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
    {
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
    }
  }
Defined.



















(* Conclusion
How to define model?
Set of states is construction like
Inductive state:Type := 
| s1:state
| s2:state
...
| sn:state
.
*)


Inductive   triangle : Set :=  A : triangle | B : triangle | C : triangle.
Definition  trans_triangle (s1 s2:triangle):Prop := (s1 = C -> (~ s2 = B)) /\ (s1 = B -> (~ s2 = C)).
Definition  label_triangle(v: nat)(s:triangle):Prop := (s = A /\ v = 0) \/ (s = B -> v = 1) /\ (s = C -> v = 1).
Definition  serial_triangle: forall w:triangle, exists (v:triangle), trans_triangle w v.
intros. case w . eexists B. repeat split. 1-3:discriminate. eexists A. repeat split. 1-3:discriminate. eexists A. repeat split. 1-3:discriminate.
Defined.

Definition init_triangle(s: triangle) : Prop := s = A.
Definition model_triangle: sts :=  {| state := triangle; trans := trans_triangle; init:= init_triangle; label := label_triangle; serial := serial_triangle |}.


Theorem f2v: forall st: state model_triangle, 
(init model_triangle) st -> 
satisfies (model_triangle) (fV 0) st.
Proof.
  intro. intro. unfold satisfies.  compute. auto.
Qed.

Theorem f2imp: forall st: state model_triangle, 
(init model_triangle) st -> 
satisfies (model_triangle) (fImp (fV 1) (fAX (fV 1))) st.
Proof.
  intro st_. intro init_.
  intro left_. intro st__. intro. right. right. auto.
Defined.

Theorem f2ax: forall st: state model_triangle, 
(init model_triangle) st -> 
satisfies (model_triangle) (fAX (fV 1)) st.
Proof.
intro st. intro init. 
  (* fAX *)
  {
    compute.
    
    intro st_l. intro tr_l. compute in init. rewrite init in tr_l. repeat destruct  tr_l.  left . intro. symmetry in H1. apply H in H1.
    contradiction.
  }
Defined.



Theorem f2au: forall st: state model_triangle, 
(init model_triangle) st -> 
satisfies (model_triangle) (fAU (fV 0) (fV 1)) st.
Proof.
intro st_. intro init_. 
  (* fAU *)
  {
    intro path_l.
    intro moment_l.
    intro is_path_l.
    compute.
    eexists 1.
    (* proof fv *)
    {
      intro m.
      intro le_m.
      unfold satisfies.  compute. left. auto.
    }
    (* proof fv *)
    {
      unfold satisfies.  compute. right. right. auto.
    }
  }
Defined.

Theorem f2ar: forall st: state model_triangle, 
(init model_triangle) st -> 
satisfies (model_triangle) (fAR (fV 0) (fV 1)) st.
Proof.
  intro st_. intro init_. 
  intro path_.
  intro moment_.
  intro begin_.
  intro fut_moment_.
    right.
    compute.
    compute in init_.
    right. right.
    auto. 
Defined.

