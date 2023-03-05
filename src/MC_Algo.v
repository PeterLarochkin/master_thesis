Require Import MC_CTL.




Inductive   bool : Set :=  true : bool | false : bool.
Definition  trans_bool (s1 s2:bool):Prop := ~ (s1 = s2).
Definition  label_bool(v: nat)(s:bool):Prop := (v = 0 -> s = false) \/ (v = 1 -> s = true).
Definition  serial_bool: forall w:bool, exists (v:bool), trans_bool w v.
intros. case w ;[> eexists false|eexists true]; compute; discriminate.
Defined.  

Definition init_bool(s: bool):Prop := s = false.
Definition model_bool: sts :=  {| state := bool; trans := trans_bool; init:= init_bool; label := label_bool; serial := serial_bool |}.
Theorem fv: forall st: state model_bool, 
(init model_bool) st -> 
satisfies (model_bool) (fV 1) st.
Proof.
  intro. intro. unfold satisfies. left. discriminate.
Qed.
