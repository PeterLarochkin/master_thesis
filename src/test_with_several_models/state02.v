Require Import tactics.
Require Import List. 
Require Import Lia.
Require Import MC_CTL2.
Import ListNotations.




Inductive model : Set :=  
| one 
| two
.

(* Model 1 *)
Definition  trans_model1 := to_Prop [
(one, [two]);
(two, [one;two])
].


Definition  label_model1 := to_Prop [
(one, [1;2;3;4;5;6]);
(two, [9;10;11;12])
].

Definition  serial_model1: forall w:model, exists (v:model), trans_model1 w v.
intros.
case w.
eexists two;repeat split; intro;try discriminate;left;auto.
eexists one;repeat split; intro;try discriminate;left;auto.
Defined.

Definition init_model1 := fun st => st = one.
Definition model1: sts :=  {| 
  state   := model; 
  trans   := trans_model1; 
  init    := init_model1; 
  label   := fun a b => label_model1 b a; 
  serial  := serial_model1
|}.

Goal 
forall st: state model1, (init model1) st -> satisfies (model1) (fV 1) st.
intro st. intro init_.
solver 2 init_.
Qed.

Goal 
forall st: state model1, (init model1) st -> satisfies (model1)  (fAX (fV 12)) st.
intro st. intro init_.
solver 2 init_.
Qed.

Goal 
forall st: state model1, (init model1) st -> satisfies (model1)  (fAX (fAnd (fV 12) (fV 9))) st.
intro st. intro init_.
solver 2 init_.
Qed.

Goal 
forall st: state model1, (init model1) st -> satisfies (model1)  (fAX (fOr (fAX (fOr (fV 2)(fV 12))) (fV 9))) st.
intro st. intro init_.
solver 2 init_.
Qed.

Goal 
forall st: state model1, (init model1) st -> satisfies (model1)  (fAU (fV 1) (fAX (fOr (fV 1)(fV 9)))) st.
intro st. intro init_.
solver 2 init_.
Qed.




(* Model 2 *)
Definition  trans_model2 := to_Prop [
(one, [one;two]);
(two, [one])
].


Definition  label_model2 := to_Prop [
(one, [8;7;12;3;7]);
(two, [10;13;6;2;7])
].

Definition  serial_model2: forall w:model, exists (v:model), trans_model2 w v.
intros.
case w.
eexists one;repeat split; intro;try discriminate;left;auto.
eexists one;repeat split; intro;try discriminate;left;auto.
Defined.

Definition init_model2 := fun st => st = one.
Definition model2: sts :=  {| 
  state   := model; 
  trans   := trans_model2; 
  init    := init_model2; 
  label   := fun a b => label_model2 b a; 
  serial  := serial_model2
|}.


Goal 
forall st: state model2, (init model2) st -> satisfies (model2) (fV 3) st.
intro st. intro init_.
solver 2 init_.
Qed.


Goal 
forall st: state model2, (init model2) st -> satisfies (model2) (fAX (fOr (fV 8)(fV 10))) st.
intro st. intro init_.
solver 2 init_.
Qed.


Goal 
forall st: state model2, (init model2) st -> satisfies (model2) (fAX (fOr (fV 8)(fV 13))) st.
intro st. intro init_.
solver 2 init_.
Qed.

Goal 
forall st: state model2, (init model2) st -> satisfies (model2) (fAX (fAnd (fV 7) (fOr (fV 8)(fV 13)))) st.
intro st. intro init_.
solver 2 init_.
Qed.

Goal 
forall st: state model2, (init model2) st -> satisfies (model2) (fAU (fOr (fV 8)(fV 10))(fOr (fV 8)(fV 10))) st.
intro st. intro init_.
solver 2 init_.
Qed.

Goal True.
idtac "2-state model passed".
auto.
Qed.
