Require Import tactics.
Require Import List. 
Require Import Lia.
Require Import MC_CTL2.
Import ListNotations.




Inductive model : Set :=  
| one 
| two
| three
| four
.

(* Model 1 *)
Definition  trans_model1 := to_Prop [
(one, [two;three]);
(two, [four]);
(three, [three;four]);
(four, [four])
].


Definition  label_model1 := to_Prop [
(one, [1;2;3;4;5]);
(two, [1;9;10;11;12]);
(three, [22;16;6]);
(four, [93;6])
].

Definition  serial_model1: forall w:model, exists (v:model), trans_model1 w v.
intros.
case w.
eexists two;repeat split; intro;try discriminate;left;auto.
eexists four;repeat split; intro;try discriminate;left;auto.
eexists three;repeat split; intro;try discriminate;left;auto.
eexists four;repeat split; intro;try discriminate;left;auto.
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
forall st: state model1, (init model1) st -> satisfies (model1) (fAU (fAX (fOr (fV 9)(fOr (fV 93)(fV 22)))) (fV 6)) st.
intro st. intro init_.
solver 4 init_.
Qed.


Goal 
forall st: state model1, (init model1) st -> satisfies (model1) (fAX (fAU (fAX (fOr (fV 9)(fOr (fV 93)(fV 22)))) (fV 6))) st.
intro st. intro init_.
solver 4 init_.
Qed.


Goal 
forall st: state model1, (init model1) st -> satisfies (model1) (fAU (fOr (fAU (fV 100) (fV 6))(fV 1)) (fV 6) ) st.
intro st. intro init_.
solver 4 init_.
Qed.


(* Model 2 *)
Definition  trans_model2 := to_Prop [
(one, [one;two]);
(two, [three;four]);
(three, [four]);
(four, [four])
].


Definition  label_model2 := to_Prop [
(one, [1;2;3;16]);
(two, [10;11;12;16]);
(three, [16;17]);
(four, [101;100])
].

Definition  serial_model2: forall w:model, exists (v:model), trans_model2 w v.
intros.
case w.
eexists one;repeat split; intro;try discriminate;left;auto.
eexists three;repeat split; intro;try discriminate;left;auto.
eexists four;repeat split; intro;try discriminate;left;auto.
eexists four;repeat split; intro;try discriminate;left;auto.
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
forall st: state model2, (init model2) st -> satisfies (model2) (fAnd (fV 1) (fAU (fAX (fV 16)) (fOr (fV 101 )(fV 16)))) st.
intro st. intro init_.
solver 4 init_.
Qed.


Goal 
forall st: state model2, (init model2) st -> satisfies (model2) (fOr (fV 16)(fAU (fV 16)(fV 101))) st.
intro st. intro init_.
solver 4 init_.
Qed.

Goal 
forall st: state model2, (init model2) st -> satisfies (model2) (fAX (fOr (fV 1) (fAU (fV 16)(fV 101)))) st.
intro st. intro init_.
solver 4 init_.
Qed.


Goal 
forall st: state model2, (init model2) st -> satisfies (model2) (fAX (fOr (fV 1) (fAX (fOr (fV 17)(fV 100))))) st.
intro st. intro init_.
solver 4 init_.
Qed.


Goal True. idtac "4-state model passed". auto. Defined.