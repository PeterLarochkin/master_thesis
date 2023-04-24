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
forall st: state model1, (init model1) st -> satisfies (model1) (fAU (fOr (fAU (fF) (fV 6))(fV 1)) (fV 6) ) st.
intro st. intro init_.
solver 4 init_.
Qed.

Goal True.
idtac "4-state model passed".
auto.
Qed.
