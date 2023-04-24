Require Import tactics.
Require Import List. 
Require Import Lia.
Require Import MC_CTL2.
Import ListNotations.




Inductive model : Set :=  
| one 
| two
| three
.

(* Model 1 *)
Definition  trans_model1 := to_Prop [
(one, [one;two;three]);
(two, [three]);
(three, [three])
].


Definition  label_model1 := to_Prop [
(one, [1;2;3;4;5;6]);
(two, [1;9;10;11;12;6]);
(three, [22;16;6])
].

Definition  serial_model1: forall w:model, exists (v:model), trans_model1 w v.
intros.
case w.
eexists one;repeat split; intro;try discriminate;left;auto.
eexists three;repeat split; intro;try discriminate;left;auto.
eexists three;repeat split; intro;try discriminate;left;auto.
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
solver 3 init_.
Qed.

Goal 
forall st: state model1, (init model1) st -> satisfies (model1)  (fAU (fV 1010) (fV 1)) st.
intro st. intro init_.
solver 3 init_.
Qed.

Goal 
forall st: state model1, (init model1) st -> satisfies (model1)  (fAU (fAU (fV 1) (fV 6)) (fOr (fV 22) (fV 6) )) st.
intro st. intro init_.
solver 3 init_.
Qed.

Goal 
forall st: state model1, (init model1) st -> satisfies (model1)  (fAX (fAnd (fAU ((fV 1))((fOr (fV 22) (fV 6) ))) (fV 6))) st.
intro st. intro init_.
solver 3 init_.
Qed.

(* Model 2 *)
Definition  trans_model2  := to_Prop [
(one, [two]);
(two, [three]);
(three, [three])
].


Definition  label_model2 := to_Prop [
(one, [1;2;3]);
(two, [9;10;11;12]);
(three, [22;16])
].

Definition  serial_model2: forall w:model, exists (v:model), trans_model2 w v.
intros.
case w.
eexists two;repeat split; intro;try discriminate;left;auto.
eexists three;repeat split; intro;try discriminate;left;auto.
eexists three;repeat split; intro;try discriminate;left;auto.
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
forall st: state model2, (init model2) st -> satisfies (model2) (fV 1) st.
intro st. intro init_.
solver 3 init_.
Qed.

Goal 
forall st: state model2, (init model2) st -> satisfies (model2) (fAU (fAU (fOr (fV 9)(fV 1))(fV 16))(fV 22)) st.
intro st. intro init_.
solver 3 init_.
Qed.

Goal 
forall st: state model2, (init model2) st -> satisfies (model2) (fAX (fAX (fAU (fV 0) (fV 22)))) st.
intro st. intro init_.
solver 3 init_.
Qed.

Goal 
forall st: state model2, (init model2) st -> satisfies (model2) (fAX (fAnd (fV 12) (fAX (fAU (fV 0) (fV 22))))) st.
intro st. intro init_.
solver 3 init_.
Qed.

Goal True.
idtac "3-state model passed".
auto.
Qed.
