Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
(* From CompDecModal.libs
  Require Import edone bcase fset base modular_hilbert sltype. *)

Set Default Proof Using "Type".

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Section Characterizations.
Notation "P =p Q" := (forall x, P x <-> Q x) (at level 40).
Definition PredC X (p : X -> Prop) x := ~ p x.
Variables (X : Type) (e : X -> X -> Prop).

Definition cEX (p : X -> Prop) (w : X) : Prop := exists2 v, e w v & p v.
Definition cAX (p : X -> Prop) (w : X) : Prop := forall v, e w v -> p v.

CoInductive cAR (p q : X -> Prop) (w : X) : Prop :=
| AR0 : p w -> q w -> cAR p q w
| ARs : q w -> (forall v, e w v -> cAR p q v) -> cAR p q w.

Inductive cAU (p q : X -> Prop) (w : X) : Prop :=
| AU0 : q w -> cAU p q w
| AUs : p w -> (forall v, e w v -> cAU p q v) -> cAU p q w.

CoInductive cER (p q : X -> Prop) (w : X) : Prop :=
| ER0 : p w -> q w -> cER p q w
| ERs v : q w -> e w v -> cER p q v -> cER p q w.

Inductive cEU (p q : X -> Prop) (w : X) : Prop :=
| EU0 : q w -> cEU p q w
| EUs v : p w -> e w v -> cEU p q v -> cEU p q w.

Lemma cAU_cER (p q : X -> Prop) (w : X) :
cER (PredC p) (PredC q) w -> ~ cAU p q w.
Proof.
move => E A. elim: A E => {w}[w qw|w]; first by case.
move => pw _ IH. case => // v _. exact: IH.
Qed.

Lemma cAR_cEU (p q : X -> Prop) (w : X) :
cEU (PredC p) (PredC q) w -> ~ cAR p q w.
Proof.
move => E A. elim: E A => {w} [w ?|w v]; first by case.
move => pw wv _ IH. case => // qw /(_ _ wv). exact: IH.
Qed.

Lemma AU_strengthen (p1 q1 p2 q2 : X -> Prop) w :
(forall v, p1 v -> p2 v) -> (forall v, q1 v -> q2 v) ->
cAU p1 q1 w -> cAU p2 q2 w.
Proof.
move => H1 H2. elim => {w} - w; first by move => ?; apply AU0; auto.
move => /H1 ? _ IH. apply: AUs ; auto.
Qed.

Lemma AR_strengthen (p1 q1 p2 q2 : X -> Prop) w :
(forall v, p1 v -> p2 v) -> (forall v, q1 v -> q2 v) ->
cAR p1 q1 w -> cAR p2 q2 w.
Proof.
move => H1 H2. move: w. cofix AR_strengthen => w.
case => [ /H1 ? /H2 ?|/H2 ? N]; first exact: AR0.
apply: ARs => // v wv. apply: AR_strengthen. exact: N.
Qed.

Lemma ER_strengthen (p1 q1 p2 q2 : X -> Prop) w :
(forall v, p1 v -> p2 v) -> (forall v, q1 v -> q2 v) ->
cER p1 q1 w -> cER p2 q2 w.
Proof.
move => Hp Hq. move: w. cofix ER_strengthen => w. 
case => [/Hp ? /Hq ?|v V1 V2 V3]; first exact: ER0.
by apply: ERs _ V2 _ ; auto.
Qed.

Lemma EU_strengthen (p1 q1 p2 q2 : X -> Prop) w :
(forall v, p1 v -> p2 v) -> (forall v, q1 v -> q2 v) ->
cEU p1 q1 w -> cEU p2 q2 w.
Proof.
move => H1 H2. elim => {w} - w; first by move => ?; apply EU0; auto.
move => v /H1 wv ? IH. apply: EUs ; auto.
Qed.

Lemma cAU_eq (x y : X) (p q : pred X) :
p x = p y -> q x = q y -> e x =p e y -> cAU p q x -> cAU p q y.
Proof.
move => Hp Hq Ht. case => [?|px Hs]; first by apply: AU0; congruence.
apply: AUs => //. congruence. move => v /Ht. exact: Hs.
Qed.

Lemma cEU_eq (x y : X) (p q : pred X) :
    p x = p y -> q x = q y -> e x =p e y -> cEU p q x -> cEU p q y.
Proof.
move => Hp Hq Ht. case => [?|z xz Hs]; first by apply: EU0; congruence.
apply: EUs => //. congruence. exact/Ht.
Qed.
End Characterizations.