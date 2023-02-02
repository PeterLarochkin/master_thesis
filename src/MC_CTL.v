
(* 

Inductive ex (A:Type) (P: A -> Prop) : Prop :=
  ex_intro : forall x:A, P x -> ex A P.
Inductive ex2 (A:Type) (P Q:A -> Prop) : Prop :=
  ex_intro2 : forall x:A, P x -> Q x -> ex2 A P Q.

Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
(at level 200, x binder, right associativity,
  format "'[' 'exists' '/ ' x .. y , '/ ' p ']'")
: type_scope.

Notation "'exists2' x , p & q" := (ex2 (fun x => p) (fun x => q))
  (at level 200, x name, p at level 200, right associativity) : type_scope.
Inductive and (A B : Prop) : Prop :=
| conj : A -> B -> and A B.
Notation "A /\ B" := (and A B).
Inductive or (A B : Prop) : Prop :=
| or_introl : A -> or A B 
| or_intror : B -> or A B.
Notation "A \/ B" := (or A B).

*)

Definition cAX: forall X : Type, 
(X -> X -> Prop) -> (X -> Prop) -> X -> Prop := 
  fun (X : Type) (e : X -> X -> Prop) (p : X -> Prop) (w : X) =>
  forall v : X, e w v -> p v.

Definition path: forall X : Type, (X -> X -> Prop) -> (nat -> X) -> Prop := 
fun (X : Type) (e : X -> X -> Prop) (pi : nat -> X) =>
forall n : nat, e (pi n) (pi (S n)).

Definition p_until: forall X : Type,
(X -> Prop) -> (X -> Prop) -> (nat -> X) -> Prop := 
  fun (X : Type) (p q : X -> Prop) (pi : nat -> X) =>
  exists2 n : nat, forall m : nat, m < n -> p (pi m) & q (pi n).

Definition p_release: forall X : Type, 
(X -> Prop) -> (X -> Prop) -> (nat -> X) -> Prop := 
  fun (X : Type) (p q : X -> Prop) (pi : nat -> X) =>
  forall n : nat, (exists2 m : nat, m < n & p (pi m)) \/ q (pi n).

Definition pAU : forall X : Type,
(X -> X -> Prop) -> (X -> Prop) -> (X -> Prop) -> X -> Prop := 
  fun (X : Type) (e : X -> X -> Prop) (p q : X -> Prop) (w : X) =>
  forall pi : nat -> X, path X e pi -> (pi 0 = w) -> p_until X p q pi.

Definition pAR: forall X : Type,
(X -> X -> Prop) -> (X -> Prop) -> (X -> Prop) -> X -> Prop := 
fun (X : Type) (e : X -> X -> Prop) (p q : X -> Prop) (w : X) =>
forall pi : nat -> X, path X e pi -> (pi 0 = w) -> p_release X p q pi.


Inductive form : Set :=
| fF    : form
| fV    : nat -> form
| fImp  : form -> form -> form
| fAX   : form -> form
| fAR   : form -> form -> form 
| fAU   : form -> form -> form.

Record sts := STS {
  state  : Type;
  trans  : state -> state -> Prop;
  init   : state -> Prop;
  label  : nat -> state -> Prop;
  serial : forall w:state, exists v, trans w v
}.

Definition satisfies: forall M : sts, form -> state M -> Prop := 
fix satisfies (M : sts) (s : form) {struct s} : state M -> Prop :=
match s with
| fF        => fun w : state M => False
| fV v      => label M v
| fImp s0 t => fun w : state M => satisfies M s0 w -> satisfies M t w
| fAX  s0   => cAX (state M) (trans M) (satisfies M s0)
| fAR  s0 t => pAR (state M) (trans M) (satisfies M s0) (satisfies M t)
| fAU  s0 t => pAU (state M) (trans M) (satisfies M s0) (satisfies M t)
end.

Inductive bool : Set :=  true : bool | false : bool.

Definition trans_bool (s1:bool)(s2:bool):Prop := 
match s1, s2 with 
| true, false => True 
| false, true => True
| _, _ => False
end.
Check Nat.eqb.
Definition label_bool(v: nat)(s:bool):Prop :=
if  Nat.eqb (Nat.modulo v 2) 0
then 
match s with 
| true => True
| false => False
end
else 
match s with 
| true => False
| false => True
end
.
Definition serial_bool: forall w:bool, exists v, trans_bool w v.
intros. case w. all: [>eexists false | eexists true]; compute; apply I.
Defined.  

Definition init_bool(s: bool):Prop := s=true.
Definition model_bool: sts :=  {| state := bool; trans := trans_bool; init:= init_bool; label := label_bool; serial := serial_bool |}.

Print eq.

Theorem check1: forall st: state model_bool, (init model_bool) st -> @satisfies(model_bool) (fAX (( (fV 1)))) st.
Proof.
  compute.
  intros.
  rewrite H in H0.
  apply H0.
Qed.
  
  
  
  
  

  
  
  
  
  
  

  

  

Qed.
	 
