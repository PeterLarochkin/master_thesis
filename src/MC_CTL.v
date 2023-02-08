
(* 

Inductive ex (A:Type) (P: A -> Prop) : Prop :=
  ex_intro : forall x:A, forall _: P x, ex A P.
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
Check eq _ _ -> eq _ _ .
Print ex_intro.

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
(* Inductive nat : Set :=  S : nat -> nat. *)
Check ex.


Fixpoint satisfies (M : sts) (s : form){struct s}:state M -> Prop := 
  (match s with
  | fF        => fun w : state M => False
  | fV v      => label M v
  | fImp s0 t => fun w : state M => satisfies M s0 w -> satisfies M t w
  | fAX  s0   => cAX (state M) (trans M) (satisfies M s0)
  | fAR  s0 t => pAR (state M) (trans M) (satisfies M s0) (satisfies M t)
  | fAU  s0 t => pAU (state M) (trans M) (satisfies M s0) (satisfies M t)
  end: state M -> Prop ).

Print False.


Inductive bool : Set :=  true : bool | false : bool.

Definition trans_bool (s1:bool)(s2:bool):Prop := ~ (s1 = s2).
Definition label_bool(v: nat)(s:bool):Prop := v = (match s with | false => 0 | true => 1 end).
Definition serial_bool: forall w:bool, exists v, trans_bool w v.
intros. case w; [> eexists false|eexists true] ;compute;discriminate.
Defined.  

Definition init_bool(s: bool):Prop := s = false.
Definition model_bool: sts :=  {| state := bool; trans := trans_bool; init:= init_bool; label := label_bool; serial := serial_bool |}.

Theorem check1: forall st: state model_bool, 
(init model_bool) st -> 
satisfies(model_bool) (fAX (( (fV 1)))) st.
Proof.
  compute.
  intros. destruct v. auto. apply H0 in H. refine (match H with end).
Defined.

  
  
  
  
  
  
Qed.
  
  
  
  
  

  
  
  
  
  
  

  

  

Qed.
	 
