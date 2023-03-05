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


Fixpoint satisfies (M : sts) (s : form){struct s}:state M -> Prop := 
  (match s with
  | fF        => fun w : state M => False
  | fV v      => fun w : state M => label M v w
  | fImp s0 t => fun w : state M => satisfies M s0 w -> satisfies M t w
  | fAX  s0   => fun w : state M => cAX (state M) (trans M) (satisfies M s0) w
  | fAR  s0 t => fun w : state M => pAR (state M) (trans M) (satisfies M s0) (satisfies M t) w
  | fAU  s0 t => fun w : state M => pAU (state M) (trans M) (satisfies M s0) (satisfies M t) w
  end: state M -> Prop ).
