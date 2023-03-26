Definition cAX (st : Type) (trans : st -> st -> Prop) (pred : st -> Prop) (w : st):= 
forall v : st, trans w v -> pred v.

Definition path(st : Type) (trans : st -> st -> Prop) (pi : nat -> st):= 
forall n : nat, trans (pi n) (pi (S n)).

Definition p_until(st : Type) (pred1 pred2 : st -> Prop) (pi : nat -> st):= 
exists2 n : nat, forall m : nat, m < n -> pred1 (pi m) & pred2 (pi n).

Definition p_release(st : Type) (pred1 pred2 : st -> Prop) (pi : nat -> st):= 
forall n : nat, (exists2 m : nat, m < n & pred1 (pi m)) \/ pred2 (pi n).

Definition pAU (st : Type) (trans : st -> st -> Prop) (pred1 pred2 : st -> Prop) (w : st):= 
forall pi : nat -> st, path st trans pi -> (pi 0 = w) -> p_until st pred1 pred2 pi.

Definition pAR (st : Type) (trans : st -> st -> Prop) (pred1 pred2: st -> Prop) (w : st) := 
forall pi : nat -> st, path st trans pi -> (pi 0 = w) -> p_release st pred1 pred2 pi.


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
