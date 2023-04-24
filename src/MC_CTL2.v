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
| fNeg  : form -> form
| fV    : nat -> form
| fOr   : form -> form -> form 
| fAnd  : form -> form -> form 
| fImp  : form -> form -> form
| fAX   : form -> form
| fAR   : form -> form -> form 
| fAU   : form -> form -> form.

Record sts := STS {
  state  : Set;
  trans  : state -> state -> Prop;
  init   : state -> Prop;
  label  : nat -> state -> Prop;
  serial : forall w:state, exists v, trans w v
}.


Fixpoint satisfies (M : sts) (s : form){struct s}:state M -> Prop := 
  (match s with
  | fF        => fun w : state M => False
  | fNeg s0   => fun w : state M => ~ (satisfies M s0 w)
  | fV v      => fun w : state M => label M v w
  | fOr  s0 t => fun w : state M => (satisfies M s0 w) \/ (satisfies M t w)
  | fAnd s0 t => fun w : state M => (satisfies M s0) w /\ (satisfies M t w)
  | fImp s0 t => fun w : state M => satisfies M s0 w -> satisfies M t w
  | fAX  s0   => fun w : state M => cAX (state M) (trans M) (satisfies M s0) w
  | fAR  s0 t => fun w : state M => pAR (state M) (trans M) (satisfies M s0) (satisfies M t) w
  | fAU  s0 t => fun w : state M => pAU (state M) (trans M) (satisfies M s0) (satisfies M t) w
  end: state M -> Prop ).


Fixpoint make_disjucntion_for_state_to{A} (s2: A)(states_in: list A) := 
match states_in with
| cons head nil => s2 = head
| cons head tail => s2 = head \/ (make_disjucntion_for_state_to s2 tail)
| nil => False
end
.

Fixpoint make_prop{A B} (s1:A )( s2:B) (list_connections: list (A * (list B))):Prop := 
match list_connections with 
| cons (pair b1 b2) nil => (s1 = b1 -> (make_disjucntion_for_state_to s2 b2))
| cons (pair b1 b2) tail => (s1 = b1 -> (make_disjucntion_for_state_to s2 b2)) /\ (make_prop s1 s2 tail)
| nil => False  
end 
.
Definition to_Prop{A B}(list_connections: list (B * (list A))): B -> A -> Prop :=
(fun s1 s2 => make_prop s1 s2 list_connections).