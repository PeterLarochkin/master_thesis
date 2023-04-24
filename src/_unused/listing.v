
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

Inductive le (n : nat) : nat -> Prop :=
	le_n : n <= n | le_S : forall m : nat, n <= m -> n <= S m.

*)
Locate "_ = _".
(* Check @eq_refl nat 1.
Check eq 0 1. *)
(* Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : x = x. *)
Inductive ex (A:Type) (P: A -> Prop) : Prop :=
  ex_intro : forall x:A, forall _: P x, ex A P.
Inductive ex2 (A:Type) (P Q:A -> Prop) : Prop :=
  ex_intro2 : forall x:A, P x -> Q x -> ex2 A P Q.
(* Inductive le (n : nat) : nat -> Prop :=
	le_n : n <= n | le_S : forall m : nat, n <= m -> n <= S m. *)
Inductive sts:Type := 
| STS: 
  forall 
  (state : Type) 
  (trans : state -> state -> Prop), 
  ((*init  :*) state -> Prop) -> 
  ((*label :*) nat -> state -> Prop) ->
  ((*serial:*) forall w : state, exists v : state, trans w v) -> sts.

Definition state (M:sts):Type := 
match M with 
| STS state _ _ _ _ => state 
end.
Definition trans (M:sts): (state M) -> (state M) -> Prop := 
match M with 
| STS _ trans _ _ _ => trans 
end.
Definition init (M:sts): (state M) ->  Prop := 
match M with 
| STS _ _ init _ _ => init 
end.
Definition label (M:sts): nat -> (state M) ->  Prop := 
match M with 
| STS _ _ _ label _ => label 
end.
Definition serial (M:sts): forall w : state M, exists v : state M, trans M w v := 
match M with 
| STS _ _ _ _ serial => serial 
end.

Section Characerization.
Context {H:sts}.

Definition cAX := 
  (fun (p : (state H) -> Prop) => fun (w : (state H)) =>
      forall v : (state H), (trans H) w v -> p v): ((state H) -> Prop) -> (state H) -> Prop.

Definition path := 
(fun  (pi : nat -> (state H)) =>
forall n : nat, (trans H) (pi n) (pi (S n))): (nat -> (state H)) -> Prop.

Definition p_until := 
  (fun (p: (state H) -> Prop)(q : (state H) -> Prop) (pi : nat -> (state H)) => 
                    exists2 n : nat, forall m : nat, m < n -> p (pi m) & q (pi n))
                    :((state H) -> Prop) -> ((state H) -> Prop) -> (nat -> (state H)) -> Prop.

Definition pAU:= 
  (fun (p: (state H) -> Prop) (q: (state H) -> Prop) => 
      fun (w : (state H)) => 
          forall (pi : nat -> (state H)), path pi -> (pi 0 = w) -> p_until p q pi) 
      : ((state H) -> Prop) -> ((state H) -> Prop) -> (state H) -> Prop .

Definition p_release:= 
  (fun (p: (state H) -> Prop) (q: (state H) -> Prop) (pi : nat -> (state H)) =>
  forall n : nat, (exists2 m : nat, m < n & p (pi m)) \/ q (pi n))
  :((state H) -> Prop) -> ((state H) -> Prop) -> (nat -> (state H)) -> Prop .

Definition pAR: ((state H) -> Prop) -> ((state H) -> Prop) -> (state H) -> Prop := 
fun (p: (state H) -> Prop) (q: (state H) -> Prop) => 
  fun (w : (state H)) =>
    forall (pi : nat -> (state H)), path pi -> (pi 0 = w) -> p_release p q pi.
End Characerization.

Inductive form : Type :=
| fF    : form
| fV    : nat -> form
| fImp  : form -> form -> form
| fAX   : form -> form
| fAR   : form -> form -> form 
| fAU   : form -> form -> form.

Fixpoint satisfies (M : sts) (s : form){struct s}: state M -> Prop := 
  (match s with
  | fF        => fun w : state M => False
  | fV v      => fun w : state M => label M v w
  | fImp s0 t => fun w : state M => satisfies M s0 w -> satisfies M t w
  | fAX  s0   => fun w : state M => cAX (satisfies M s0) w
  | fAR  s0 t => fun w : state M => pAR (satisfies M s0) (satisfies M t) w
  | fAU  s0 t => fun w : state M => pAU (satisfies M s0) (satisfies M t) w
  end: state M -> Prop ).


Inductive   bool : Set :=  true : bool | false : bool.
Definition  trans_bool (s1:bool)(s2:bool):Prop := ~ (s1 = s2).
Definition  label_bool(v: nat)(s:bool):Prop := v = (match s with | false => 0 | true => 1 end).
Definition  serial_bool: forall w:bool, exists v, trans_bool w v.
intros. case w; [> eexists false|eexists true] ;compute;discriminate.
Defined.
Definition  init_bool(s: bool):Prop := s = false.
Definition  model_bool: sts := 
@STS bool trans_bool init_bool label_bool serial_bool .


Theorem check1: forall st: state model_bool, 
(init model_bool) st -> 
satisfies(model_bool) (fAX (( (fV 1)))) st.
Proof.
  compute.
  intros. destruct v. auto. apply H0 in H. refine (match H with end).
Defined.
