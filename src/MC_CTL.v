(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)

Section Characterizations.

Variables (X : Type) (e : X -> X -> Prop).
Definition cAX (p : X -> Prop) (w : X) : Prop := forall v, e w v -> p v.
Definition path (pi : nat -> X) := forall n, e (pi n) (pi (S n)).

Definition pcons (x : X) pi (k : nat) := 
match k with
| 0 => x
| S k0 => pi k0 
end.

Definition ptail (pi : nat -> X) (k:nat) : X := pi (S k).

Definition p_until (p q : X -> Prop) pi := 
  exists2 n, forall m, m < n -> p (pi m) & q (pi n).

Definition p_release (p q : X -> Prop) pi := 
  forall n, (exists2 m, m < n & p (pi m)) \/ q (pi n).

Definition pAU (p q : X -> Prop) (w : X) : Prop := 
  forall pi, path pi -> pi 0 = w -> p_until p q pi.

Definition pAR (p q : X -> Prop) (w : X) : Prop := 
  forall pi, path pi -> pi 0 = w -> p_release p q pi.

End Characterizations.
Check cAX.

Definition var := nat.

Inductive form : Set :=
| fF : form
| fV : var -> form
| fImp : form -> form -> form
| fAX : form -> form
| fAR : form -> form -> form
| fAU : form -> form -> form.

Record sts := STS {
  state  :> Type;
  trans  : state -> state -> Prop;
  label  : var -> state -> Prop;
  serial : forall w:state, exists v, trans w v
}.

Arguments trans {s} _ _.
(* Prenex Implicits trans. *)
Arguments cAX [X]%type_scope (e p)%function_scope w.
Arguments pAR [X]%type_scope (e p q)%function_scope w.
Arguments pAU [X]%type_scope (e p q)%function_scope w.
Arguments label [s] _ _.
Fixpoint satisfies (M : sts) (s : form) := 
match s with
| fF       => (fun _ => False)
| fV v     => label v
| fImp s t => (fun w => satisfies M s w -> satisfies M t w)
| fAX s    => cAX (@trans M) (satisfies M s)
| fAR s t  => pAR trans (satisfies M s) (satisfies M t)
| fAU s t  => pAU trans (satisfies M s) (satisfies M t)
end.  