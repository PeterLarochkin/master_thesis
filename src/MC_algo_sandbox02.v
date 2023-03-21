Require Import MC_CTL.
Require Import List. Import ListNotations.
Require Import Lia.


Definition from_trans_to_Prop{A}(list_connections: list (A*A)): A -> A -> Prop :=
(fun s1 s2 =>
  let fix make_prop (list_connections: list (A*A)):Prop :=
    match list_connections with 
    | (b1,b2)::nil => (s1 = b1 -> (s2 = b2))
    | (b1,b2)::tail => (s1 = b1 -> (s2 = b2)) /\ (make_prop tail)
    | nil => False
    end in 
  make_prop list_connections).

Definition from_label_to_Prop{A}(list_label: list (A*nat)):nat -> A -> Prop:=
  (fun v s =>
    let fix make_prop (list_label: list (A*nat)):Prop :=
      match list_label with 
      | (b,n)::nil => (s = b -> v = n)
      | (b,n)::tail => (s = b -> v = n) /\ (make_prop tail)
      | nil => False
      end in 
    make_prop list_label).

Definition from_init_to_Prop{A}(list_init: list A):A->Prop :=
(fun s =>
  let fix make_prop (list_init: list A):Prop :=
    match list_init with 
    | b::nil => s = b
    | b::tail => (s = b) \/ (make_prop tail)
    | nil => False
    end in 
  make_prop list_init) 
.


Inductive   triangle : Set :=  one | two | three.
Definition  trans_triangle := from_trans_to_Prop [(one, two);(two, one);(three, one)].

Definition  label_triangle := from_label_to_Prop [(one, 1); (two, 0); (three,1)].

Definition  serial_triangle: forall w:triangle, exists (v:triangle), trans_triangle w v.
intro. case w. 
eexists two. compute. split;auto. split; intro; discriminate.
eexists one. compute. repeat split. auto. 
eexists one. compute. repeat split. intro; discriminate.
Defined.


Definition init_triangle := from_init_to_Prop [three].
Definition model_triangle: sts :=  {| 
  state   := triangle; 
  trans   := trans_triangle; 
  init    := init_triangle; 
  label   := label_triangle; 
  serial  := serial_triangle 
|}.

Theorem f1ax: forall st: state model_triangle, 
(init model_triangle) st -> 
satisfies (model_triangle) (fAX (fV 0)) st.
Proof.
  intros.
  compute.
  intros. repeat split. Focus 2. intro. compute in H. destruct H0. destruct H2. apply H3 in H. rewrite H in H1. discriminate.
  intro pre. destruct H0. destruct H1. compute in H.
Admitted.
(* works! *)

(* pose proof (is_path_l 1) as is_path_st_l.
  compute in is_path_st_l. *)
Definition gen_cases (n:nat):Prop := 
forall m:nat, (S m) <= n ->
let fix gen n := 
match n with 
| S O => (m = 0)
| S n' => (m = n') \/ (gen n')
| O => False
end
in
gen n
.


Definition usefull: forall m n:nat, S m <= n -> S m = n \/ S m <= n - 1.
lia.
Defined. 

Definition usefull2: forall m n:nat, S m = S n -> m = n .
lia.
Defined.
Definition usefull3: forall m n:nat, m <= n -> m - 1 <= n - 1.
lia.
Defined. 
Theorem F1AU: forall st: state model_triangle, 
(init model_triangle) st -> 
satisfies (model_triangle) (fAU (fV 1)(fV 0)) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l. compute in init_l.
  let path_pi := fresh "path_pi" in
  intro path_pi.
  let is_path_pi := fresh "is_path_pi" in
  intro is_path_pi.
  let first_state:= fresh "first_state" in
  intro first_state.
  compute.

  
  let solve_AU n path_pi is_path_pi first_state := 
    
    eexists n;
    
    [
      auto;
      let m := fresh "m" in
      let le_m := fresh "le_m" in
      intro m;
      intro le_m
       ;
      repeat split
      ;
      (
        let pre := fresh "pre" in
        
        intro pre
        
        
        ;
        apply le_S_S in le_m;
        destruct le_m
      )
      | auto
      (* let solve_m :=
      let progress_in_edges m first_state :=
        let is_path_pi_0:= fresh "is_path_pi_0" in
        pose proof (is_path_pi m) as is_path_pi_0; compute in is_path_pi_0; 
        repeat let a := fresh "is_path_pi_0" in
        destruct is_path_pi_0 as (a&is_path_pi_0);
        (apply a in first_state) + (apply is_path_pi_0 in first_state)
      in
      intro pre;
      rewrite init_l in first_state;
      progress_in_edges 0 first_state;
      progress_in_edges 1 first_state;
      rewrite first_state in pre; discriminate 
    in 
    repeat split;solve_m *)
      (* let solve_m :=
        let progress_in_edges m first_state :=
          let is_path_pi_0:= fresh "is_path_pi_0" in
          pose proof (is_path_pi m) as is_path_pi_0; 
          compute in is_path_pi_0; 
          repeat let a := fresh "is_path_pi_0" in
          destruct is_path_pi_0 as (a&is_path_pi_0);
          (apply a in first_state) + (apply is_path_pi_0 in first_state)
        in
        
        let rec iter n := 
          iter(n-1);progress_in_edges n first_state
        in
        intro pre;
        rewrite init_l in first_state;
        iter n;
        rewrite first_state in pre; discriminate 
      in 
      repeat split;solve_m *)
    ]
  in
  (* solve_AU 2 path_pi is_path_pi first_state. *)
  eexists 2 (*n*).
  {
    let m := fresh "m" in
    intro m.
    let le_m := fresh "le_m" in
    intro le_m.
    repeat split.
    {
      intro pre.
      repeat apply usefull in le_m.

      (* let le_S_S :=  fresh "le_S_S" in
      assert (le_S_S: forall m, (S m) <= 2 -> m = 1 \/ m = 0). lia.
      apply le_S_S in le_m. *)
      destruct le_m.
      
        apply usefull2 in H.
        rewrite H in pre.
        rewrite init_l in first_state.
        pose proof (is_path_pi 0) as is_path_pi_0. compute in is_path_pi_0. 
        repeat let a := fresh "is_path_pi_0" in
        destruct is_path_pi_0 as (a&is_path_pi_0); 
        try (apply is_path_pi_0 in first_state;rewrite first_state in pre; discriminate).
      
        apply usefull in H.
        compute in H.
        apply usefull2 in H.
        rewrite H in pre.
        rewrite init_l in first_state.
        pose proof (is_path_pi 0) as is_path_pi_0. compute in is_path_pi_0. 
        repeat let a := fresh "is_path_pi_0" in
        destruct is_path_pi_0 as (a&is_path_pi_0); 
        try (apply is_path_pi_0 in first_state;rewrite first_state in pre; discriminate).

      }


      { (*case k < m*)
        rewrite H in pre.
        rewrite init_l in first_state.
        pose proof (is_path_pi 0) as is_path_pi_0. compute in is_path_pi_0. 
        repeat let a := fresh "is_path_pi_0" in
        destruct is_path_pi_0 as (a&is_path_pi_0); 
        try (apply is_path_pi_0 in first_state;rewrite first_state in pre; discriminate).
      }
      {  (*case 0 = m*)
        rewrite H in pre.
        rewrite init_l in first_state.
        rewrite first_state in pre. discriminate.
      }
    }
  }
  {
    (* proof that m=2 is ok *)
    let solve_m :=
      let progress_in_edges m first_state :=
        let is_path_pi_0:= fresh "is_path_pi_0" in
        pose proof (is_path_pi m) as is_path_pi_0; compute in is_path_pi_0; 
        repeat let a := fresh "is_path_pi_0" in
        destruct is_path_pi_0 as (a&is_path_pi_0);
        (apply a in first_state) + (apply is_path_pi_0 in first_state)
      in
      intro pre;
      rewrite init_l in first_state;
      progress_in_edges 0 first_state;
      progress_in_edges 1 first_state;
      rewrite first_state in pre; discriminate 
    in 
    repeat split;solve_m.
  }
Defined.
  