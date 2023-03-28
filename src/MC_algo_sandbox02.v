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



Ltac SOLVE_AU STATE_SIZE init_l := 
let solve_AU max_of_state :=
  let path_pi := fresh "path_pi" in
  intro path_pi;
  let is_path_pi := fresh "is_path_pi" in
  intro is_path_pi;
  let first_state:= fresh "first_state" in
  intro first_state;
  compute;
  let rec sol_AU n :=
  tryif (let h:= fresh "h" in assert(h: n + 1 <= max_of_state); [progress auto | auto])
  then
    (eexists n (*n*); 
    [
      auto;
        let m := fresh "m" in
        let le_m := fresh "le_m" in
        intro m;
        intro le_m;
        repeat split;
        (
          let pre := fresh "pre" in
          intro pre;
          let rec solve_rec m le_m pre := 
            apply usefull in le_m; compute in le_m;
            let first_case := fresh "first_case" in
            let second_case := fresh "second_case" in
            destruct le_m as [ first_case | second_case]; 
            [> 
            (apply usefull2 in first_case;
              rewrite first_case in pre;
              rewrite init_l in first_state;
              rewrite first_state in pre; discriminate) +
              (apply usefull2 in first_case;
              rewrite first_case in pre;
              rewrite init_l in first_state;
              pose proof (is_path_pi 0) as is_path_pi_0; compute in is_path_pi_0;
              repeat let a := fresh "is_path_pi_0" in
              destruct is_path_pi_0 as (a&is_path_pi_0);
              try ((apply a in first_state)+(apply is_path_pi_0 in first_state);rewrite first_state in pre; discriminate) )
              
            | 
              lia +  
              (solve_rec (m-1) second_case pre) + auto
            ]
          in
          (solve_rec m le_m pre)
        )
        
      |
        compute;
        rewrite init_l in first_state ;  
        repeat split;
        let pre := fresh "pre" in
        let H := fresh "H" in
        intro pre;
        (
          
  
            let rec progress_in_edges m first_state :=
              
              ((
                let is_path_pi_0:= fresh "is_path_pi_0" 
                in
                pose proof (is_path_pi m) as is_path_pi_0; 
                compute in is_path_pi_0; 
                repeat (
                  let a := fresh "is_path_pi_0" in
                  destruct is_path_pi_0 as (a&is_path_pi_0);
                  (apply a in first_state) + (apply is_path_pi_0 in first_state)
                );
                rewrite first_state in pre; discriminate
                ;
                try (apply is_path_pi_0 in first_state;rewrite first_state in pre; discriminate)
              ) 
              +
              (
                (
                  let is_path_pi_0:= fresh "is_path_pi_0" 
                  in
                  pose proof (is_path_pi m) as is_path_pi_0; 
                  compute in is_path_pi_0; 
                  repeat (
                    let a := fresh "is_path_pi_0" in
                    destruct is_path_pi_0 as (a&is_path_pi_0);
                    (apply a in first_state) + (apply is_path_pi_0 in first_state)
                  );
                  tryif (let h:= fresh "h" in assert(h: m+1 < n); [progress auto| auto])
                  then
                  progress_in_edges (m+1) first_state 
                  else 
                  fail "progress_in_edges: with" m "and 1"
                )
              ))
            in
            progress_in_edges 0 first_state
        )
    ])
    +
    sol_AU (n + 1)
  else 
  fail "solve_AU: with" n
  in
  sol_AU 0
in
(* auto. *)
solve_AU STATE_SIZE.




  Theorem F1AU: forall st: state model_triangle, 
(init model_triangle) st -> 
satisfies (model_triangle) (fAU (fV 1)(fV 0)) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l. compute in init_l.
  
  let solve_AU max_of_state :=
    let path_pi := fresh "path_pi" in
    intro path_pi;
    let is_path_pi := fresh "is_path_pi" in
    intro is_path_pi;
    let first_state:= fresh "first_state" in
    intro first_state;
    compute;
    let rec sol_AU n :=
    tryif (let h:= fresh "h" in assert(h: n + 1 <= max_of_state); [progress auto | auto])
    then
      (eexists n (*n*); 
      [
        auto;
          let m := fresh "m" in
          let le_m := fresh "le_m" in
          intro m;
          intro le_m;
          repeat split;
          (
            let pre := fresh "pre" in
            intro pre;
            let rec solve_rec m le_m pre := 
              apply usefull in le_m; compute in le_m;
              let first_case := fresh "first_case" in
              let second_case := fresh "second_case" in
              destruct le_m as [ first_case | second_case]; 
              [> 
              (apply usefull2 in first_case;
                rewrite first_case in pre;
                rewrite init_l in first_state;
                rewrite first_state in pre; discriminate) +
                (apply usefull2 in first_case;
                rewrite first_case in pre;
                rewrite init_l in first_state;
                pose proof (is_path_pi 0) as is_path_pi_0; compute in is_path_pi_0;
                repeat let a := fresh "is_path_pi_0" in
                destruct is_path_pi_0 as (a&is_path_pi_0);
                try (apply is_path_pi_0 in first_state;rewrite first_state in pre; discriminate) )
                
              | 
                lia +  
                (solve_rec (m-1) second_case pre) + auto
              ]
            in
            (solve_rec m le_m pre)
          )
          
        |
          compute;
          rewrite init_l in first_state ;  
          repeat split;
          let pre := fresh "pre" in
          let H := fresh "H" in
          intro pre;
          (
            
    
              let rec progress_in_edges m first_state :=
                
                ((
                  let is_path_pi_0:= fresh "is_path_pi_0" 
                  in
                  pose proof (is_path_pi m) as is_path_pi_0; 
                  compute in is_path_pi_0; 
                  repeat (
                    let a := fresh "is_path_pi_0" in
                    destruct is_path_pi_0 as (a&is_path_pi_0);
                    (apply a in first_state) + (apply is_path_pi_0 in first_state)
                  );
                  rewrite first_state in pre; discriminate
                  ;
                  try (apply is_path_pi_0 in first_state;rewrite first_state in pre; discriminate)
                ) 
                +
                (
                  (
                    let is_path_pi_0:= fresh "is_path_pi_0" 
                    in
                    pose proof (is_path_pi m) as is_path_pi_0; 
                    compute in is_path_pi_0; 
                    repeat (
                      let a := fresh "is_path_pi_0" in
                      destruct is_path_pi_0 as (a&is_path_pi_0);
                      (apply a in first_state) + (apply is_path_pi_0 in first_state)
                    );
                    tryif (let h:= fresh "h" in assert(h: m+1 < n); [progress auto| auto])
                    then
                    progress_in_edges (m+1) first_state 
                    else 
                    fail "progress_in_edges: with" m "and 1"
                  )
                ))
              in
              progress_in_edges 0 first_state
          )
      ])
      +
      sol_AU (n + 1)
    else 
    fail "solve_AU: with" n
    in
    sol_AU 0
  in
  (* auto. *)
  SOLVE_AU 3 init_l.
  (* eexists 2 (*n*); 
  [
    auto;
      let m := fresh "m" in
      let le_m := fresh "le_m" in
      intro m;
      intro le_m;
      repeat split;
      (
        let pre := fresh "pre" in
        intro pre;
        let rec solve_rec m le_m pre := 
          apply usefull in le_m; compute in le_m;
          let first_case := fresh "first_case" in
          let second_case := fresh "second_case" in
          destruct le_m as [ first_case | second_case]; 
          [> 
          (apply usefull2 in first_case;
            rewrite first_case in pre;
            rewrite init_l in first_state;
            rewrite first_state in pre; discriminate) +
            (apply usefull2 in first_case;
            rewrite first_case in pre;
            rewrite init_l in first_state;
            pose proof (is_path_pi 0) as is_path_pi_0; compute in is_path_pi_0;
            repeat let a := fresh "is_path_pi_0" in
            destruct is_path_pi_0 as (a&is_path_pi_0);
            try (apply is_path_pi_0 in first_state;rewrite first_state in pre; discriminate) )
            
          | 
            lia +  
            (solve_rec (m-1) second_case pre) + auto
          ]
        in
        (solve_rec m le_m pre)
      )
      
    |
      
      rewrite init_l in first_state ;  
      repeat split;
      let pre := fresh "pre" in
      let H := fresh "H" in
      intro pre;
      (
        

          let rec progress_in_edges m first_state :=
            
            ((
              let is_path_pi_0:= fresh "is_path_pi_0" 
              in
              pose proof (is_path_pi m) as is_path_pi_0; 
              compute in is_path_pi_0; 
              repeat (
                let a := fresh "is_path_pi_0" in
                destruct is_path_pi_0 as (a&is_path_pi_0);
                (apply a in first_state) + (apply is_path_pi_0 in first_state)
              );
              rewrite first_state in pre; 
              discriminate;
              try (apply is_path_pi_0 in first_state;rewrite first_state in pre; discriminate)
            ) 
            +
            (
              (
                let is_path_pi_0:= fresh "is_path_pi_0" 
                in
                pose proof (is_path_pi m) as is_path_pi_0; 
                compute in is_path_pi_0; 
                repeat (
                  let a := fresh "is_path_pi_0" in
                  destruct is_path_pi_0 as (a&is_path_pi_0);
                  (apply a in first_state) + (apply is_path_pi_0 in first_state)
                );
                tryif (let h:= fresh "h" in assert(h: m+1 < 2); [progress auto| auto])
                then
                progress_in_edges (m+1) first_state 
                else 
                fail "progress_in_edges: with" m "and 1"
              )
            ))
          in
          progress_in_edges 0 first_state
      )
  ]. *)
Defined.



Definition from_trans_to_Prop2{A}(list_connections: list (A*A)): A -> A -> Prop :=
(fun s1 s2 =>
  let fix make_prop (list_connections: list (A*A)):Prop :=
    match list_connections with 
    | (b1,b2)::nil => (s1 = b1 /\ (s2 = b2))
    | (b1,b2)::tail => (s1 = b1 /\ (s2 = b2)) \/ (make_prop tail)
    | nil => False
    end in 
  make_prop list_connections).
(* Testing AU tactic *)
Inductive   sq : Set :=  one_sq | two_sq | three_sq | four_sq.
Definition  trans_sq := fun x x0 : sq =>
(x = three_sq -> x0 = four_sq) /\
(x = four_sq -> ((x0 = one_sq) \/ (x0 = two_sq))) /\
(x = two_sq -> x0 = two_sq) /\ (x = one_sq -> x0 = one_sq).
  (* from_trans_to_Prop [(three_sq, four_sq);(four_sq, one_sq);(four_sq, two_sq); (two_sq, two_sq); (one_sq, one_sq)]. *)
Compute trans_sq.
Definition  label_sq := from_label_to_Prop [(one_sq, 0); (two_sq, 0); (three_sq,1); (four_sq, 1)].

Definition  serial_sq: forall w:sq, exists (v:sq), trans_sq w v.
intro; case w;[eexists one_sq | eexists two_sq | eexists four_sq | eexists one_sq].
compute. repeat split; intro; discriminate.
compute. repeat split; intro; discriminate.
compute. repeat split; intro; discriminate.
compute. repeat split; intro. try discriminate. left. auto. discriminate.
Defined.


Definition init_sq := from_init_to_Prop [three_sq].
Definition model_sq: sts :=  {| 
  state   := sq; 
  trans   := trans_sq; 
  init    := init_sq; 
  label   := label_sq; 
  serial  := serial_sq 
|}.
Ltac test_ltb_m_n m n:=
assert (m < n);progress auto
.

Ltac SOLVE_AU2 n max_of_state init_l := 
let solve_AU max_of_state :=
  let path_pi := fresh "path_pi" in
  intro path_pi;
  let is_path_pi := fresh "is_path_pi" in
  intro is_path_pi;
  let first_state:= fresh "first_state" in
  intro first_state;
  compute;
  let rec sol_AU n :=
  tryif (let h:= fresh "h" in assert(h: n <= max_of_state); [progress auto | auto])
  then
    (
      eexists n (*n*); 
      [
          auto;
          let m := fresh "m" in
          let le_m := fresh "le_m" in
          intro m;
          intro le_m;
          repeat split;
          (
            let pre := fresh "pre" in
            intro pre;
            let rec solve_rec m le_m pre := 
              apply usefull in le_m; compute in le_m;
              let first_case := fresh "first_case" in
              let second_case := fresh "second_case" in
              destruct le_m as [ first_case | second_case]; 
              [> 
              (apply usefull2 in first_case;
                rewrite first_case in pre;
                rewrite init_l in first_state;
                rewrite first_state in pre; discriminate) +
                (apply usefull2 in first_case;
                rewrite first_case in pre;
                rewrite init_l in first_state;
                pose proof (is_path_pi 0) as is_path_pi_0; compute in is_path_pi_0;
                repeat let a := fresh "is_path_pi_0" in
                destruct is_path_pi_0 as (a&is_path_pi_0);
                try ((apply a in first_state)+(apply is_path_pi_0 in first_state);rewrite first_state in pre; discriminate) )
                
              | 
                lia +  
                (solve_rec (m-1) second_case pre) + auto
              ]
            in
            (solve_rec m le_m pre)
          )
        |
        let progress_in_edges n :=
          compute;
          rewrite init_l in first_state ;  
          repeat split;
          let pre := fresh "pre" in
          intro pre;
          let rec through_edge m first_state := 
            (
              lazymatch goal with 
              | first_state: ?K \/ ?L |- _ => (destruct first_state as [first_state|first_state])
              | first_state: _ |- _ => idtac
              end
            );
            (let is_path_pi_0:= fresh "is_path_pi_0" in
            pose proof (is_path_pi m) as is_path_pi_0; 
            compute in is_path_pi_0; 
            repeat (
              let a := fresh "is_path_pi_0" in
              destruct is_path_pi_0 as (a&is_path_pi_0);
              ((apply a in first_state) + (apply is_path_pi_0 in first_state))
            ));
            (
              lazymatch goal with 
              | first_state: ?K \/ ?L |- _ => (destruct first_state as [first_state|first_state])
              | first_state: _ |- _ => idtac
              end
            );
            ((rewrite first_state in pre; 
            discriminate)
            +
            (
              tryif (let h:= fresh "h" in assert(h: m + 1 <= n); [progress auto | auto])
              then through_edge (m+1) first_state
              else idtac
              )
            )
          in
          through_edge 0 first_state
        in
        progress_in_edges max_of_state
      ]
    )
    +
    sol_AU (n + 1)
  else 
  fail "solve_AU: with" n
  in
  sol_AU n
in
solve_AU max_of_state .


(* try (destruct first_state; [auto|auto]). *)
Theorem F2AU: forall st: state model_sq, 
(init model_sq) st -> 
satisfies (model_sq) (fAU (fV 1)(fV 0)) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l. compute in init_l.
  SOLVE_AU2 2 4 init_l.
Defined.


Ltac SOLVE_AX init_l := 
  let state_in := fresh "state_in" in
  intro state_in;
  let tr := fresh "tr" in
  intro tr;
  repeat split;
  compute in init_l;
  let pre_state := fresh "pre_state" in
  intro pre_state;
  repeat (
    let a := fresh "a" in
    let b := fresh "b" in
    destruct tr as (a&b);((apply a in init_l) + (apply b in init_l)); rewrite init_l in pre_state; discriminate
  )  
.


Theorem F1AX: forall st: state model_sq, 
(init model_sq) st -> 
satisfies (model_sq) (fAX (fV 1)) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l.
  SOLVE_AX init_l.
Defined.

Ltac SOLVE_AX_AX init_l := 
  let state_in := fresh "state_in" in
  intro state_in;
  let tr := fresh "tr" in
  intro tr;
  repeat split;
  compute in init_l;
  let pre_state := fresh "pre_state" in
  intro pre_state;
  repeat (
    let a := fresh "a" in
    let b := fresh "b" in
    destruct tr as (a&b);((apply a in init_l) + (apply b in init_l)); rewrite init_l in pre_state; discriminate
  )
.

Ltac search_way tr1 init_l pre_state:=
repeat (
    let a := fresh "a" in
    let b := fresh "b" in
    destruct tr1 as (a&b);((apply a in init_l) + (apply b in init_l));
    rewrite init_l in pre_state; discriminate
  )
.


Theorem F1AXAX: forall st: state model_sq, 
(init model_sq) st -> 
satisfies (model_sq) (fAX (fAX (fV 0))) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l.
  let state_in := fresh "state_in" in
  intro state_in.
  let tr := fresh "tr" in
  intro tr.
  compute.
  let new_state_in := fresh "new_state_in" in
  intro new_state_in.
  let tr := fresh "tr" in
  intro tr.
  repeat split;
  let pre_state := fresh "pre_state" in
  intro pre_state;
  compute in tr; compute in init_l;
  repeat (
    let a := fresh "a" in
    let b := fresh "b" in
    destruct tr as (a&b);((apply a in init_l) + (apply b in init_l));
    (
      lazymatch goal with 
      | init_l: ?K \/ ?L |- _ => (destruct init_l as [init_l|init_l])
      | init_l: _ |- _ => idtac
      end
    );
    repeat (
    let a := fresh "a" in
    let b := fresh "b" in
    destruct tr0 as (a&b);((apply a in init_l) + (apply b in init_l));
    (
    lazymatch goal with 
    | init_l: ?K \/ ?L |- _ => (destruct init_l as [init_l|init_l])
    | init_l: _ |- _ => idtac
    end
    )
    ) 
  );rewrite init_l in pre_state; discriminate.
Defined.

(* need to put right init_l *)
Ltac SOLVE_AX' init_l := 
  let state_in := fresh "state_in" in
  intro state_in;
  let tr := fresh "tr" in
  intro tr;
  repeat split;
  compute in init_l;
  let pre_state := fresh "pre_state" in
  intro pre_state;
  repeat (
    let a := fresh "a" in
    let b := fresh "b" in
    destruct tr as (a&b);((apply a in init_l) + (apply b in init_l));
    (
      lazymatch goal with 
      | init_l: ?K \/ ?L |- _ => (destruct init_l as [init_l|init_l])
      | init_l: _ |- _ => idtac
      end
    );
    rewrite init_l in pre_state; discriminate
  )  
.
Theorem F1AX': forall st: state model_sq, 
(init model_sq) st -> 
satisfies (model_sq) ((fAX (fV 1))) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l.
  SOLVE_AX' init_l.
Defined.


Ltac SOLVE_FV init_l st_l := 
  repeat split;
  let pre := fresh "pre" in
  intro pre; 
  rewrite init_l in pre; 
  discriminate
.
Theorem F1_FV: forall st: state model_sq, 
(init model_sq) st -> 
satisfies (model_sq) (fV 1) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l. compute in init_l.
  SOLVE_FV init_l st_l.
Defined.


Ltac SOLVE_AU2' n max_of_state init_l solve_subformula1 solve_subformula2 := 
let solve_AU max_of_state :=
  let path_pi := fresh "path_pi" in
  intro path_pi;
  let is_path_pi := fresh "is_path_pi" in
  intro is_path_pi;
  let first_state:= fresh "first_state" in
  intro first_state;
  compute;
  let (*rec*) sol_AU n :=
  (* tryif (let h:= fresh "h" in assert(h: n <= max_of_state); [progress auto | auto])
  then *)
    (
      eexists n (*n*); 
      [
          auto;
          let m := fresh "m" in
          let le_m := fresh "le_m" in
          intro m;
          intro le_m;
          (
            let rec solve_rec le_m := 
              apply usefull in le_m; (*compute in le_m;*)
              destruct le_m as [ le_m | le_m];
              [>
                apply usefull2 in le_m;
                rewrite init_l in first_state;
                let rec loop_to_needed_m i m :=
                  tryif (let h:= fresh "h" in assert(h: i < m); [progress auto | auto])
                    then 
                        let is_path_pi_i := fresh "is_path_pi_i" in
                        pose proof (is_path_pi i) as is_path_pi_i;
                        compute in is_path_pi_i;
                        repeat (
                          let a := fresh "a" in
                          let b := fresh "b" in
                          destruct is_path_pi_i as (a&b);
                          ((apply a in first_state)+(apply b in first_state));
                          (
                            lazymatch type of first_state with 
                            | _ \/ _ => (repeat destruct first_state as [first_state|first_state])
                            | _ => idtac
                            end
                          );
                          loop_to_needed_m (i + 1) m)
                    else 
                        idtac
                in
                lazymatch type of le_m with 
                | _ = ?k => loop_to_needed_m 0 k
                | _ => idtac
                end
                ;
                rewrite <- le_m in first_state;
                solve_subformula1 first_state
                
              | 
                lia +  
                (solve_rec le_m) + auto
              ]
            in
            (solve_rec le_m)
          )
          
        |
        rewrite init_l in first_state;
        let rec loop_to_needed_m i m :=
          tryif (let h:= fresh "h" in assert(h: i < m); [progress auto | auto])
            then 
                let is_path_pi_i := fresh "is_path_pi_i" in
                pose proof (is_path_pi i) as is_path_pi_i;
                compute in is_path_pi_i;
                repeat (
                  let a := fresh "a" in
                  let b := fresh "b" in
                  destruct is_path_pi_i as (a&b);
                  ((apply a in first_state)+(apply b in first_state));
                  (
                    lazymatch type of first_state with 
                    | _ \/ _ => (repeat destruct first_state as [first_state|first_state])
                    | _ => idtac
                    end
                  );
                  loop_to_needed_m (i + 1) m)
            else 
                fail "loop_to_needed_m"
        in
        loop_to_needed_m 0 2;
        solve_subformula2 first_state
      ]
    )
    (* +
    sol_AU (n + 1)
  else 
    fail "solve_AU: with" n*)
  in 
  sol_AU n
in
solve_AU max_of_state .



Ltac SOLVE_FV' init_l := (*solve satisfies model (fV ?) (?st) probleb *)
  repeat split;
  let pre := fresh "pre" in
  intro pre; 
  rewrite init_l in pre; 
  discriminate
.
Theorem F1_AU_FV: forall st: state model_sq, 
(init model_sq) st -> 
satisfies (model_sq) (fAU (fV 1)((fV 0))) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l. compute in init_l.
  SOLVE_AU2' 2 4  init_l SOLVE_FV' SOLVE_FV'.
Defined.



Ltac SOLVE_AX2' init_l solve_subformula1 := let next_state := fresh "next_state" in 
intro next_state;
let trans_to_new_state := fresh "trans_to_new_state" in 
intro trans_to_new_state;
compute in trans_to_new_state;
repeat (
  let a := fresh "a" in
  let b := fresh "b" in
  destruct trans_to_new_state as (a&b);
  ((apply a in init_l)+(apply b in init_l));
  (
    lazymatch type of init_l with 
    | _ \/ _ => (repeat destruct init_l as [init_l|init_l])
    | _ => idtac
    end
  ));
  solve_subformula1 init_l.

Theorem F1AX'': forall st: state model_sq, 
(st = four_sq) -> 
satisfies (model_sq) ((fAX (fV 0))) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l.
  SOLVE_AX2' init_l SOLVE_FV'.
Defined.


Theorem F1AR: forall st: state model_sq, 
(init model_sq) st -> 
satisfies (model_sq) (fAR (fV 1) (fV 0)) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l.
  (* compute. *)
  let path_pi := fresh "path_pi" in
  intro path_pi.
  let is_path_pi := fresh "is_path_pi" in 
  intro is_path_pi.
  let first_state := fresh "first_state" in
  intro first_state.
  right.
Admitted.

Definition from_trans_to_Prop3{A}(list_connections: list (A * (list A))): A -> A -> Prop :=
(fun s1 s2 =>
  let fix make_disjucntion_for_state_to (states_in: list A) := 
  match states_in with
  | head :: nil => s2 = head
  | head :: tail => s2 = head \/ (make_disjucntion_for_state_to tail)
  | nil => False
  end
  
  in
  let fix make_prop (list_connections: list (A * (list A))):Prop :=
    match list_connections with 
    | (b1,b2)::nil => (s1 = b1 -> (make_disjucntion_for_state_to b2))
    | (b1,b2)::tail => (s1 = b1 -> (make_disjucntion_for_state_to b2)) /\ (make_prop tail)
    | nil => False
    end in 
  make_prop list_connections).

(* FIVE STATES *)
Inductive   fifth : Set :=  one_fi | two_fi | three_fi | four_fi| five_fi.
Definition  trans_fifth := from_trans_to_Prop3 [
  (one_fi, [two_fi]);
  (two_fi, [three_fi; four_fi]);
  (three_fi, [four_fi]);
  (four_fi, [five_fi]); 
  (five_fi, [one_fi])
].

Definition  label_fifth := from_label_to_Prop [(one_fi, 0); (two_fi, 0); (three_fi,0); (four_fi, 1); (four_fi, 0); (five_fi, 0)].

Definition  serial_fifth: forall w:fifth, exists (v:fifth), trans_fifth w v.
intro; case w.
eexists two_fi; compute; repeat split; intro; discriminate.
eexists four_fi; compute. repeat split. intro. discriminate. intro. right. auto.
intro; discriminate.
intro; discriminate.
eexists four_fi; compute. repeat split. intro. discriminate.
intro. discriminate.
intro. discriminate.
intro. discriminate.
eexists five_fi; compute. repeat split; intro; discriminate.
eexists one_fi; compute. repeat split; intro; discriminate.
Defined.


Definition init_fifth := from_init_to_Prop [one_fi].
Definition model_fifth: sts :=  {| 
  state   := fifth; 
  trans   := trans_fifth; 
  init    := init_fifth; 
  label   := label_fifth; 
  serial  := serial_fifth 
|}.

Ltac test_ltb_m_n' m n:=
assert (m < n);progress auto
.
























Ltac SOLVE_AX2'' init_l solve_subformula1 := let next_state := fresh "next_state" in 
intro next_state;
let trans_to_new_state := fresh "trans_to_new_state" in 
intro trans_to_new_state;
compute in trans_to_new_state;
repeat (
  let a := fresh "a" in
  let b := fresh "b" in
  destruct trans_to_new_state as (a&b);
  ((apply a in init_l)+(apply b in init_l));
  (
    lazymatch type of init_l with 
    | _ \/ _ => (repeat destruct init_l as [init_l|init_l])
    | _ => idtac
    end
  ));
  solve_subformula1.

  Theorem usefull4: forall m n, S m = n -> m = n - 1.
  lia.
  Defined.













Ltac SOLVE_AU2'' n max_of_state init_l solve_subformula1 solve_subformula2 := 
let solve_AU max_of_state :=
    let path_pi := fresh "path_pi" in
    intro path_pi;
    let is_path_pi := fresh "is_path_pi" in
    intro is_path_pi;
    let first_state:= fresh "first_state" in
    intro first_state;
    compute;
    let (*rec*) sol_AU n :=
    (* tryif (let h:= fresh "h" in assert(h: n <= max_of_state); [progress auto | auto])
    then *)
    (
        eexists n (*n*); 
        [
            auto;
            let m := fresh "m" in
            let le_m := fresh "le_m" in
            intro m;
            intro le_m;
            (
            let rec solve_rec le_m := 
                apply usefull in le_m; (*compute in le_m;*)
                destruct le_m as [ le_m | le_m];
                [>
                (apply usefull2 in le_m) + lia (* for cases S m = 0*);
                rewrite init_l in first_state;
                try (rewrite <- le_m in first_state;
                solve_subformula1 first_state);
                let rec loop_to_needed_m i m :=
                    tryif (let h:= fresh "h" in assert(h: i < m); [progress auto | auto])
                    then 
                        let is_path_pi_i := fresh "is_path_pi_i" in
                        pose proof (is_path_pi i) as is_path_pi_i;
                        compute in is_path_pi_i;
                        repeat (
                            let a := fresh "a" in
                            let b := fresh "b" in
                            destruct is_path_pi_i as (a&b);
                            ((apply a in first_state)+(apply b in first_state));
                            (
                            lazymatch type of first_state with 
                            | _ \/ _ => (repeat destruct first_state as [first_state|first_state])
                            | _ => idtac
                            end
                            );
                            loop_to_needed_m (i + 1) m)
                    else 
                        idtac
                in
                lazymatch type of le_m with 
                | _ = ?k => loop_to_needed_m 0 k
                | _ => idtac
                end
                ;
                rewrite <- le_m in first_state;
                solve_subformula1 first_state
                
                |
                (compute in le_m;
                lia) +  
                (solve_rec le_m) + auto
                ]
            in
            (solve_rec le_m)
            )
            
        |
        auto;
        rewrite init_l in first_state;
        let rec loop_to_needed_m i m :=
            tryif (let h:= fresh "h" in assert(h: i < m); [progress auto | auto])
            then 
                let is_path_pi_i := fresh "is_path_pi_i" in
                pose proof (is_path_pi i) as is_path_pi_i;
                compute in is_path_pi_i;
                repeat (
                    let a := fresh "a" in
                    let b := fresh "b" in
                    destruct is_path_pi_i as (a&b);
                    ((apply a in first_state)+(apply b in first_state));
                    (
                    lazymatch type of first_state with 
                    | _ \/ _ => (repeat destruct first_state as [first_state|first_state])
                    | _ => idtac
                    end
                    );
                    loop_to_needed_m (i + 1) m)
            else 
                idtac
        in
        loop_to_needed_m 0 n;
        solve_subformula2 first_state
        ]
    )
    (* +
    sol_AU (n + 1)
    else 
    fail "solve_AU: with" n*)
    in 
    sol_AU n
in
solve_AU max_of_state .

Theorem F2_AU_FV: forall st: state model_fifth, 
(init model_fifth) st -> 
satisfies (model_fifth) (fAU (fV 0) (fAX (fV 0))) st.
Proof.
  let st_l := fresh "st_l" in
  intro st_l.
  let init_l := fresh "init_l" in
  intro init_l. compute in init_l.
  let tac := (fun init => SOLVE_AX2' init SOLVE_FV') in 
  SOLVE_AU2'' 0 1 init_l SOLVE_FV' tac.
Defined.
