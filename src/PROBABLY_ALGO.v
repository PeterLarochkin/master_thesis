Require Import MC_CTL.
Require Import List. Import ListNotations.
Require Import Lia.

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



Ltac SOLVE_FV' init_l := (*solve satisfies model (fV ?) (?st) problem *)
  repeat split;
  let pre := fresh "pre" in
  intro pre; 
  rewrite init_l in pre; 
  discriminate
.