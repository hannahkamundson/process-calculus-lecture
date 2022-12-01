Require Import String Arith List Lia.
Import ListNotations.

(* 
First, we will define name as we did in the lecture notes.
*)
Definition var := string.

(* 
Then we need to define the labels for the in and out. 
*)
Inductive label :=
    | In (name: var)
    | Out (name: var)
.

(* 
And we need to define actions including the internal action, Tau.
 *)
Inductive action :=
    | Label (l: label)
    | Tau
.

Definition complement (a: action) : action :=
    match a with
    | Label (In n) => Label (Out n)
    | Label (Out n) => Label (In n)
    | Tau => Tau
end.

Definition action_eq (a b: action) : bool :=
    match a with 
    | Label (In n) => match b with
                        | Label (In m) => eqb n m
                        | _ => false
                        end
    | Label (Out n) => match b with
                        | Label (Out m) => eqb n m
                        | _ => false
                        end
    | Tau => match b with 
                | Tau => true
                | _ => false
                end
end.

    
(* 
We can now define all of our proess expressions as we did in the lecture notes.
 *)
Inductive expr :=
    | Skip 
    | Const (v: var) (e: expr)
    | Action (a: action) (e: expr)
    | Sum (e1 e1: expr)
    | Comp (e1 e2: expr)
    | Rest (e: expr) (a: action)
    | Relab (e: expr) (from to: label)
.

(* 
Now, let's define our labelling transition step semantics.
 *)
Inductive expr_step: expr -> action -> expr -> Prop :=
    (* The name of the constant can step to the same place that the expression can step *)
    | expr_step_const               : forall (v: var) (e1 e2: expr) (a: action),
                                        expr_step e1 a e2 ->
                                        expr_step (Const v e1) a e2

    (* The action describes the step that can be taken *)
    | expr_step_act                 : forall (e: expr) (a: action),
                                        expr_step (Action a e) a e

    (* If the left side of a sum can take a step, then the entire expression can take a step there *)
    | expr_step_sum_left            : forall (e1 e1' e2: expr) (a: action),
                                        expr_step e1 a e1' ->
                                        expr_step (Sum e1 e2) a e1'

    (* If the right side of a sum can take a step, then the entire expression can take a step there *)
    | expr_step_sum_right           : forall (e1 e2 e2': expr) (a: action),
                                        expr_step e2 a e2' ->
                                        expr_step (Sum e1 e2) a e2'
    
    
    (* If the left side of a composition can take a step, then the entire expression can take a step there where the left side is modified *)                                
    | expr_step_comp_left           : forall (e1 e1' e2: expr) (a: action),
                                        expr_step e1 a e1' ->
                                        expr_step (Comp e1 e2) a e1'
    
    (* If the right side of a composition can take a step, then the entire expression can take a step there where the right side is modified *)                                
    | expr_step_comp_right          : forall (e1 e2 e2': expr) (a: action),
                                        expr_step e2 a e2' ->
                                        expr_step (Comp e1 e2) a e2'   
    
    (* If the actions are internal to the composition, we can step to the next composite expression with tau *)
    | expr_step_comp_internal       : forall (e1 e1' e2 e2': expr) (a: action),
                                        expr_step e1 a e1' ->
                                        expr_step e2 (complement a) e2' ->
                                        expr_step (Comp e1 e2) Tau (Comp e1' e2')

    (* The step is preserved as long as the label being restricted isn't the being restricted *)
    | expr_step_res                 : forall (e1 e2: expr) (a b: action),
                                        (action_eq Tau b) = false ->
                                        (action_eq a b) = false -> 
                                        (action_eq (complement a) b) = false ->
                                        expr_step e1 a e2 ->
                                        expr_step (Rest e1 b) a (Rest e2 b)

    (* If you can step between two expressions, then you can step to the relabeling of that action taking into account the relabelling of the state it can step to *)
    | expr_step_rel                 : forall (e1 e2: expr) (a b: label),
                                        expr_step e1 (Label a) e2 ->
                                        expr_step (Relab e1 a b) (Label b) (Relab e2 a b)
    .

(* 
Let's work through the example we did in the lecture notes.
*)
Example class_example:
    forall (e f: expr) (a b: label),
        expr_step (Rest (Comp (Sum (Action (Label a) e) (Action (Label b) Skip)) (Action (complement (Label a)) f)) (Label a)) Tau (Rest (Comp e f) (Label a)).
Proof.
    intros.
    eapply expr_step_res.
    - auto. 
    - auto.
    - auto.
    - eapply expr_step_comp_internal.
        + eapply expr_step_sum_left.
            * apply expr_step_act.
        + apply expr_step_act.
Qed.
(* 
It was exactly like the proof in the lecture notes!
*)