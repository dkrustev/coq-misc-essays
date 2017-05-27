(* author: Dimitur Krustev *)
(* started: 20170526 *)

Require Import ZArith List.

Open Scope Z_scope.

Definition Model := Z.

Definition model : Model := 0.

Inductive Msg := Increment | Decrement.

Definition update (msg: Msg) (model: Model) : Model :=
  match msg with
  | Increment => model + 1
  | Decrement => model - 1
  end.

(* *** *)

Theorem update_ok: forall (msgs: list Msg) (model: Model), 
  let decrements := filter (fun msg => 
    match msg with Decrement => true | _ => false end) msgs in
  let increments := filter (fun msg => 
    match msg with Increment => true | _ => false end) msgs in
  fold_left (fun model msg => update msg model) msgs model
    = model + Zlength increments - Zlength decrements.
Proof.
  induction msgs.
  - simpl. unfold Zlength. simpl. intros. unfold Model in *. ring.
  - simpl. destruct a.
    + simpl. intros. rewrite Zlength_cons. 
      rewrite IHmsgs.
      unfold Model in *. ring.
    + simpl. intros. rewrite Zlength_cons. 
      rewrite IHmsgs.
      unfold Model in *. ring.
Qed.

(* *** *)

Extraction Language Haskell.
Require ExtrHaskellBasic.
Require ExtrHaskellZInt.

Recursive Extraction update.
