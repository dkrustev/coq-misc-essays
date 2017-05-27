(* author: Dimitur Krustev *)
(* started: 20170521 *)

Require Import Arith List.

Fixpoint replicate {A: Type} (n: nat) (x: A) : list A :=
  match n with
  | 0 => nil
  | S n => x :: replicate n x
  end.

Lemma cons_replicate_swap: forall (A: Type) (n: nat) (x: A),
  x :: replicate n x = replicate n x ++ x::nil.
Proof.
  induction n; auto.
  intros. simpl. rewrite IHn. reflexivity.
Qed.

Section RLE.

Variable A: Type.
Variable Adec: forall x y: A, {x = y} + {x <> y}.

Let RLEncHelper := fix RLEncHelper (n: nat) (x: A) (xs: list A) : list (nat * A) :=
  match xs with
  | nil => (n, x)::nil
  | x1::xs => match Adec x x1 with
    | left Heq => RLEncHelper (S n) x xs
    | right Hneq => (n, x) :: RLEncHelper 1 x1 xs
    end
  end.

Definition RLEnc (xs: list A) : list (nat * A) :=
  match xs with
  | nil => nil
  | x::xs => RLEncHelper 1 x xs
  end.

Definition RLDec (nxs: list (nat * A)) : list A :=
  flat_map (fun nx => let '(n, x) := nx in replicate n x) nxs.

Lemma RLEncHelper_correct: forall n x xs, RLDec (RLEncHelper n x xs) = replicate n x ++ xs.
Proof.
  intros. revert n x. induction xs; auto.
  { intros. simpl. destruct (Adec x a) as [Heq | Hneq].
    - subst. rewrite IHxs. simpl.
      change ((a :: replicate n a) ++ xs = replicate n a ++ a :: xs).
      rewrite cons_replicate_swap.
      rewrite <- app_assoc. reflexivity.
    - simpl. rewrite IHxs. reflexivity.
  }
Qed.

Theorem RLEnc_correct: forall xs, RLDec (RLEnc xs) = xs.
Proof.
  destruct xs.
  - simpl. reflexivity.
  - simpl. apply RLEncHelper_correct.
Qed.

End RLE.

Recursive Extraction RLDec RLEnc.