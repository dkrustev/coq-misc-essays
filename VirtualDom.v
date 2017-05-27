(* author: Dimitur Krustev *)
(* started: 20170526 *)

Require Import List.
Require String.
Require Fin.

Fixpoint optionMap {A B: Type} (f: A -> option B) (xs: list A) : option (list B) :=
  match xs with
  | nil => Some nil
  | x::xs => match f x with
    | None => None
    | Some y => match optionMap f xs with
      | None => None
      | Some ys => Some (y::ys)
      end
    end
  end.

(* *** *)

Inductive VDom := 
  VText (t: String.string) | VElement (name: String.string) (children: list VDom).

Inductive DomNode (heapSize: nat) : Set  := 
  | DomText (t: String.string) 
  | DomElement (name: String.string) (children: list (Fin.t heapSize)).

Record Dom := MkDom {
  size: nat;
  nodes: Fin.t size -> DomNode size;
  root: Fin.t size;
  }.

Fixpoint dom2vdomHelper {size} (nodes: Fin.t size -> DomNode size)
  (root: Fin.t) (seen: Fin.t size -> bool) {struct size} : option VDom :=
  match size with
  | 0 => None
  | S size => 
    if seen root then None
    else match nodes root with
      | DomText t => Some (VText t)
      | DomElement name els =>
    



