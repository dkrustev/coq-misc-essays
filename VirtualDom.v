(* author: Dimitur Krustev *)
(* started: 20170526 *)

(* partially inspired by: https://medium.com/@deathmood/how-to-write-your-own-virtual-dom-ee74acc13060 *)

Require Import List Arith.
Require String.
Require Fin.

(*
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

Section MonadOps.

Variable M: Type -> Type.
Variable mret: forall {X}, X -> M X.
Variable mbind: forall {X Y}, M X -> (X -> M Y) -> M Y.

Fixpoint mapM {A B} (f: A -> M B) (xs: list A) {struct xs} : M (list B) :=
  match xs with
  | nil => mret _ nil
  | x::xs => mbind _ _ (f x) (fun y => mbind _ _ (mapM f xs) (fun ys => mret _ (y::ys)))
  end.

End MonadOps.

Implicit Arguments mapM [M A B].
*)

(* *** *)

Inductive State (S A: Type) := MkState (f: S -> A * S).
Implicit Arguments MkState [S A].

Definition stRet {S A} (x: A) : State S A := MkState (fun s => (x, s)).
Definition stBind {S A B} (m: State S A) (f: A -> State S B) : State S B :=
  let '(MkState g) := m in MkState (fun s0 : S =>
     let '(a, s1) := g s0 in
     let '(MkState h) := f a in
     h s1).

Definition stGet {S} : State S S := MkState (fun s => (s, s)).
Definition stPut {S} (s: S) : State S unit := MkState (fun _ => (tt, s)).
Definition stRun {S A} (m: State S A) (s0: S) : A * S :=
  let '(MkState f) := m in f s0.

Notation "m >>= f" := (stBind m f) (at level 50, left associativity).
Notation "'do' a <- e ; c" := (e >>= (fun a => c)) (at level 60, right associativity).

(*
Fixpoint stMapM {S A B} (f: A -> State S B) (xs: list A) : State S (list B) :=
  match xs with
  | nil => stRet nil
  | x::xs => stBind (f x) (fun y => stBind (stMapM f xs) (fun ys => stRet (y::ys)))
  end.
*)

(* *** *)

Section VDom.

Variable Dom: Type.
Variable DomNode: Type.

Inductive DomNodeType := TextNode | ElementNode.

Record DomOps := MkDomOps {
  (* nodeEqDec: forall x y: DomNode, {x = y} + {x <> y}; *)
  getNodeType: DomNode -> State Dom DomNodeType;
  childrenCount: DomNode -> State Dom nat;
  getChildNode: DomNode -> nat -> State Dom DomNode;
  createTextNode: String.string -> State Dom DomNode;
  createElement: String.string -> State Dom DomNode;
  appendChild: DomNode -> DomNode -> State Dom unit;
  removeChildAt: DomNode -> nat -> State Dom unit;
  replaceChildAt: DomNode -> nat -> DomNode -> State Dom unit;
  getTagName: DomNode -> State Dom String.string;
  getText: DomNode -> State Dom String.string;
  setText: DomNode -> String.string -> State Dom unit;
  }.

Variable domOps: DomOps.

Inductive VDomNode := 
  VText (t: String.string) | VElement (name: String.string) (children: list VDomNode).

Fixpoint createNode (node: VDomNode) : State Dom DomNode :=
  let createNodes := fix createNodes (parent: DomNode) (nodes: list VDomNode) 
    : State Dom (list DomNode) :=
    match nodes with
    | nil => stRet nil
    | node::nodes => 
      do n <- createNode node;
      do _ <- domOps.(appendChild) parent n;
      do ns <- createNodes parent nodes;
      stRet (n::ns)
    end in
  match node with
  | VText t => domOps.(createTextNode) t
  | VElement name children =>
    do el <- domOps.(createElement) name;
    do els <- createNodes el children;
    stRet el
  end.

Fixpoint updateNode (parent: DomNode) (newNode: VDomNode) (index: nat) {struct newNode} 
  : State Dom unit :=
  let removeNodes := 
    fix removeNodes (parent: DomNode) (from: nat) (count: nat) 
      {struct count} : State Dom unit :=
      stRet tt (* TODO *) 
    in
  let updateNodes := 
    fix updateNodes (parent: DomNode) (newNodes: list VDomNode) (index: nat)
      {struct newNodes} : State Dom unit :=
      match newNodes with
      | nil => stRet tt
      | newNode::newNodes =>
          do _ <- updateNode parent newNode index;
          updateNodes parent newNodes (S index)
      end
    in
  do childCount <- domOps.(childrenCount) parent;
  if index <? childCount
  then 
    do oldNode <- domOps.(getChildNode) parent index;
    do oldNodeType <- domOps.(getNodeType) oldNode;
    match newNode, oldNodeType with
    | VElement name children, ElementNode => 
        do oldName <- domOps.(getTagName) oldNode;
        if String.string_dec name oldName then
          do oldLen <- domOps.(childrenCount) oldNode;
          let newLen := length children in
          do _ <- if newLen <=? oldLen then removeNodes oldNode newLen (oldLen - newLen) else stRet tt;
          updateNodes oldNode children 0
        else
          do node <- createNode newNode;
          domOps.(replaceChildAt) parent index node
    | VText text, TextNode =>
        do oldText <- domOps.(getText) oldNode;
        if String.string_dec text oldText then stRet tt
        else domOps.(setText) oldNode text
    | _, _ => 
        do node <- createNode newNode;
        domOps.(replaceChildAt) parent index node
    end
  else
    do node <- createNode newNode;
    domOps.(appendChild) parent node.

(*
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
*)


End VDom.
