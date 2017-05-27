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
Definition stEval {S A} (m: State S A) s0 := fst (stRun m s0).

Notation "m >>= f" := (stBind m f) (at level 50, left associativity).
Notation "'do' a <- e ; c" := (e >>= (fun a => c)) (at level 60, right associativity).

(*
Fixpoint stMapM {S A B} (f: A -> State S B) (xs: list A) : State S (list B) :=
  match xs with
  | nil => stRet nil
  | x::xs => stBind (f x) (fun y => stBind (stMapM f xs) (fun ys => stRet (y::ys)))
  end.
*)

Require Import FunctionalExtensionality.

Lemma stBind_assoc: forall S A B C (m: State S A) (f: A -> State S B) (g: B -> State S C),
  stBind (stBind m f) g = stBind m (fun x => stBind (f x) g).
Proof.
  destruct m as [fm]. simpl. intros. f_equal. extensionality s0.
  destruct (fm s0) as [a s1]. destruct (f a) as [h]. reflexivity.
Qed.

Lemma stRun_stBind: forall S A B (m: State S A) (f: A -> State S B) s,
  stRun (stBind m f) s = let p := stRun m s in stRun (f (fst p)) (snd p).
Proof.
  destruct m as [g]. simpl. intros. destruct (g s) as [a s1].
  simpl. destruct (f a) as [h]. reflexivity.
Qed.

Lemma stEval_stBind: forall S A B (m: State S A) (f: A -> State S B) s,
  stEval (stBind m f) s = let p := stRun m s in stEval (f (fst p)) (snd p).
Proof.
  destruct m as [g]. simpl. intros. unfold stEval. simpl. destruct (g s) as [a s1].
  simpl. destruct (f a) as [h]. reflexivity.
Qed.

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

(* *** *)

Inductive VDomNode := 
  VText (t: String.string) | VElement (name: String.string) (children: list VDomNode).

Fixpoint vdomDepth (node: VDomNode) : nat :=
  match node with
  | VText _ => 0
  | VElement _ children => S (fold_right max 0 (map vdomDepth children))
  end.

Section VDomNodeFullInd.

Variable P: VDomNode -> Prop.
Variable PText: forall text, P (VText text).
Variable PElement: forall name children, Forall P children -> P (VElement name children).

Fixpoint VDomNode_fullInd (node: VDomNode) : P node :=
  match node with
  | VText text => PText text
  | VElement name children =>
      PElement name _ ((fix nodesInd (nodes: list VDomNode) : Forall P nodes :=
        match nodes return Forall P nodes with
        | nil => Forall_nil _
        | node::nodes => Forall_cons node (VDomNode_fullInd node) (nodesInd nodes)
        end) children)
  end.

End VDomNodeFullInd.

(* *** *)

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
      match count with
      | 0 => stRet tt
      | S count => 
          do _ <- domOps.(removeChildAt) parent (count + from);
          removeNodes parent from count
      end
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
          do _ <- if newLen <? oldLen then removeNodes oldNode newLen (oldLen - newLen) else stRet tt;
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

(* *** *)

Fixpoint dom2vdom (maxDepth: nat) (root: DomNode) {struct maxDepth} : State Dom VDomNode :=
  do type <- domOps.(getNodeType) root;
  match type with
  | TextNode => 
      do text <- domOps.(getText) root;
      stRet (VText text)
  | ElementNode =>
      do tag <- domOps.(getTagName) root;
      do children <- match maxDepth with
        | 0 => stRet nil
        | S maxDepth => 
            let convChildren :=
              fix convChildren index count :=
                match count with
                | 0 => stRet nil
                | S count =>
                    do childNode <- domOps.(getChildNode) root index;
                    do vnode <- dom2vdom maxDepth childNode;
                    do vnodes <- convChildren (S index) count;
                    stRet (vnode::vnodes)
                end
              in
            do count <- domOps.(childrenCount) root;
            convChildren 0 count
        end;
      stRet (VElement tag children)
  end.

Theorem updateNode_correct: forall vdom dom parent index,
  index < stEval (domOps.(childrenCount) parent) dom ->
  stEval (
    do _ <- updateNode parent vdom index;
    do node <- domOps.(getChildNode) parent index;
    dom2vdom (vdomDepth vdom) node) dom 
  = vdom.
Proof.
  induction vdom using VDomNode_fullInd.
  - simpl. intros.
    rewrite stBind_assoc.
    rewrite stEval_stBind.
    destruct (stRun (childrenCount domOps parent) dom) as [chldCnt dom1].
    simpl.
    rewrite stEval_stBind. destruct (index <? chldCnt) eqn: Hlt.
    + admit.
    + rewrite stRun_stBind.
      destruct (stRun (createTextNode domOps text)) as [txtNode dom2] eqn: Heq.
      simpl.

Qed.

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
