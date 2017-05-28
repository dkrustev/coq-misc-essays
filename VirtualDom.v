(* author: Dimitur Krustev *)
(* started: 20170526 *)

(* partially inspired by: https://medium.com/@deathmood/how-to-write-your-own-virtual-dom-ee74acc13060 *)

Require Import List Arith.
Require String.
Require Fin.

Fixpoint replaceNth {A} (n: nat) (xs: list A) (y: A) {struct xs} : list A :=
  match xs with
  | nil => nil
  | x::xs => match n with
    | 0 => y::xs
    | S n => x :: replaceNth n xs y
    end
  end.

Lemma length_replaceNth: forall A (xs: list A) n y, length (replaceNth n xs y) = length xs.
Proof.
  induction xs; auto.
  simpl. intros. destruct n; auto. 
  simpl. f_equal. auto.
Qed.

Lemma nth_replaceNth_sameInd: forall A (xs: list A) n y default,
  nth n (replaceNth n xs y) default =  if n <? length xs then y else default.
Proof.
  induction xs.
  - simpl. intros. destruct n; auto.
  - simpl. intros. destruct n; auto.
    simpl. rewrite IHxs. unfold Nat.ltb. reflexivity.
Qed.

Lemma nth_replaceNth_diffInd: forall A (xs: list A) n m y default,
  n <> m -> nth n (replaceNth m xs y) default = nth n xs default.
Proof.
  induction xs; auto.
  simpl. destruct m.
  - simpl. intros. destruct n; try congruence.
  - simpl. intros. destruct n; auto.
Qed.

Lemma replaceNth_app_l: forall A (xs ys: list A) n y,
  n < length xs -> replaceNth n (xs ++ ys) y = replaceNth n xs y ++ ys.
Proof.
  induction xs.
  - simpl. intros. contradict H. auto with arith.
  - simpl. intros. destruct n; auto.
    rewrite IHxs; auto with arith.
Qed.

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

Inductive DomNodeType := TextNode | ElementNode.

Record DomOps (Dom: Type) (DomNode: Type) := MkDomOps {
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

Implicit Arguments getNodeType [Dom DomNode].
Implicit Arguments childrenCount [Dom DomNode].
Implicit Arguments getChildNode [Dom DomNode].
Implicit Arguments createTextNode [Dom DomNode].
Implicit Arguments createElement [Dom DomNode].
Implicit Arguments appendChild [Dom DomNode].
Implicit Arguments removeChildAt [Dom DomNode].
Implicit Arguments replaceChildAt [Dom DomNode].
Implicit Arguments getTagName [Dom DomNode].
Implicit Arguments getText [Dom DomNode].
Implicit Arguments setText [Dom DomNode].

Definition DomNode := nat.

Inductive DomNodeCell: Set  := 
  | DomText (t: String.string) 
  | DomElement (name: String.string) (children: list DomNode).

Definition Dom := list DomNodeCell.

Definition getNodeCell dom node := nth node dom (DomText String.EmptyString).

Definition domOps: DomOps Dom DomNode := {|
  getNodeType node := 
    do dom <- stGet;
    match getNodeCell dom node with
    | DomText _ => stRet TextNode
    | DomElement _ _ => stRet ElementNode
    end;
  childrenCount node :=
    do dom <- stGet;
    match getNodeCell dom node with
    | DomText _ => stRet 0
    | DomElement _ children => stRet (length children)
    end;
  getChildNode node index :=
    do dom <- stGet;
    match getNodeCell dom node with
    | DomText _ => stRet 0
    | DomElement _ children => stRet (nth index children 0)
    end;
  createTextNode text :=
    do dom <- stGet;
    let len := length dom in
    do _ <- stPut (dom ++ (DomText text :: nil));
    stRet len;
  createElement tag :=
    do dom <- stGet;
    let len := length dom in
    do _ <- stPut (dom ++ (DomElement tag nil :: nil));
    stRet len;
  appendChild parent child :=
    do dom <- stGet;
    match getNodeCell dom parent with
    | DomText _ => stRet tt
    | DomElement tag children => 
        stPut (replaceNth parent dom (DomElement tag (children ++ child::nil)))
    end;
  removeChildAt node index :=
    do dom <- stGet;
    match getNodeCell dom node with
    | DomText _ => stRet tt
    | DomElement tag children => 
        stPut (replaceNth node dom (DomElement tag 
          (firstn index children ++ skipn (S index) children)))
    end;
  replaceChildAt node index newChild :=
    do dom <- stGet;
    match getNodeCell dom node with
    | DomText _ => stRet tt
    | DomElement tag children => 
        stPut (replaceNth node dom (DomElement tag (replaceNth index children newChild)))
    end;
  getTagName node :=
    do dom <- stGet;
    match getNodeCell dom node with
    | DomText _ => stRet String.EmptyString
    | DomElement tag _ => stRet tag
    end;
  getText node :=
    do dom <- stGet;
    match getNodeCell dom node with
    | DomText text => stRet text
    | DomElement _ _ => stRet String.EmptyString
    end;
  setText node newText :=
    do dom <- stGet;
    match getNodeCell dom node with
    | DomText _ => 
        stPut (replaceNth node dom (DomText newText))
    | DomElement tag children => stRet tt
    end;
  |}.

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
          do len <- domOps.(childrenCount) parent;
          do _ <- 
            if index <? len then
              updateNode parent newNode index
            else
              do node <- createNode newNode;
              domOps.(appendChild) parent node;
          updateNodes parent newNodes (S index)
      end
    in
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
  end.

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

Definition ValidDomNode (dom: Dom) (node: DomNode) : Prop := node < length dom.

Theorem updateNode_correct: forall vdom dom parent index,
  ValidDomNode dom parent ->
  stEval (domOps.(getNodeType) parent) dom = ElementNode ->
  index < stEval (domOps.(childrenCount) parent) dom ->
  stEval (
    do _ <- updateNode parent vdom index;
    do node <- domOps.(getChildNode) parent index;
    dom2vdom (vdomDepth vdom) node) dom 
  = vdom.
Proof.
  induction vdom using VDomNode_fullInd.
  - simpl. intros. unfold stEval, stRun in *.
    destruct (getNodeCell dom parent) as [oldText | parentTag nodes] eqn: Heq; 
      try (simpl in *; congruence).
    unfold stRet in *. simpl in *.
    destruct (getNodeCell dom (nth index nodes 0)) as [oldText | tag children] eqn: Heq1.
    + rewrite Heq1. destruct (String.string_dec text oldText) as [Heq2 | Hneq].
      * subst. rewrite Heq. repeat (rewrite Heq1). reflexivity.
      * rewrite Heq1. unfold stPut. unfold getNodeCell at 1.
        rewrite nth_replaceNth_diffInd.
        2: admit.
        fold (getNodeCell dom parent).
        rewrite Heq. unfold getNodeCell at 1.
        rewrite nth_replaceNth_sameInd.
        destruct (nth index nodes 0 <? length dom) eqn: Hltb.
        2: admit.
        unfold getNodeCell at 1.
        rewrite nth_replaceNth_sameInd.
        rewrite Hltb. reflexivity.
    + unfold getNodeCell at 1. rewrite app_nth1; auto.
      fold (getNodeCell dom parent).
      rewrite Heq. unfold stPut. 
      unfold getNodeCell at 1.
      rewrite nth_replaceNth_sameInd.
      rewrite app_length. simpl. rewrite plus_comm. simpl.
      destruct (parent <? S (length dom)) eqn: Hltb.
      2: admit.
      rewrite nth_replaceNth_sameInd.
      destruct (index <? length nodes) eqn: Hltb1.
      2: admit.
      unfold getNodeCell at 1.
      rewrite replaceNth_app_l; auto.
      rewrite app_nth2.
      2: rewrite length_replaceNth; auto with arith.
      rewrite length_replaceNth. rewrite <- minus_diag_reverse. simpl.
      unfold getNodeCell at 1.
      rewrite app_nth2.
      2: rewrite length_replaceNth; auto with arith.
      rewrite length_replaceNth. rewrite <- minus_diag_reverse. reflexivity.
  - simpl. intros. unfold stEval, stRun in *.
    destruct (getNodeCell dom parent) as [oldText | parentTag nodes] eqn: Heq; 
      try (simpl in *; congruence).
    unfold stRet in *. simpl in *.
    destruct (getNodeCell dom (nth index nodes 0)) as [text | tag oldChildren] eqn: Heq1.
    + unfold stBind at 1. 

Qed.


End VDom.
