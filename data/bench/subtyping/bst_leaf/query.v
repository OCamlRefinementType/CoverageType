From Stdlib Require Import BinInt.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.
From Stdlib Require Import Floats.
From Stdlib Require Import Lia.
Open Scope Z_scope.

Module Type Signatures.
  Parameter tree : forall (a : Type), Type.
  Parameter rbtree : forall (a : Type), Type.

  Parameter depth : forall {a : Type}, tree a -> Z -> Prop.
  Parameter leaf : forall {a : Type}, tree a -> Prop.
  Parameter root : forall {a : Type}, tree a -> a -> Prop.
  Parameter lch : forall {a : Type}, tree a -> tree a -> Prop.
  Parameter rch : forall {a : Type}, tree a -> tree a -> Prop.
  Parameter lower_bound : tree Z -> Z -> Prop.
  Parameter upper_bound : tree Z -> Z -> Prop.
  Parameter bst : tree Z -> Prop.


  Axiom tree_leaf_bst : forall (l : tree Z), (leaf l) -> (bst l).
End Signatures.

Module Axioms : Signatures.
  Inductive tree' (a : Type) : Type :=
  | Leaf : tree' a
  | Node : a -> tree' a -> tree' a -> tree' a.
  Definition tree := tree'.
  Inductive rbtree' (a : Type) : Type :=
  | Rbtleaf : rbtree' a
  | Rbtnode : bool -> rbtree' a -> a -> rbtree' a -> rbtree' a.
  Definition rbtree := rbtree'.

  Fixpoint depth {a : Type} (t : tree a) (n : Z) : Prop :=
    match t with
    | Leaf _ => n = 0
    | Node _ _ l r => exists nl nr : Z, 
      depth l nl /\ depth r nr /\ n = Z.max nl nr + 1
    end.
  Definition leaf {a : Type} (t : tree a) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ _ _ _ => False
    end.
  Definition root {a : Type} (t : tree a) (x : a) : Prop :=
    match t with
    | Leaf _ => False
    | Node _ x' _ _ => x = x'
    end.
  Definition lch {a : Type} (t : tree a) (l : tree a) : Prop :=
    match t with
    | Leaf _ => False
    | Node _ _ l1 _ => l1 = l
    end.
  Definition rch {a : Type} (t : tree a) (r : tree a) : Prop :=
    match t with
    | Leaf _ => False
    | Node _ _ _ r1 => r1 = r
    end.
  Fixpoint lower_bound (t : tree Z) (x : Z) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ y l r => x <= y /\ lower_bound l x /\ lower_bound r x
    end.
  Fixpoint upper_bound (t : tree Z) (x : Z) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ y l r => y <= x /\ upper_bound l x /\ upper_bound r x
    end.
  Fixpoint bst (t : tree Z) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ x l r => bst l /\ bst r /\ upper_bound l x /\ lower_bound r x
    end.


  Lemma tree_leaf_bst : forall (l : tree Z), (leaf l) -> (bst l).
  Proof.
    intros [] Hl.
    - reflexivity.
    - contradiction.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (d : Z), 0 <= d -> (forall (lo : Z), forall (hi : Z), lo < hi -> (forall (v : tree Z), (leaf v /\ d = 0 /\ depth v 0) -> (leaf v /\ d = 0 /\ (~leaf v -> lower_bound v lo) /\ (~leaf v -> upper_bound v hi) /\ bst v /\ (exists (n : Z), depth v n /\ n <= d /\ n >= 0)))).
  Proof.
    intros d Hd lo hi Hlh v [Hl [Hd1 Hdep]].
    intuition.
    - apply tree_leaf_bst. assumption.
    - exists 0. intuition.
  Qed.
End Goal.
