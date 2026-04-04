From Stdlib Require Import BinInt.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.
From Stdlib Require Import Floats.
Open Scope Z_scope.

Module Type Signatures.
Parameter tree : forall (a : Type), Type.

  Parameter depth : forall {a : Type}, tree a -> Z -> Prop.
  Parameter leaf : forall {a : Type}, tree a -> Prop.
  Parameter root : forall {a : Type}, tree a -> a -> Prop.
  Parameter lch : forall {a : Type}, tree a -> tree a -> Prop.
  Parameter rch : forall {a : Type}, tree a -> tree a -> Prop.
  Parameter complete : forall {a : Type}, tree a -> Prop.


  Axiom tree_complete_leaf : forall (l : tree Z), leaf l -> complete l.
End Signatures.

Module Axioms : Signatures.
  Inductive tree' (a : Type) : Type :=
  | Leaf : tree' a
  | Node : a -> tree' a -> tree' a -> tree' a.
  Definition tree := tree'.

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
  Fixpoint complete {a : Type} (t : tree a) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ _ l r => complete l /\ complete r /\ (exists n, depth l n /\ depth r n)
    end.


  Lemma tree_complete_leaf : forall (l : tree Z), leaf l -> complete l.
  Proof.
    intros [] Hl.
    - reflexivity.
    - contradiction.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (v : tree Z), leaf v -> (leaf v /\ complete v).
  Proof.
    intros v Hl.
    split; try assumption.
    apply tree_complete_leaf.
    assumption.
  Qed.
End Goal.
