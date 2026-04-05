From Stdlib Require Import BinInt.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.
From Stdlib Require Import Floats.
From Stdlib Require Import Lia.
Open Scope Z_scope.

Module Type Signatures.
Parameter tree : forall (a : Type), Type.

  Parameter depth : forall {a : Type}, tree a -> Z -> Prop.
  Parameter leaf : forall {a : Type}, tree a -> Prop.
  Parameter root : forall {a : Type}, tree a -> a -> Prop.
  Parameter lch : forall {a : Type}, tree a -> tree a -> Prop.
  Parameter rch : forall {a : Type}, tree a -> tree a -> Prop.
  Parameter complete : forall {a : Type}, tree a -> Prop.


  Axiom tree_root_no_leaf : forall (l : tree Z) (x : Z), (root l x) -> ~(leaf l).
  Axiom tree_depth_node_lch : forall (l : tree Z) (l1 : tree Z) (l2 : tree Z) (n1 : Z) (n2 : Z), (depth l1 n1 /\ depth l2 n2 /\ lch l l1 /\ rch l l2 /\ n1 >= n2) -> (depth l (n1 + 1)).
  Axiom tree_complete_node : forall (l : tree Z) (l1 : tree Z) (l2 : tree Z) (n : Z), (complete l1 /\ complete l2 /\ depth l1 n /\ depth l2 n /\ lch l l1 /\ rch l l2) -> (complete l).
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


  Lemma tree_root_no_leaf : forall (l : tree Z) (x : Z), (root l x) -> ~(leaf l).
  Proof.
    intros [] x Hr.
    - contradiction.
    - intros [].
  Qed.

  Lemma tree_depth_node_lch : forall (l : tree Z) (l1 : tree Z) (l2 : tree Z)
    (n1 : Z) (n2 : Z), (depth l1 n1 /\ depth l2 n2 /\ lch l l1 /\ rch l l2 /\ n1 >= n2)
    -> (depth l (n1 + 1)).
  Proof.
    intros [] l1 l2 n1 n2 H;
    decompose [and] H;
    try contradiction.
    simpl. exists n1. exists n2.
    inversion H1. inversion H3. subst.
    intuition.
  Qed.

  Lemma tree_complete_node : forall (l : tree Z) (l1 : tree Z) (l2 : tree Z) (n : Z),
    (complete l1 /\ complete l2 /\ depth l1 n /\ depth l2 n /\ lch l l1 /\ rch l l2)
    -> (complete l).
  Proof.
    intros [] l1 l2 n H;
    decompose [and] H;
    try contradiction.
    simpl. inversion H4. inversion H6. subst.
    intuition. exists n. intuition.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (s : Z), 0 <= s -> (forall (v : tree Z), (exists (_2 : Z), exists (s_4 : Z), exists (_48 : tree Z), exists (_46 : tree Z), s > 0 /\ 0 <= s_4 /\ s_4 >= 0 /\ s_4 < s /\ s_4 = (s - 1) /\ depth _46 s_4 /\ complete _46 /\ depth _48 s_4 /\ complete _48 /\ root v _2 /\ lch v _46 /\ rch v _48) -> (~leaf v /\ depth v s /\ complete v)).
  Proof.
    intros s Hs v.
    intuition;
    destruct H as [x [s' [r [l H1]]]];
    decompose [and] H1; subst.
    - apply tree_root_no_leaf in H10. contradiction.
    - replace s with (s - 1 + 1) by intuition.
      eapply tree_depth_node_lch.
      intuition. apply H5. apply H7.
      assumption. assumption. intuition.
    - eapply tree_complete_node.
      intuition. apply H6. apply H8. apply H5.
      assumption. assumption. assumption.
  Qed.
End Goal.
