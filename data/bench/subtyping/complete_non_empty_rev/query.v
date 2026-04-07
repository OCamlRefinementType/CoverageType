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
  Parameter complete : forall {a : Type}, tree a -> Prop.

  Axiom tree_complete_lch_depth_minus_1 : forall (l : tree Z), forall (l1 : tree Z), forall (n : Z), (lch l l1 /\ (complete l /\ depth l n)) -> depth l1 (n - 1).
  Axiom tree_complete_rch_depth_minus_1 : forall (l : tree Z), forall (l1 : tree Z), forall (n : Z), (rch l l1 /\ (complete l /\ depth l n)) -> depth l1 (n - 1).
  Axiom tree_no_leaf_exists_lch : forall (l : tree Z), exists (l1 : tree Z), ~(leaf l) -> (lch l l1).
  Axiom tree_no_leaf_exists_rch : forall (l : tree Z), exists (l1 : tree Z), ~(leaf l) -> (rch l l1).
  Axiom tree_no_leaf_exists_root : forall (l : tree Z), exists (x : Z), ~(leaf l) -> (root l x).
  Axiom tree_complete_lch_complete : forall (l : tree Z) (l1 : tree Z), (lch l l1 /\ complete l) -> (complete l1).
  Axiom tree_complete_rch_complete : forall (l : tree Z) (l1 : tree Z), (rch l l1 /\ complete l) -> (complete l1).
  Axiom tree_no_leaf_depth_pos : forall (l : tree Z) (s : Z), ~(leaf l) /\ (depth l s) -> s > 0.
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
  Fixpoint complete {a : Type} (t : tree a) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ _ l r => complete l /\ complete r /\ (exists n, depth l n /\ depth r n)
    end.

  Lemma tree_complete_lch_depth_minus_1 : forall (l : tree Z), forall (l1 : tree Z), forall (n : Z), (lch l l1 /\ (complete l /\ depth l n)) -> depth l1 (n - 1). Admitted.
  Lemma tree_complete_rch_depth_minus_1 : forall (l : tree Z), forall (l1 : tree Z), forall (n : Z), (rch l l1 /\ (complete l /\ depth l n)) -> depth l1 (n - 1). Admitted.
  Lemma tree_no_leaf_exists_lch : forall (l : tree Z), exists (l1 : tree Z), ~(leaf l) -> (lch l l1).
  Proof.
    intros [].
    - exists (Leaf Z). intros []. reflexivity.
    - exists t. intros Hl. reflexivity.
  Qed.

  Lemma tree_no_leaf_exists_rch : forall (l : tree Z), exists (l1 : tree Z), ~(leaf l) -> (rch l l1).
  Proof.
    intros [].
    - exists (Leaf Z). intros []. reflexivity.
    - exists t0. intros Hl. reflexivity.
  Qed.

  Lemma tree_no_leaf_exists_root : forall (l : tree Z), exists (x : Z), ~(leaf l) -> (root l x).
  Proof.
    intros [].
    - exists 0. intros []. reflexivity.
    - exists z. intros. reflexivity.
  Qed.

  Lemma tree_complete_lch_complete : forall (l : tree Z) (l1 : tree Z), (lch l l1 /\ complete l) -> (complete l1).
  Proof.
    intros [] l1 [Hlch Hc].
    - contradiction.
    - inversion Hlch. subst.
      simpl in Hc.
      destruct Hc as [Hc' H].
      assumption.
  Qed.

  Lemma tree_complete_rch_complete : forall (l : tree Z) (l1 : tree Z), (rch l l1 /\ complete l) -> (complete l1).
  Proof.
    intros [] l1 [Hrch Hc].
    - contradiction.
    - inversion Hrch. subst.
      simpl in Hc.
      destruct Hc as [Hc' [Hc'' H]].
      assumption.
  Qed.

  Lemma tree_depth_geq_0 : forall (l : tree Z) (s : Z), (depth l s) -> s >= 0.
  Proof.
    induction l; intros s Hd; simpl in Hd.
    - intuition.
    - destruct Hd as [nl [nr [Hld [Hrd Hs]]]].
      apply IHl1 in Hld.
      apply IHl2 in Hrd.
      intuition.
  Qed.
  
  Lemma tree_no_leaf_depth_pos : forall (l : tree Z) (s : Z), ~(leaf l) /\ (depth l s) -> s > 0.
  Proof.
    intros [] s [Hl Hd].
    - simpl in Hl. contradiction.
    - simpl in Hd. destruct Hd as [nl [nr [Hld [Hrd Hs]]]].
      apply tree_depth_geq_0 in Hld.
      apply tree_depth_geq_0 in Hrd.
      intuition.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (s : Z), 0 <= s -> (forall (v : tree Z), (~leaf v /\ depth v s /\ complete v) -> (exists (_2 : Z), exists (s_4 : Z), exists (_48 : tree Z), exists (_46 : tree Z), s > 0 /\ 0 <= s_4 /\ s_4 >= 0 /\ s_4 < s /\ s_4 = (s - 1) /\ depth _46 s_4 /\ complete _46 /\ depth _48 s_4 /\ complete _48 /\ root v _2 /\ lch v _46 /\ rch v _48)).
  Proof.
    intros s Hs v [Hl [Hd Hc]].
    destruct (tree_no_leaf_exists_root v) as [x Hr].
    destruct (tree_no_leaf_exists_lch v) as [l Hlch].
    destruct (tree_no_leaf_exists_rch v) as [r Hrch].
    exists x. exists (s - 1). exists r. exists l.
    intuition.
    - apply (tree_no_leaf_depth_pos v). intuition.
    - assert (s > 0) by (apply (tree_no_leaf_depth_pos v s); intuition). intuition.
    - assert (s > 0) by (apply (tree_no_leaf_depth_pos v s); intuition). intuition.
    - apply (tree_complete_lch_depth_minus_1 v). intuition.
    - apply (tree_complete_lch_complete v). intuition.
    - apply (tree_complete_rch_depth_minus_1 v). intuition.
    - apply (tree_complete_rch_complete v). intuition.
  Qed.
End Goal.
