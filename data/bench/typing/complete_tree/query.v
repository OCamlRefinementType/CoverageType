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
  Parameter bool_gen : unit -> Prop.
  Parameter int_gen : unit -> Z.
  Parameter sizecheck : Z -> Prop.
  Parameter subs : Z -> Z.

  Axiom tree_depth_0_is_leaf : forall (l : tree Z), forall (n : Z), (depth l n /\ n = 0) -> leaf l.
  Axiom tree_positive_depth_is_not_leaf : forall (l : tree Z), forall (n : Z), (depth l n /\ n > 0) -> ~leaf l.
  Axiom tree_no_leaf_exists_lch : forall (l : tree Z), exists (l1 : tree Z), ~leaf l -> lch l l1.
  Axiom tree_no_leaf_exists_rch : forall (l : tree Z), exists (l1 : tree Z), ~leaf l -> rch l l1.
  Axiom tree_no_leaf_exists_root : forall (l : tree Z), exists (x : Z), ~leaf l -> root l x.
  Axiom tree_complete_lch_complete : forall (l : tree Z) (l1 : tree Z), (lch l l1 /\ complete l) -> (complete l1).
  Axiom tree_complete_rch_complete : forall (l : tree Z) (l1 : tree Z), (rch l l1 /\ complete l) -> (complete l1).
  Axiom tree_complete_lch_depth_minus_1 : forall (l : tree Z) (l1 : tree Z) (n : Z), (lch l l1 /\ complete l /\ depth l n) -> (depth l1 (n - 1)).
  Axiom tree_complete_rch_depth_minus_1 : forall (l : tree Z) (l1 : tree Z) (n : Z), (rch l l1 /\ complete l /\ depth l n) -> (depth l1 (n - 1)).
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
  Parameter bool_gen : unit -> Prop.
  Parameter int_gen : unit -> Z.
  Parameter sizecheck : Z -> Prop.
  Parameter subs : Z -> Z.

  Lemma tree_depth_0_is_leaf : forall (l : tree Z), forall (n : Z), (depth l n /\ n = 0) -> leaf l. Admitted.
  Lemma tree_positive_depth_is_not_leaf : forall (l : tree Z), forall (n : Z), (depth l n /\ n > 0) -> ~leaf l. Admitted.
  Lemma tree_no_leaf_exists_lch : forall (l : tree Z), exists (l1 : tree Z), ~leaf l -> lch l l1. Admitted.
  Lemma tree_no_leaf_exists_rch : forall (l : tree Z), exists (l1 : tree Z), ~leaf l -> rch l l1. Admitted.
  Lemma tree_no_leaf_exists_root : forall (l : tree Z), exists (x : Z), ~leaf l -> root l x. Admitted.
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

  Lemma tree_depth_unique : forall (l : tree Z) (n1 n2 : Z), depth l n1 -> depth l n2 -> n1 = n2.
  Proof.
    induction l; intros n1 n2 Hd1 Hd2;
    simpl in *.
    - subst. reflexivity.
    - destruct Hd1 as [nl1 [nr1 H1]].
      destruct Hd2 as [nl2 [nr2 H2]].
      intuition.
      assert (nl1 = nl2) by (apply IHl1; intuition).
      assert (nr1 = nr2) by (apply IHl2; intuition).
      subst. reflexivity.
  Qed.
  Lemma tree_complete_lch_depth_minus_1 : forall (l : tree Z) (l1 : tree Z) (n : Z),
    (lch l l1 /\ complete l /\ depth l n) -> (depth l1 (n - 1)).
  Proof.
    intros [] l1 n [Hl [Hc Hd]].
    - contradiction.
    - simpl in Hc. simpl in Hd. simpl in Hl. subst.
      destruct Hc as [Hcl [Hcr [n1 [Hdln Hdrn]]]].
      destruct Hd as [nl [nr [Hdl [Hdr Hn]]]].
      remember (tree_depth_unique _ _ _ Hdl Hdln).
      remember (tree_depth_unique _ _ _ Hdr Hdrn).
      subst.
      replace (Z.max n1 n1 + 1 - 1) with n1 by lia.
      assumption.
  Qed.

  Lemma tree_complete_rch_depth_minus_1 : forall (l : tree Z) (l1 : tree Z) (n : Z),
    (rch l l1 /\ complete l /\ depth l n) -> (depth l1 (n - 1)).
  Proof.
    intros [] l1 n [Hr [Hc Hd]].
    - contradiction.
    - simpl in Hc. simpl in Hd. simpl in Hr. subst.
      destruct Hc as [Hcl [Hcr [n1 [Hdln Hdrn]]]].
      destruct Hd as [nl [nr [Hdl [Hdr Hn]]]].
      remember (tree_depth_unique _ _ _ Hdl Hdln).
      remember (tree_depth_unique _ _ _ Hdr Hdrn).
      subst.
      replace (Z.max n1 n1 + 1 - 1) with n1 by lia.
      assumption.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (s : Z), 0 <= s -> (forall (v : tree Z), (depth v s /\ complete v) -> ((~s = 0 <-> s > 0) /\ ((s = 0 /\ leaf v) \/ (~s = 0 /\ (exists (lt : tree Z), (s - 1) < s /\ 0 <= (s - 1) /\ depth lt (s - 1) /\ complete lt /\ (exists (rt : tree Z), (s - 1) < s /\ 0 <= (s - 1) /\ depth rt (s - 1) /\ complete rt /\ (exists (n : Z), root v n /\ lch v lt /\ rch v rt))))))).
  Proof.
    intros s Hs v [Hd Hc]. split; try lia.
    destruct (s =? 0) eqn:Hseq.
    - left. assert (s = 0) by lia.
      split; try assumption.
      apply (tree_depth_0_is_leaf _ s). intuition.
    - right. assert (s > 0) by lia.
      assert (~leaf v) by (apply (tree_positive_depth_is_not_leaf _ s); intuition).
      destruct (tree_no_leaf_exists_root v) as [x Hrt].
      destruct (tree_no_leaf_exists_lch v) as [l Hl].
      destruct (tree_no_leaf_exists_rch v) as [r Hr].
      intuition.
      exists l. intuition.
      * apply (tree_complete_lch_depth_minus_1 v l). intuition.
      * apply (tree_complete_lch_complete v l). intuition.
      * exists r. intuition.
        + apply (tree_complete_rch_depth_minus_1 v r). intuition.
        + apply (tree_complete_rch_complete v r). intuition.
        + exists x. intuition.
  Qed.
End Goal.
