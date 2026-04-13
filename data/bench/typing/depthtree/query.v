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
  Parameter bool_gen : unit -> Prop.
  Parameter int_gen : unit -> Z.
  Parameter sizecheck : Z -> Prop.
  Parameter subs : Z -> Z.

  Axiom tree_no_leaf_exists_lch : forall (l : tree Z), exists (l1 : tree Z), ~leaf l -> lch l l1.
  Axiom tree_no_leaf_exists_rch : forall (l : tree Z), exists (l1 : tree Z), ~leaf l -> rch l l1.
  Axiom tree_no_leaf_exists_root : forall (l : tree Z), exists (x : Z), ~leaf l -> root l x.
  Axiom tree_lch_depth_minus_1 : forall (l : tree Z), forall (l1 : tree Z), forall (n : Z), forall (n1 : Z), (lch l l1 /\ (depth l n /\ depth l1 n1)) -> n1 <= (n - 1).
  Axiom tree_rch_depth_minus_1 : forall (l : tree Z), forall (l1 : tree Z), forall (n : Z), forall (n1 : Z), (rch l l1 /\ (depth l n /\ depth l1 n1)) -> n1 <= (n - 1).
  Axiom tree_depth_geq_0 : forall (l : tree Z) (n : Z), (depth l n) -> (n >= 0).
  Axiom tree_depth_0_is_leaf : forall (l : tree Z) (n : Z), (depth l n /\ n = 0) -> (leaf l).
  Axiom tree_positive_depth_is_not_leaf : forall (l : tree Z), forall (n : Z), (depth l n /\ n > 0) -> ~leaf l.
  Axiom tree_depth_exists : forall (l : tree Z), exists (n : Z), depth l n.
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
  Parameter bool_gen : unit -> Prop.
  Parameter int_gen : unit -> Z.
  Parameter sizecheck : Z -> Prop.
  Parameter subs : Z -> Z.

  Lemma tree_no_leaf_exists_lch : forall (l : tree Z), exists (l1 : tree Z), ~leaf l -> lch l l1. Admitted.
  Lemma tree_no_leaf_exists_rch : forall (l : tree Z), exists (l1 : tree Z), ~leaf l -> rch l l1. Admitted.
  Lemma tree_no_leaf_exists_root : forall (l : tree Z), exists (x : Z), ~leaf l -> root l x. Admitted.
  Lemma tree_lch_depth_minus_1 : forall (l : tree Z), forall (l1 : tree Z), forall (n : Z), forall (n1 : Z), (lch l l1 /\ (depth l n /\ depth l1 n1)) -> n1 <= (n - 1). Admitted.
  Lemma tree_rch_depth_minus_1 : forall (l : tree Z), forall (l1 : tree Z), forall (n : Z), forall (n1 : Z), (rch l l1 /\ (depth l n /\ depth l1 n1)) -> n1 <= (n - 1). Admitted.
  Lemma tree_depth_geq_0 : forall (l : tree Z) (n : Z), (depth l n) -> (n >= 0).
  Proof.
    induction l; intros n Hd.
    - inversion Hd. lia.
    - simpl in Hd. destruct Hd as [nl [nr [Hd1 [Hd2 Hc]]]].
      apply IHl1 in Hd1.
      apply IHl2 in Hd2.
      intuition.
  Qed.

  Lemma tree_depth_0_is_leaf : forall (l : tree Z) (n : Z), (depth l n /\ n = 0) -> (leaf l).
  Proof.
    induction l; intros n [Hd Hn].
    - reflexivity.
    - subst. simpl in Hd.
      destruct Hd as [nl [nr [Hd1 [Hd2 Hc]]]].
      apply tree_depth_geq_0 in Hd1.
      apply tree_depth_geq_0 in Hd2.
      lia.
  Qed.

  Lemma tree_positive_depth_is_not_leaf : forall (l : tree Z), forall (n : Z), (depth l n /\ n > 0) -> ~leaf l.
  Proof.
    intros [] n [Hd Hn].
    - simpl in Hd. lia.
    - simpl. auto.
  Qed.

  Lemma tree_depth_exists : forall (l : tree Z), exists (n : Z), depth l n.
  Proof.
    induction l.
    - exists 0. reflexivity.
    - destruct IHl1 as [n1 Hd1].
      destruct IHl2 as [n2 Hd2].
      exists ((Z.max n1 n2) + 1). simpl.
      exists n1. exists n2. intuition.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (s : Z), 0 <= s -> (forall (v : tree Z), (exists (u : Z), depth v u /\ u <= s) -> ((~s = 0 <-> s > 0) /\ ((s = 0 /\ leaf v) \/ (~s = 0 /\ (leaf v \/ (exists (lt_1 : tree Z), (s - 1) < s /\ 0 <= (s - 1) /\ (exists (u_5 : Z), depth lt_1 u_5 /\ u_5 <= (s - 1)) /\ (exists (rt_1 : tree Z), (s - 1) < s /\ 0 <= (s - 1) /\ (exists (u_6 : Z), depth rt_1 u_6 /\ u_6 <= (s - 1)) /\ (exists (n_0 : Z), root v n_0 /\ lch v lt_1 /\ rch v rt_1)))))))).
  Proof.
    intros s Hs v [u [Hd Hu]]. intuition.
    set (Hu1 := (tree_depth_geq_0 _ _ Hd)).
    destruct (s =? 0) eqn:Heq.
    - left.
      assert (u = 0) by lia.
      remember (tree_depth_0_is_leaf v u).
      intuition.
    - right.
      assert (s > 0) by lia.
      split; try lia.
      destruct (u =? 0) eqn:Hequ.
      * left. assert (u = 0) by lia.
        apply (tree_depth_0_is_leaf v u).
        intuition.
      * right. assert (u > 0) by lia.
        destruct (tree_no_leaf_exists_root v) as [x Hrt].
        destruct (tree_no_leaf_exists_lch v) as [l Hl].
        destruct (tree_no_leaf_exists_rch v) as [r Hr].
        remember (tree_positive_depth_is_not_leaf v u).
        intuition.
        exists l. intuition.
        + destruct (tree_depth_exists l) as [nl Hn].
          exists nl. split; try assumption.
          assert (nl <= u - 1) by (apply (tree_lch_depth_minus_1 v l u nl); intuition).
          lia.
        + exists r. intuition.
          -- destruct (tree_depth_exists r) as [nr Hn].
              exists nr. split; try assumption.
              assert (nr <= u - 1) by (apply (tree_rch_depth_minus_1 v r u nr); intuition).
              lia.
          -- exists x. intuition.
  Qed.
End Goal.
