From Stdlib Require Import BinInt.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.
From Stdlib Require Import Floats.
From Stdlib Require Import Lia.
Open Scope Z_scope.

Module Type Signatures.
  Parameter tree : forall (a : Type), Type.
  Parameter rbtree : forall (a : Type), Type.

  Parameter num_black : forall {a : Type}, rbtree a -> Z -> Prop.
  Parameter rb_leaf : forall {a : Type}, rbtree a -> Prop.
  Parameter rb_root : forall {a : Type}, rbtree a -> a -> Prop.
  Parameter rb_root_color : forall {a : Type}, rbtree a -> bool -> Prop.
  Parameter rb_lch : forall {a : Type}, rbtree a -> rbtree a -> Prop.
  Parameter rb_rch : forall {a : Type}, rbtree a -> rbtree a -> Prop.
  Parameter no_red_red : forall {a : Type}, rbtree a -> Prop.

  Axiom rbtree_no_rb_leaf_exists_ch : forall (l : rbtree Z), exists (l1 : rbtree Z), exists (l2 : rbtree Z), ~rb_leaf l -> (rb_lch l l1 /\ rb_rch l l2).
  Axiom rbtree_no_rb_leaf_exists_rb_root_color : forall (l : rbtree Z), exists (x : bool), ~rb_leaf l -> rb_root_color l x.
  Axiom black_lt_black_num_black_gt_1 : forall (v : rbtree Z), forall (lt : rbtree Z), forall (h : Z), (num_black v h /\ (rb_lch v lt /\ (rb_root_color v false /\ rb_root_color lt false))) -> h > 1.
  Axiom black_rt_black_num_black_gt_1 : forall (v : rbtree Z), forall (rt : rbtree Z), forall (h : Z), (num_black v h /\ (rb_rch v rt /\ (rb_root_color v false /\ rb_root_color rt false))) -> h > 1.
  Axiom rbtree_positive_num_black_is_not_rb_leaf : forall (l : rbtree Z) (n : Z), (num_black l n /\ n > 0) -> ~(rb_leaf l).
  Axiom rbtree_no_rb_leaf_exists_rb_root : forall (l : rbtree Z), exists (x : Z), ~(rb_leaf l) -> (rb_root l x).
  Axiom no_red_red_lt : forall (v : rbtree Z) (lt : rbtree Z), (no_red_red v /\ rb_lch v lt) -> (no_red_red lt).
  Axiom no_red_red_rt : forall (v : rbtree Z) (rt : rbtree Z), (no_red_red v /\ rb_rch v rt) -> (no_red_red rt).
  Axiom num_black_root_black_lt_minus_1 : forall (v : rbtree Z) (lt : rbtree Z) (h : Z), (rb_root_color v false /\ num_black v h /\ rb_lch v lt) -> (num_black lt (h - 1)).
  Axiom num_black_root_black_rt_minus_1 : forall (v : rbtree Z) (rt : rbtree Z) (h : Z), (rb_root_color v false /\ num_black v h /\ rb_rch v rt) -> (num_black rt (h - 1)).
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

  Fixpoint num_black {a : Type} (t : rbtree a) (h : Z) : Prop :=
    match t with
    | Rbtleaf _ => h = 0
    | Rbtnode _ c l _ r =>
      if c then num_black l h /\ num_black r h
      else num_black l (h - 1) /\ num_black r (h - 1)
    end.
  Definition rb_leaf {a : Type} (t : rbtree a) : Prop :=
    match t with
    | Rbtleaf _ => True
    | Rbtnode _ _ _ _ _ => False
    end.
  Definition rb_root {a : Type} (t : rbtree a) (x : a) : Prop :=
    match t with
    | Rbtleaf _ => False
    | Rbtnode _ _ _ y _ => x = y
    end.
  Definition rb_root_color {a : Type} (t : rbtree a) (c : bool) : Prop :=
    match t with
    | Rbtleaf _ => False
    | Rbtnode _ c1 _ _ _ => c = c1
    end.
  Definition rb_lch {a : Type} (t : rbtree a) (l : rbtree a) : Prop :=
    match t with
    | Rbtleaf _ => False
    | Rbtnode _ _ l1 _ _ => l = l1
    end.
  Definition rb_rch {a : Type} (t : rbtree a) (r : rbtree a) : Prop :=
    match t with
    | Rbtleaf _ => False
    | Rbtnode _ _ _ _ r1 => r = r1
    end.
  Fixpoint no_red_red {a : Type} (t : rbtree a) : Prop :=
    match t with
    | Rbtleaf _ => True
    | Rbtnode _ c l _ r =>
      if negb c then no_red_red l /\ no_red_red r
      else
        match (l, r) with
        | (Rbtnode _ c' _ _ _, Rbtnode _ c'' _ _ _) =>
          (c' = false) /\ (c'' = false) /\ no_red_red l /\ no_red_red r
        | (Rbtnode _ c' _ _ _, Rbtleaf _) => (c' = false) /\ no_red_red l
        | (Rbtleaf _, Rbtnode _ c'' _ _ _) => (c'' = false) /\ no_red_red r
        | (Rbtleaf _, Rbtleaf _) => True
        end
    end.

  Lemma rbtree_no_rb_leaf_exists_ch : forall (l : rbtree Z), exists (l1 : rbtree Z), exists (l2 : rbtree Z), ~rb_leaf l -> (rb_lch l l1 /\ rb_rch l l2). Admitted.
  Lemma rbtree_no_rb_leaf_exists_rb_root_color : forall (l : rbtree Z), exists (x : bool), ~rb_leaf l -> rb_root_color l x. Admitted.
  Lemma black_lt_black_num_black_gt_1 : forall (v : rbtree Z), forall (lt : rbtree Z), forall (h : Z), (num_black v h /\ (rb_lch v lt /\ (rb_root_color v false /\ rb_root_color lt false))) -> h > 1. Admitted.
  Lemma black_rt_black_num_black_gt_1 : forall (v : rbtree Z), forall (rt : rbtree Z), forall (h : Z), (num_black v h /\ (rb_rch v rt /\ (rb_root_color v false /\ rb_root_color rt false))) -> h > 1. Admitted.
  Lemma rbtree_positive_num_black_is_not_rb_leaf : forall (l : rbtree Z) (n : Z), (num_black l n /\ n > 0) -> ~(rb_leaf l).
  Proof.
    intros [] n [Hnb Hn].
    - simpl in Hnb. lia.
    - auto.
  Qed.

  Lemma rbtree_no_rb_leaf_exists_rb_root : forall (l : rbtree Z), exists (x : Z), ~(rb_leaf l) -> (rb_root l x).
  Proof.
    intros [].
    - exists 0. intros []. reflexivity.
    - exists z. intros Hl. reflexivity.
  Qed.

  Lemma no_red_red_lt : forall (v : rbtree Z) (lt : rbtree Z), (no_red_red v /\ rb_lch v lt) -> (no_red_red lt).
  Proof.
    intros [] [] [Hr Hl]; try contradiction.
    - reflexivity.
    - destruct b; simpl in Hr; simpl in Hl; subst.
      * destruct r0; decompose [and] Hr; assumption.
      * destruct Hr. assumption.
  Qed.

  Lemma no_red_red_rt : forall (v : rbtree Z) (rt : rbtree Z), (no_red_red v /\ rb_rch v rt) -> (no_red_red rt).
  Proof.
    intros [] [] [Hr Hrch]; try contradiction.
    - reflexivity.
    - destruct b; simpl in Hr; simpl in Hrch; subst.
      * destruct r; decompose [and] Hr; assumption.
      * destruct Hr. assumption.
  Qed.

  Lemma num_black_root_black_lt_minus_1 : forall (v : rbtree Z) (lt : rbtree Z) (h : Z),
    (rb_root_color v false /\ num_black v h /\ rb_lch v lt) -> (num_black lt (h - 1)).
  Proof.
    intros [] lt h [Hrc [Hnb Hl]]; try contradiction.
    simpl in Hnb. simpl in Hrc. simpl in Hl.
    subst. destruct Hnb. assumption.
  Qed.

  Lemma num_black_root_black_rt_minus_1 : forall (v : rbtree Z) (rt : rbtree Z) (h : Z),
    (rb_root_color v false /\ num_black v h /\ rb_rch v rt) -> (num_black rt (h - 1)).
  Proof.
    intros [] rt h [Hrc [Hnb Hr]]; try contradiction.
    simpl in Hnb. simpl in Hrc. simpl in Hr.
    subst. destruct Hnb. assumption.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (inv : Z), inv >= 0 -> ((forall (h : Z), (h >= 0 /\ (True -> (h + h) = inv) /\ (False -> ((h + h) + 1) = inv)) -> (forall (v : rbtree Z), (h > 0 /\ num_black v h /\ no_red_red v /\ (True -> ~rb_root_color v true) /\ (False -> (h = 0 -> ~rb_root_color v false))) -> (h > 0 /\ (exists (x_13 : Z), (inv - 1) >= 0 /\ (h - 1) >= 0 /\ (((h - 1) + (h - 1)) + 1) = (inv - 1) /\ (exists (lt2 : rbtree Z), no_red_red lt2 /\ num_black lt2 (h - 1) /\ ((h - 1) = 0 -> ~rb_root_color lt2 false) /\ (inv - 1) < inv /\ (h - 1) >= 0 /\ (((h - 1) + (h - 1)) + 1) = (inv - 1) /\ (exists (rt2 : rbtree Z), no_red_red rt2 /\ num_black rt2 (h - 1) /\ ((h - 1) = 0 -> ~rb_root_color rt2 false) /\ rb_root_color v false /\ rb_root v x_13 /\ rb_lch v lt2 /\ rb_rch v rt2)))))) /\ (forall (h_0 : Z), (h_0 >= 0 /\ (False -> (h_0 + h_0) = inv) /\ (True -> ((h_0 + h_0) + 1) = inv)) -> (forall (v_0 : rbtree Z), True))).
  Proof.
    intros inv Hinv. intuition.
    assert (~rb_leaf v) by (apply (rbtree_positive_num_black_is_not_rb_leaf _ h); intuition).
    destruct (rbtree_no_rb_leaf_exists_ch v) as [l [r Hch]].
    destruct (rbtree_no_rb_leaf_exists_rb_root v) as [x Hrt].
    destruct (rbtree_no_rb_leaf_exists_rb_root_color v) as [b Hb].
    exists x. intuition.
    destruct b; try contradiction.
    assert (num_black l (h - 1)) by (apply (num_black_root_black_lt_minus_1 v l h); intuition).
    assert (num_black r (h - 1)) by (apply (num_black_root_black_rt_minus_1 v r h); intuition).
    exists l. intuition.
    - apply (no_red_red_lt v l). intuition.
    - assert (h = 1) by lia.
      assert (h > 1) by (apply (black_lt_black_num_black_gt_1 v l); intuition).
      lia.
    - exists r. intuition.
      * apply (no_red_red_rt v r). intuition.
      * assert (h = 1) by lia.
        assert (h > 1) by (apply (black_rt_black_num_black_gt_1 v r); intuition).
        lia.
  Qed.
End Goal.
