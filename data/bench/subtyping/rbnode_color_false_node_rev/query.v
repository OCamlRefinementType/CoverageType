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

  Axiom rbtree_positive_num_black_is_not_rb_leaf : forall (l : rbtree Z), forall (n : Z), (num_black l n /\ n > 0) -> ~rb_leaf l.
  Axiom rbtree_no_rb_leaf_exists_rb_root_color : forall (l : rbtree Z), exists (x : bool), ~rb_leaf l -> rb_root_color l x.
  Axiom rbtree_no_rb_leaf_exists_ch : forall (l : rbtree Z), exists (l1 : rbtree Z), exists (l2 : rbtree Z), ~rb_leaf l -> (rb_lch l l1 /\ rb_rch l l2).
  Axiom rbtree_no_rb_leaf_exists_rb_root : forall (l : rbtree Z), exists (x : Z), ~rb_leaf l -> rb_root l x.
  Axiom num_black_root_black_lt_minus_1 : forall (v : rbtree Z), forall (lt : rbtree Z), forall (h : Z), (rb_root_color v false /\ (num_black v h /\ rb_lch v lt)) -> num_black lt (h - 1).
  Axiom num_black_root_black_rt_minus_1 : forall (v : rbtree Z), forall (rt : rbtree Z), forall (h : Z), (rb_root_color v false /\ (num_black v h /\ rb_rch v rt)) -> num_black rt (h - 1).
  Axiom no_red_red_lt : forall (v : rbtree Z), forall (lt : rbtree Z), (no_red_red v /\ rb_lch v lt) -> no_red_red lt.
  Axiom no_red_red_rt : forall (v : rbtree Z), forall (rt : rbtree Z), (no_red_red v /\ rb_rch v rt) -> no_red_red rt.
  Axiom root_color_single : forall (v : rbtree Z), ~(rb_root_color v false /\ rb_root_color v true).
  Axiom black_lt_black_num_black_gt_1 : forall (v : rbtree Z), forall (lt : rbtree Z), forall (h : Z), (num_black v h /\ (rb_lch v lt /\ (rb_root_color v false /\ rb_root_color lt false))) -> h > 1.
  Axiom black_rt_black_num_black_gt_1 : forall (v : rbtree Z), forall (rt : rbtree Z), forall (h : Z), (num_black v h /\ (rb_rch v rt /\ (rb_root_color v false /\ rb_root_color rt false))) -> h > 1.
  Axiom num_black_root_red_lt_same : forall (v : rbtree Z) (lt : rbtree Z) (h : Z), (rb_root_color v true /\ num_black v h /\ rb_lch v lt) -> (num_black lt h).
  Axiom num_black_root_red_rt_same : forall (v : rbtree Z) (rt : rbtree Z) (h : Z), (rb_root_color v true /\ num_black v h /\ rb_rch v rt) -> (num_black rt h).
  Axiom no_red_red_root_red_lt_not_red : forall (v : rbtree Z) (lt : rbtree Z), (no_red_red v /\ rb_lch v lt /\ rb_root_color v true) -> ~(rb_root_color lt true).
  Axiom no_red_red_root_red_rt_not_red : forall (v : rbtree Z) (rt : rbtree Z), (no_red_red v /\ rb_rch v rt /\ rb_root_color v true) -> ~(rb_root_color rt true).
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

  Lemma rbtree_positive_num_black_is_not_rb_leaf : forall (l : rbtree Z), forall (n : Z), (num_black l n /\ n > 0) -> ~rb_leaf l. Admitted.
  Lemma rbtree_no_rb_leaf_exists_rb_root_color : forall (l : rbtree Z), exists (x : bool), ~rb_leaf l -> rb_root_color l x. Admitted.
  Lemma rbtree_no_rb_leaf_exists_ch : forall (l : rbtree Z), exists (l1 : rbtree Z), exists (l2 : rbtree Z), ~rb_leaf l -> (rb_lch l l1 /\ rb_rch l l2). Admitted.
  Lemma rbtree_no_rb_leaf_exists_rb_root : forall (l : rbtree Z), exists (x : Z), ~rb_leaf l -> rb_root l x. Admitted.
  Lemma num_black_root_black_lt_minus_1 : forall (v : rbtree Z), forall (lt : rbtree Z), forall (h : Z), (rb_root_color v false /\ (num_black v h /\ rb_lch v lt)) -> num_black lt (h - 1). Admitted.
  Lemma num_black_root_black_rt_minus_1 : forall (v : rbtree Z), forall (rt : rbtree Z), forall (h : Z), (rb_root_color v false /\ (num_black v h /\ rb_rch v rt)) -> num_black rt (h - 1). Admitted.
  Lemma no_red_red_lt : forall (v : rbtree Z), forall (lt : rbtree Z), (no_red_red v /\ rb_lch v lt) -> no_red_red lt. Admitted.
  Lemma no_red_red_rt : forall (v : rbtree Z), forall (rt : rbtree Z), (no_red_red v /\ rb_rch v rt) -> no_red_red rt. Admitted.
  Lemma root_color_single : forall (v : rbtree Z), ~(rb_root_color v false /\ rb_root_color v true). Admitted.
  Lemma black_lt_black_num_black_gt_1 : forall (v : rbtree Z), forall (lt : rbtree Z), forall (h : Z), (num_black v h /\ (rb_lch v lt /\ (rb_root_color v false /\ rb_root_color lt false))) -> h > 1. Admitted.
  Lemma black_rt_black_num_black_gt_1 : forall (v : rbtree Z), forall (rt : rbtree Z), forall (h : Z), (num_black v h /\ (rb_rch v rt /\ (rb_root_color v false /\ rb_root_color rt false))) -> h > 1. Admitted.
  Lemma num_black_root_red_lt_same : forall (v : rbtree Z) (lt : rbtree Z) (h : Z),
    (rb_root_color v true /\ num_black v h /\ rb_lch v lt) -> (num_black lt h).
  Proof.
    intros [] lt h [Hrc [Hnb Hl]].
    - contradiction.
    - simpl in *. subst. intuition.
  Qed.

  Lemma num_black_root_red_rt_same : forall (v : rbtree Z) (rt : rbtree Z) (h : Z),
    (rb_root_color v true /\ num_black v h /\ rb_rch v rt) -> (num_black rt h).
  Proof.
    intros [] lt h [Hrc [Hnb Hr]].
    - contradiction.
    - simpl in *. subst. intuition.
  Qed.

  Lemma no_red_red_root_red_lt_not_red : forall (v : rbtree Z) (lt : rbtree Z),
    (no_red_red v /\ rb_lch v lt /\ rb_root_color v true) -> ~(rb_root_color lt true).
  Proof.
    intros [] [] [Hrr [Hl Hrc]]; try contradiction.
    - intros [].
    - simpl in *. subst. simpl in Hrr.
      destruct r0; destruct Hrr; subst; discriminate.
  Qed.

  Lemma no_red_red_root_red_rt_not_red : forall (v : rbtree Z) (rt : rbtree Z),
    (no_red_red v /\ rb_rch v rt /\ rb_root_color v true) -> ~(rb_root_color rt true).
  Proof.
    intros [] [] [Hrr [Hl Hrc]]; try contradiction.
    - intros [].
    - simpl in *. subst. simpl in Hrr.
      destruct r; destruct Hrr; try destruct H0; subst; discriminate.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (inv : Z), inv >= 0 -> ((forall (h : Z), (h >= 0 /\ (True -> (h + h) = inv) /\ (False -> ((h + h) + 1) = inv)) -> (forall (v : rbtree Z), False -> ((exists (lt4_1 : rbtree Z), exists (rt4_1 : rbtree Z), exists (x_26 : Z), False) \/ (exists (lt4_2 : rbtree Z), exists (rt4_2 : rbtree Z), exists (x_27 : Z), False) \/ (exists (lt3 : rbtree Z), exists (rt3 : rbtree Z), False)))) /\ (forall (h_0 : Z), (h_0 >= 0 /\ (False -> (h_0 + h_0) = inv) /\ (True -> ((h_0 + h_0) + 1) = inv)) -> (forall (v_0 : rbtree Z), (h_0 > 0 /\ num_black v_0 h_0 /\ no_red_red v_0 /\ (True -> (h_0 = 0 -> ~rb_root_color v_0 false))) -> ((exists (lt4_3 : rbtree Z), exists (rt4_3 : rbtree Z), exists (x_29 : Z), False) \/ (exists (lt4_4 : rbtree Z), exists (rt4_4 : rbtree Z), exists (x_30 : Z), h_0 > 0 /\ (inv - 2) >= 0 /\ (inv - 2) < inv /\ (h_0 - 1) >= 0 /\ (((h_0 - 1) + (h_0 - 1)) + 1) = (inv - 2) /\ num_black lt4_4 (h_0 - 1) /\ no_red_red lt4_4 /\ ((h_0 - 1) = 0 -> ~rb_root_color lt4_4 false) /\ num_black rt4_4 (h_0 - 1) /\ no_red_red rt4_4 /\ ((h_0 - 1) = 0 -> ~rb_root_color rt4_4 false) /\ rb_root_color v_0 false /\ rb_root v_0 x_30 /\ rb_lch v_0 lt4_4 /\ rb_rch v_0 rt4_4) \/ (exists (lt3_0 : rbtree Z), exists (rt3_0 : rbtree Z), h_0 > 0 /\ (inv - 1) >= 0 /\ (inv - 1) < inv /\ h_0 >= 0 /\ (h_0 + h_0) = (inv - 1) /\ num_black lt3_0 h_0 /\ no_red_red lt3_0 /\ num_black rt3_0 h_0 /\ no_red_red rt3_0 /\ ~rb_root_color rt3_0 true /\ ~rb_root_color lt3_0 true /\ (exists (x_31 : Z), rb_root v_0 x_31 /\ rb_lch v_0 lt3_0 /\ rb_rch v_0 rt3_0 /\ ~rb_root_color v_0 false /\ rb_root_color v_0 true)))))).
  Proof.
    intros inv Hinv. split.
    - intros. contradiction.
    - intros h0 [Hh0 [Hf Ht]] v0 [Hh0' [Hnb [Hrr Ht1]]]. right.
      assert (~rb_leaf v0) by (apply (rbtree_positive_num_black_is_not_rb_leaf v0 h0); intuition).
      destruct (rbtree_no_rb_leaf_exists_rb_root_color v0) as [b Hb].
      destruct (rbtree_no_rb_leaf_exists_rb_root v0) as [x Hrt].
      destruct (rbtree_no_rb_leaf_exists_ch v0) as [l [r Hch]].
      intuition.
      destruct b.
      * right. exists l. exists r. intuition.
        + apply (num_black_root_red_lt_same v0 l). intuition.
        + apply (no_red_red_lt v0 l). intuition.
        + apply (num_black_root_red_rt_same v0 r). intuition.
        + apply (no_red_red_rt v0 r). intuition.
        + apply (no_red_red_root_red_rt_not_red v0 r); intuition.
        + apply (no_red_red_root_red_lt_not_red v0 l); intuition.
        + exists x. intuition.
          remember (root_color_single v0). intuition.
      * left. exists l. exists r. exists x.
        assert (num_black l (h0 - 1)) by (apply (num_black_root_black_lt_minus_1 v0 l); intuition).
        assert (num_black r (h0 - 1)) by (apply (num_black_root_black_rt_minus_1 v0 r); intuition).
        intuition.
        + apply (no_red_red_lt v0 l). intuition.
        + assert (h0 > 1) by (apply (black_lt_black_num_black_gt_1 v0 l h0); intuition).
          assert (h0 = 1) by lia.
          lia.
        + apply (no_red_red_rt v0 r). intuition.
        + assert (h0 > 1) by (apply (black_rt_black_num_black_gt_1 v0 r h0); intuition).
          assert (h0 = 1) by lia.
          lia.
  Qed.
End Goal.
