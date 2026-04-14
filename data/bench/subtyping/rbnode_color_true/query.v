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
  Parameter rb_root_color : forall {a : Type}, rbtree a -> Prop -> Prop.
  Parameter rb_lch : forall {a : Type}, rbtree a -> rbtree a -> Prop.
  Parameter rb_rch : forall {a : Type}, rbtree a -> rbtree a -> Prop.
  Parameter no_red_red : forall {a : Type}, rbtree a -> Prop.


  Axiom num_black_root_from_lt_rt_plus_1 : forall (v : rbtree Z) (lt : rbtree Z) (rt : rbtree Z) (h : Z), (num_black lt h /\ num_black rt h /\ rb_rch v rt /\ rb_lch v lt /\ rb_root_color v False) -> (num_black v (h + 1)).
  Axiom root_color_single : forall (v : rbtree Z), ~(rb_root_color v False /\ rb_root_color v True).
  Axiom no_red_red_given_lt_rt_black_root : forall (v : rbtree Z) (lt : rbtree Z) (rt : rbtree Z), (no_red_red lt /\ no_red_red rt /\ rb_lch v lt /\ rb_rch v rt /\ rb_root_color v False) -> (no_red_red v).
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
  Definition rb_root_color {a : Type} (t : rbtree a) (c : Prop) : Prop :=
    match t with
    | Rbtleaf _ => False
    | Rbtnode _ c1 _ _ _ => (c /\ c1 = true) \/ (~c /\ c1 = false)
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


  Lemma num_black_root_from_lt_rt_plus_1 : forall (v : rbtree Z) (lt : rbtree Z) (rt : rbtree Z) (h : Z),
    (num_black lt h /\ num_black rt h /\ rb_rch v rt /\ rb_lch v lt /\ rb_root_color v False) -> (num_black v (h + 1)).
  Proof.
    intros [] lt rt h H; intuition; try contradiction.
    simpl in *. intuition. subst.
    replace (h + 1 - 1) with h by lia.
    intuition.
  Qed.

  Lemma root_color_single : forall (v : rbtree Z), ~(rb_root_color v False /\ rb_root_color v True).
  Proof.
    intros [] [Hcf Hct].
    - contradiction.
    - simpl in *. destruct b; lia.
  Qed.

  Lemma no_red_red_given_lt_rt_black_root : forall (v : rbtree Z) (lt : rbtree Z) (rt : rbtree Z),
    (no_red_red lt /\ no_red_red rt /\ rb_lch v lt /\ rb_rch v rt /\ rb_root_color v False) -> (no_red_red v).
  Proof.
    intros [] lt rt H; intuition; try contradiction.
    simpl in *. intuition. subst.
    simpl. intuition.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (inv : Z), inv >= 0 -> ((forall (h : Z), (h >= 0 /\ (True -> (h + h) = inv) /\ (False -> ((h + h) + 1) = inv)) -> (forall (v : rbtree Z), (h > 0 /\ (inv - 1) >= 0 /\ (inv - 1) < inv /\ (h - 1) >= 0 /\ (((h - 1) + (h - 1)) + 1) = (inv - 1) /\ (exists (lt2 : rbtree Z), num_black lt2 (h - 1) /\ no_red_red lt2 /\ ((h - 1) = 0 -> ~rb_root_color lt2 False) /\ (inv - 1) >= 0 /\ (inv - 1) < inv /\ (h - 1) >= 0 /\ (((h - 1) + (h - 1)) + 1) = (inv - 1) /\ (exists (rt2 : rbtree Z), num_black rt2 (h - 1) /\ no_red_red rt2 /\ ((h - 1) = 0 -> ~rb_root_color rt2 False) /\ (exists (x_13 : Z), rb_root_color v False /\ rb_root v x_13 /\ rb_lch v lt2 /\ rb_rch v rt2)))) -> (h > 0 /\ num_black v h /\ no_red_red v /\ (True -> ~rb_root_color v True)))) /\ (forall (h_0 : Z), (h_0 >= 0 /\ (False -> (h_0 + h_0) = inv) /\ (True -> ((h_0 + h_0) + 1) = inv)) -> (forall (v_0 : rbtree Z), True))).
  Proof.
    intros inv Hinv. intuition;
    destruct H8 as [l Hl]; intuition.
    - destruct H15 as [r Hr]. intuition.
      destruct H18 as [rt Hrt]. intuition.
      replace h with (h - 1 + 1) by lia.
      apply (num_black_root_from_lt_rt_plus_1 v l r).
      intuition.
    - destruct H15 as [r Hr]. intuition.
      destruct H18 as [rt Hrt]. intuition.
      apply (no_red_red_given_lt_rt_black_root v l r).
      intuition.
    - destruct H17 as [r Hr]. intuition.
      destruct H20 as [rt Hrt]. intuition.
      apply (root_color_single v). intuition.
  Qed.
End Goal.
