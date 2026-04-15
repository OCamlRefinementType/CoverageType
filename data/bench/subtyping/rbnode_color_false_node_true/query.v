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

  Axiom no_red_red_given_lt_rt_red_root : forall (v : rbtree Z), forall (lt : rbtree Z), forall (rt : rbtree Z), (no_red_red lt /\ (no_red_red rt /\ (rb_lch v lt /\ (rb_rch v rt /\ (~rb_root_color lt true /\ (~rb_root_color rt true /\ rb_root_color v true)))))) -> no_red_red v.
  Axiom num_black_root_from_lt_rt : forall (v : rbtree Z) (lt : rbtree Z) (rt : rbtree Z) (h : Z), (num_black lt h /\ num_black rt h /\ rb_rch v rt /\ rb_lch v lt /\ rb_root_color v true) -> (num_black v h).
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

  Lemma no_red_red_given_lt_rt_red_root : forall (v : rbtree Z), forall (lt : rbtree Z), forall (rt : rbtree Z), (no_red_red lt /\ (no_red_red rt /\ (rb_lch v lt /\ (rb_rch v rt /\ (~rb_root_color lt true /\ (~rb_root_color rt true /\ rb_root_color v true)))))) -> no_red_red v. Admitted.
  Lemma num_black_root_from_lt_rt : forall (v : rbtree Z) (lt : rbtree Z) (rt : rbtree Z) (h : Z),
    (num_black lt h /\ num_black rt h /\ rb_rch v rt /\ rb_lch v lt /\ rb_root_color v true)
    -> (num_black v h).
  Proof.
    intros [] lt rt h [Hnbl [Hnbr [Hrch [Hlch Hrc]]]].
    - contradiction.
    - simpl in *. intuition. subst. intuition.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (inv : Z), inv >= 0 -> ((forall (h_6 : Z), (h_6 >= 0 /\ (True -> (h_6 + h_6) = inv) /\ (False -> ((h_6 + h_6) + 1) = inv)) -> (forall (v : rbtree Z), ((exists (lt3_1 : rbtree Z), exists (rt3_1 : rbtree Z), exists (inv_7 : Z), exists (inv_8 : Z), exists (h_7 : Z), exists (h_8 : Z), exists (x_22 : Z), False) \/ (exists (lt3_2 : rbtree Z), exists (rt3_2 : rbtree Z), exists (inv_9 : Z), exists (inv_10 : Z), exists (h_9 : Z), exists (h_10 : Z), exists (x_23 : Z), False)) -> False)) /\ (forall (h_11 : Z), (h_11 >= 0 /\ (False -> (h_11 + h_11) = inv) /\ (True -> ((h_11 + h_11) + 1) = inv)) -> (forall (v_0 : rbtree Z), ((exists (lt3_3 : rbtree Z), exists (rt3_3 : rbtree Z), exists (inv_11 : Z), exists (inv_12 : Z), exists (h_12 : Z), exists (h_13 : Z), exists (x_24 : Z), h_11 > 0 /\ inv_11 >= 0 /\ inv_11 < inv /\ inv_11 = (inv - 1) /\ h_12 >= 0 /\ (True -> (h_12 + h_12) = inv_11) /\ (False -> ((h_12 + h_12) + 1) = inv_11) /\ h_12 = h_11 /\ num_black lt3_3 h_12 /\ no_red_red lt3_3 /\ (True -> ~rb_root_color lt3_3 true) /\ (False -> (h_12 = 0 -> ~rb_root_color lt3_3 false)) /\ inv_12 >= 0 /\ inv_12 < inv /\ inv_12 = (inv - 1) /\ h_13 >= 0 /\ (True -> (h_13 + h_13) = inv_12) /\ (False -> ((h_13 + h_13) + 1) = inv_12) /\ h_13 = h_11 /\ num_black rt3_3 h_13 /\ no_red_red rt3_3 /\ (True -> ~rb_root_color rt3_3 true) /\ (False -> (h_13 = 0 -> ~rb_root_color rt3_3 false)) /\ rb_root_color v_0 true /\ rb_root v_0 x_24 /\ rb_lch v_0 lt3_3 /\ rb_rch v_0 rt3_3) \/ (exists (lt3_4 : rbtree Z), exists (rt3_4 : rbtree Z), exists (inv_13 : Z), exists (inv_14 : Z), exists (h_14 : Z), exists (h_15 : Z), exists (x_25 : Z), False)) -> (h_11 > 0 /\ num_black v_0 h_11 /\ no_red_red v_0 /\ rb_root_color v_0 true /\ (True -> (h_11 = 0 -> ~rb_root_color v_0 false)))))).
  Proof.
    intros inv Hinv. split.
    - intros.
      destruct H0 as [[_ [_ [_ [_ [_ [_ []]]]]]] | [_ [_ [_ [_ [_ [_ []]]]]]]];
      contradiction.
    - intros h1 [Hh1 [Hf Ht]] v0 [[l [r [inv1 [inv2 [h2 [h3 [x H]]]]]]] | [_ [_ [_ [_ [_ [_ []]]]]]]];
      try contradiction.
      intuition; subst.
      * apply (num_black_root_from_lt_rt v0 l r). intuition.
      * apply (no_red_red_given_lt_rt_red_root v0 l r). intuition.
  Qed.
End Goal.
