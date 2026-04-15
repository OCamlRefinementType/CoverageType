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

  Axiom no_red_red_given_lt_rt_black_root : forall (v : rbtree Z), forall (lt : rbtree Z), forall (rt : rbtree Z), (no_red_red lt /\ (no_red_red rt /\ (rb_lch v lt /\ (rb_rch v rt /\ rb_root_color v false)))) -> no_red_red v.
  Axiom num_black_root_from_lt_rt_plus_1 : forall (v : rbtree Z), forall (lt : rbtree Z), forall (rt : rbtree Z), forall (h : Z), (num_black lt h /\ (num_black rt h /\ (rb_rch v rt /\ (rb_lch v lt /\ rb_root_color v false)))) -> num_black v (h + 1).
  Axiom num_black_root_from_lt_rt : forall (v : rbtree Z), forall (lt : rbtree Z), forall (rt : rbtree Z), forall (h : Z), (num_black lt h /\ (num_black rt h /\ (rb_rch v rt /\ (rb_lch v lt /\ rb_root_color v true)))) -> num_black v h.
  Axiom no_red_red_given_lt_rt_red_root : forall (v : rbtree Z) (lt : rbtree Z) (rt : rbtree Z), (no_red_red lt /\ no_red_red rt /\ rb_lch v lt /\ rb_rch v rt /\ ~(rb_root_color lt true) /\ ~(rb_root_color rt true) /\ rb_root_color v true) -> (no_red_red v).
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

  Lemma no_red_red_given_lt_rt_black_root : forall (v : rbtree Z), forall (lt : rbtree Z), forall (rt : rbtree Z), (no_red_red lt /\ (no_red_red rt /\ (rb_lch v lt /\ (rb_rch v rt /\ rb_root_color v false)))) -> no_red_red v. Admitted.
  Lemma num_black_root_from_lt_rt_plus_1 : forall (v : rbtree Z), forall (lt : rbtree Z), forall (rt : rbtree Z), forall (h : Z), (num_black lt h /\ (num_black rt h /\ (rb_rch v rt /\ (rb_lch v lt /\ rb_root_color v false)))) -> num_black v (h + 1). Admitted.
  Lemma num_black_root_from_lt_rt : forall (v : rbtree Z), forall (lt : rbtree Z), forall (rt : rbtree Z), forall (h : Z), (num_black lt h /\ (num_black rt h /\ (rb_rch v rt /\ (rb_lch v lt /\ rb_root_color v true)))) -> num_black v h. Admitted.
  Lemma no_red_red_given_lt_rt_red_root : forall (v : rbtree Z) (lt : rbtree Z) (rt : rbtree Z),
    (no_red_red lt /\ no_red_red rt /\ rb_lch v lt /\ rb_rch v rt
    /\ ~(rb_root_color lt true)
    /\ ~(rb_root_color rt true)
    /\ rb_root_color v true)
    -> (no_red_red v).
  Proof.
    intros [] [] [] H; intuition; try contradiction;
    simpl in *; intuition; subst; simpl.
    - reflexivity.
    - destruct b0; try (intuition; contradiction).
    - destruct b0; try (intuition; contradiction).
    - destruct b0, b1; try (intuition; contradiction).
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (inv : Z), inv >= 0 -> ((forall (h : Z), (h >= 0 /\ (True -> (h + h) = inv) /\ (False -> ((h + h) + 1) = inv)) -> (forall (v : rbtree Z), ((exists (lt4_1 : rbtree Z), exists (rt4_1 : rbtree Z), exists (x_26 : Z), False) \/ (exists (lt4_2 : rbtree Z), exists (rt4_2 : rbtree Z), exists (x_27 : Z), False) \/ (exists (lt3 : rbtree Z), exists (rt3 : rbtree Z), exists (x_28 : Z), False)) -> False)) /\ (forall (h_0 : Z), (h_0 >= 0 /\ (False -> (h_0 + h_0) = inv) /\ (True -> ((h_0 + h_0) + 1) = inv)) -> (forall (v_0 : rbtree Z), ((exists (lt4_3 : rbtree Z), exists (rt4_3 : rbtree Z), exists (x_29 : Z), False) \/ (exists (lt4_4 : rbtree Z), exists (rt4_4 : rbtree Z), exists (x_30 : Z), h_0 > 0 /\ (inv - 2) >= 0 /\ (inv - 2) < inv /\ (h_0 - 1) >= 0 /\ (((h_0 - 1) + (h_0 - 1)) + 1) = (inv - 2) /\ num_black lt4_4 (h_0 - 1) /\ no_red_red lt4_4 /\ ((h_0 - 1) = 0 -> ~rb_root_color lt4_4 false) /\ num_black rt4_4 (h_0 - 1) /\ no_red_red rt4_4 /\ ((h_0 - 1) = 0 -> ~rb_root_color rt4_4 false) /\ rb_root_color v_0 false /\ rb_root v_0 x_30 /\ rb_lch v_0 lt4_4 /\ rb_rch v_0 rt4_4) \/ (exists (lt3_0 : rbtree Z), exists (rt3_0 : rbtree Z), exists (x_31 : Z), h_0 > 0 /\ (inv - 1) >= 0 /\ (inv - 1) < inv /\ h_0 >= 0 /\ (h_0 + h_0) = (inv - 1) /\ num_black lt3_0 h_0 /\ no_red_red lt3_0 /\ num_black rt3_0 h_0 /\ no_red_red rt3_0 /\ ~rb_root_color rt3_0 true /\ ~rb_root_color lt3_0 true /\ rb_root v_0 x_31 /\ rb_lch v_0 lt3_0 /\ rb_rch v_0 rt3_0 /\ ~rb_root_color v_0 false /\ rb_root_color v_0 true)) -> (h_0 > 0 /\ num_black v_0 h_0 /\ no_red_red v_0 /\ (True -> (h_0 = 0 -> ~rb_root_color v_0 false)))))).
  Proof.
    intros inv Hinv. split.
    - intros.
      destruct H0. destruct H0 as [_ [_ [_ []]]].
      destruct H0. destruct H0 as [_ [_ [_ []]]].
      destruct H0 as [_ [_ [_ []]]].
    - intros h0 [Hh0 [Hf Ht]] v0 [[_ [_ [_ []]]] | [[lt [rt [x H1]]] | [lt [rt [x H2]]]]].
      * intuition.
        + replace h0 with (h0 - 1 + 1) by lia.
          apply (num_black_root_from_lt_rt_plus_1 v0 lt rt).
          intuition.
        + apply (no_red_red_given_lt_rt_black_root v0 lt rt).
          intuition.
      * intuition.
        + apply (num_black_root_from_lt_rt v0 lt rt).
          intuition.
        + apply (no_red_red_given_lt_rt_red_root v0 lt rt).
          intuition.
  Qed.
End Goal.
