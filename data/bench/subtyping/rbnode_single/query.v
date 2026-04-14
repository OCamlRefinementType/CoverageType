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

  Axiom rbtree_rb_leaf_num_black_0_second : forall (l : rbtree Z), rb_leaf l -> num_black l 0.
  Axiom rbtree_rb_leaf_no_rb_root_color : forall (l : rbtree Z), forall (x : bool), rb_leaf l -> ~rb_root_color l x.
  Axiom rbtree_rb_leaf_no_red_red : forall (l : rbtree Z), rb_leaf l -> no_red_red l.
  Axiom num_black_root_from_lt_rt : forall (v : rbtree Z) (lt : rbtree Z) (rt : rbtree Z) (h : Z), (num_black lt h /\ num_black rt h /\ rb_rch v rt /\ rb_lch v lt /\ rb_root_color v true) -> (num_black v h).
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

  Lemma rbtree_rb_leaf_num_black_0_second : forall (l : rbtree Z), rb_leaf l -> num_black l 0. Admitted.
  Lemma rbtree_rb_leaf_no_rb_root_color : forall (l : rbtree Z), forall (x : bool), rb_leaf l -> ~rb_root_color l x. Admitted.
  Lemma rbtree_rb_leaf_no_red_red : forall (l : rbtree Z), rb_leaf l -> no_red_red l. Admitted.
  Lemma num_black_root_from_lt_rt : forall (v : rbtree Z) (lt : rbtree Z) (rt : rbtree Z) (h : Z),
    (num_black lt h /\ num_black rt h /\ rb_rch v rt /\ rb_lch v lt /\ rb_root_color v true)
    -> (num_black v h).
  Proof.
    intros [] lt rt h [Hnbl [Hnbr [Hrch [Hlch Hrc]]]].
    - contradiction.
    - simpl in *. intuition. subst. intuition.
  Qed.

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

  Theorem goal : forall (inv : Z), inv >= 0 -> ((forall (h : Z), (h >= 0 /\ (True -> (h + h) = inv) /\ (False -> ((h + h) + 1) = inv)) -> (forall (v : rbtree Z), (exists (t : rbtree Z), rb_leaf t /\ rb_root_color v true /\ ~rb_root_color v false /\ rb_lch v t /\ rb_rch v t) -> (~rb_root_color v false /\ rb_root_color v true /\ num_black v 0 /\ no_red_red v))) /\ (forall (h_0 : Z), (h_0 >= 0 /\ (False -> (h_0 + h_0) = inv) /\ (True -> ((h_0 + h_0) + 1) = inv)) -> (forall (v_0 : rbtree Z), (exists (t_0 : rbtree Z), rb_leaf t_0 /\ rb_root_color v_0 true /\ ~rb_root_color v_0 false /\ rb_lch v_0 t_0 /\ rb_rch v_0 t_0) -> (~rb_root_color v_0 false /\ rb_root_color v_0 true /\ num_black v_0 0 /\ no_red_red v_0)))).
  Proof.
    intros inv Hinv. split.
    - intros h [Hh [Ht Hf]] v [t [Hlt [Hct1 [Hct2 [Hlct Hrct]]]]].
      intuition.
      * apply rbtree_rb_leaf_num_black_0_second in Hlt.
        apply (num_black_root_from_lt_rt v t t). intuition.
      * apply (no_red_red_given_lt_rt_red_root v t t). intuition.
        apply (rbtree_rb_leaf_no_red_red _ Hlt).
        apply (rbtree_rb_leaf_no_red_red _ Hlt).
        apply (rbtree_rb_leaf_no_rb_root_color _ _ Hlt) in H0. contradiction.
        apply (rbtree_rb_leaf_no_rb_root_color _ _ Hlt) in H0. contradiction.
    - intros h0 [Hh0 [Hf Ht]] v0 [t0 Ht0].
      intuition.
      * apply rbtree_rb_leaf_num_black_0_second in H.
        apply (num_black_root_from_lt_rt v0 t0 t0). intuition.
      * apply (no_red_red_given_lt_rt_red_root v0 t0 t0). intuition.
        apply (rbtree_rb_leaf_no_red_red _ H).
        apply (rbtree_rb_leaf_no_red_red _ H).
        apply (rbtree_rb_leaf_no_rb_root_color _ _ H) in H5. contradiction.
        apply (rbtree_rb_leaf_no_rb_root_color _ _ H) in H5. contradiction.
  Qed.
End Goal.
