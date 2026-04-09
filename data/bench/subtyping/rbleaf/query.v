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


  Axiom rbtree_rb_leaf_no_rb_root_color : forall (l : rbtree Z) (x : Prop), (rb_leaf l) -> ~(rb_root_color l x).
  Axiom rbtree_rb_leaf_no_red_red : forall (l : rbtree Z), (rb_leaf l) -> (no_red_red l).
  Axiom rbtree_rb_leaf_num_black_0_second : forall (l : rbtree Z), (rb_leaf l) -> (num_black l 0).
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


  Lemma rbtree_rb_leaf_no_rb_root_color : forall (l : rbtree Z) (x : Prop), (rb_leaf l) -> ~(rb_root_color l x).
  Proof.
    intros [] x Hl.
    - intros [].
    - contradiction.
  Qed.

  Lemma rbtree_rb_leaf_no_red_red : forall (l : rbtree Z), (rb_leaf l) -> (no_red_red l).
  Proof.
    intros [] Hl.
    - reflexivity.
    - contradiction.
  Qed.

  Lemma rbtree_rb_leaf_num_black_0_second : forall (l : rbtree Z), (rb_leaf l) -> (num_black l 0).
  Proof.
    intros [] Hl.
    - reflexivity.
    - contradiction.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (inv : Z), inv >= 0 -> ((forall (h : Z), (h >= 0 /\ (True -> (h + h) = inv) /\ (False -> ((h + h) + 1) = inv)) -> (forall (v : rbtree Z), (h = 0 /\ rb_leaf v /\ (True -> ~rb_root_color v True) /\ (False -> (h = 0 -> ~rb_root_color v False))) -> (h = 0 /\ ~rb_root_color v False /\ ~rb_root_color v True /\ num_black v h /\ no_red_red v /\ (True -> ~rb_root_color v True) /\ (False -> (h = 0 -> ~rb_root_color v False))))) /\ (forall (h_0 : Z), (h_0 >= 0 /\ (False -> (h_0 + h_0) = inv) /\ (True -> ((h_0 + h_0) + 1) = inv)) -> (forall (v_0 : rbtree Z), True))).
  Proof.
    intros inc Hinv. split.
    - intros h [Hh [Ht Hf]] v [Hvh [Hl [Hvt Hvf]]].
      intuition.
      * apply (rbtree_rb_leaf_no_rb_root_color _ _ Hl) in H1. contradiction.
      * subst. apply (rbtree_rb_leaf_num_black_0_second _ Hl).
      * apply (rbtree_rb_leaf_no_red_red _ Hl).
    - intros h0 [Hh0 [Hf Ht]]. reflexivity.
  Qed.
End Goal.
