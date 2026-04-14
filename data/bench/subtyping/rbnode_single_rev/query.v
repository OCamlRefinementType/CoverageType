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


  Axiom rbtree_rb_root_color_no_rb_leaf : forall (l : rbtree Z) (x : Prop), (rb_root_color l x) -> ~(rb_leaf l).
  Axiom rbtree_no_rb_leaf_exists_ch : forall (l : rbtree Z), exists (l1 : rbtree Z) (l2 : rbtree Z), ~(rb_leaf l) -> (rb_lch l l1 /\ rb_rch l l2).
  Axiom rbtree_leaf_is_leaf : forall (l : rbtree Z) (l2 : rbtree Z), (rb_leaf l /\ rb_leaf l2) -> (l = l2).
  Axiom num_black_root_black_0_lt_leaf : forall (v : rbtree Z) (lt : rbtree Z), (no_red_red v /\ num_black v 0 /\ rb_lch v lt) -> (rb_leaf lt).
  Axiom num_black_root_black_0_rt_leaf : forall (v : rbtree Z) (rt : rbtree Z), (no_red_red v /\ num_black v 0 /\ rb_rch v rt) -> (rb_leaf rt).
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


  Lemma rbtree_rb_root_color_no_rb_leaf : forall (l : rbtree Z) (x : Prop), (rb_root_color l x) -> ~(rb_leaf l).
  Proof.
    intros [] x Hc.
    - contradiction.
    - auto.
  Qed.

  Lemma rbtree_no_rb_leaf_exists_ch : forall (l : rbtree Z), exists (l1 : rbtree Z) (l2 : rbtree Z),
    ~(rb_leaf l) -> (rb_lch l l1 /\ rb_rch l l2).
  Proof.
    intros [].
    - exists (Rbtleaf Z). exists (Rbtleaf Z).
      intros []. reflexivity.
    - exists r. exists r0.
      intros Hl. split; reflexivity.
  Qed.

  Lemma rbtree_leaf_is_leaf : forall (l : rbtree Z) (l2 : rbtree Z), (rb_leaf l /\ rb_leaf l2) -> (l = l2).
  Proof.
    intros [] [] [Hl1 Hl2]; try contradiction.
    reflexivity.
  Qed.

  Lemma rbtree_num_black_geq_0 : forall (l : rbtree Z) (n : Z), (num_black l n) -> (n >= 0).
  Proof.
    induction l; intros n Hnb; simpl in Hnb.
    - lia.
    - destruct b; intuition. apply IHl1 in H. lia.
  Qed.
  Lemma num_black_root_black_0_lt_leaf : forall (v : rbtree Z) (lt : rbtree Z),
    (no_red_red v /\ num_black v 0 /\ rb_lch v lt) -> (rb_leaf lt).
  Proof.
    intros [] [] [Hr [Hnb Hl]]; try contradiction.
    - reflexivity.
    - destruct b, b0; simpl in *; subst.
      + destruct r0; destruct Hr; discriminate.
      + destruct Hnb. simpl in *.
        destruct H. apply rbtree_num_black_geq_0 in H1. lia.
      + destruct Hnb. apply rbtree_num_black_geq_0 in H. lia.
      + destruct Hnb. apply rbtree_num_black_geq_0 in H. lia.
  Qed.

  Lemma num_black_root_black_0_rt_leaf : forall (v : rbtree Z) (rt : rbtree Z),
    (no_red_red v /\ num_black v 0 /\ rb_rch v rt) -> (rb_leaf rt).
  Proof.
    intros [] [] [Hr [Hnb Hrc]]; try contradiction.
    - reflexivity.
    - destruct b, b0; simpl in *; subst.
      + destruct r; decompose [and] Hr; discriminate.
      + destruct Hnb. simpl in H0.
        destruct H0. apply rbtree_num_black_geq_0 in H0. lia.
      + destruct Hnb. apply rbtree_num_black_geq_0 in H. lia.
      + destruct Hnb. apply rbtree_num_black_geq_0 in H. lia.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (inv : Z), inv >= 0 -> ((forall (h : Z), (h >= 0 /\ (True -> (h + h) = inv) /\ (False -> ((h + h) + 1) = inv)) -> (forall (v : rbtree Z), (~rb_root_color v False /\ rb_root_color v True /\ num_black v 0 /\ no_red_red v) -> (exists (t : rbtree Z), rb_leaf t /\ rb_root_color v True /\ ~rb_root_color v False /\ rb_lch v t /\ rb_rch v t))) /\ (forall (h_0 : Z), (h_0 >= 0 /\ (False -> (h_0 + h_0) = inv) /\ (True -> ((h_0 + h_0) + 1) = inv)) -> (forall (v_0 : rbtree Z), (~rb_root_color v_0 False /\ rb_root_color v_0 True /\ num_black v_0 0 /\ no_red_red v_0) -> (exists (t_0 : rbtree Z), rb_leaf t_0 /\ rb_root_color v_0 True /\ ~rb_root_color v_0 False /\ rb_lch v_0 t_0 /\ rb_rch v_0 t_0)))).
  Proof.
    intros inv Hinv. intuition.
    - set (Hnl := (rbtree_rb_root_color_no_rb_leaf v _ H)).
      destruct (rbtree_no_rb_leaf_exists_ch v) as [l [r Hch]].
      assert (rb_leaf l) by (apply (num_black_root_black_0_lt_leaf v l); intuition).
      assert (rb_leaf r) by (apply (num_black_root_black_0_rt_leaf v r); intuition).
      assert (l = r) by (apply rbtree_leaf_is_leaf; intuition).
      subst. exists r. 
      intuition.
    - set (Hnl := (rbtree_rb_root_color_no_rb_leaf v_0 _ H2)).
      destruct (rbtree_no_rb_leaf_exists_ch v_0) as [l [r Hch]].
      assert (rb_leaf l) by (apply (num_black_root_black_0_lt_leaf v_0 l); intuition).
      assert (rb_leaf r) by (apply (num_black_root_black_0_rt_leaf v_0 r); intuition).
      assert (l = r) by (apply rbtree_leaf_is_leaf; intuition).
      subst. exists r. 
      intuition.
  Qed.
End Goal.
