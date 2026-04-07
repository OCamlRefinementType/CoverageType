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
  Parameter lower_bound : tree Z -> Z -> Prop.
  Parameter upper_bound : tree Z -> Z -> Prop.
  Parameter bst : tree Z -> Prop.

  Axiom tree_depth_node_lch : forall (l : tree Z), forall (l1 : tree Z), forall (l2 : tree Z), forall (n1 : Z), forall (n2 : Z), (depth l1 n1 /\ (depth l2 n2 /\ (lch l l1 /\ (rch l l2 /\ n1 >= n2)))) -> depth l (n1 + 1).
  Axiom tree_depth_node_rch : forall (l : tree Z), forall (l1 : tree Z), forall (l2 : tree Z), forall (n1 : Z), forall (n2 : Z), (depth l1 n1 /\ (depth l2 n2 /\ (lch l l1 /\ (rch l l2 /\ n2 >= n1)))) -> depth l (n2 + 1).
  Axiom tree_root_no_leaf : forall (l : tree Z) (x : Z), (root l x) -> ~(leaf l).
  Axiom tree_leaf_or_root : forall (l : tree Z), leaf l \/ exists (x : Z), root l x.
  Axiom tree_node_bst : forall (l : tree Z) (l1 : tree Z) (l2 : tree Z) (x : Z), (bst l1 /\ bst l2 /\ lch l l1 /\ rch l l2 /\ root l x /\ ((not (leaf l1)) -> (upper_bound l1 x)) /\ ((not (leaf l2)) -> (lower_bound l2 x))) -> (bst l).
  Axiom tree_lower_bound_base : forall (l : tree Z) (l1 : tree Z) (x : Z) (y : Z), (bst l /\ root l x /\ lch l l1 /\ leaf l1 /\ y < x) -> (lower_bound l y).
  Axiom tree_lower_bound_other : forall (l : tree Z) (l1 : tree Z) (x : Z) (y : Z), (bst l /\ root l x /\ lch l l1 /\ ~(leaf l1) /\ lower_bound l1 y /\ y < x) -> (lower_bound l y).
  Axiom tree_upper_bound_base : forall (l : tree Z) (l1 : tree Z) (x : Z) (y : Z), (bst l /\ root l x /\ rch l l1 /\ leaf l1 /\ y > x) -> (upper_bound l y).
  Axiom tree_upper_bound_other : forall (l : tree Z) (l1 : tree Z) (x : Z) (y : Z), (bst l /\ root l x /\ rch l l1 /\ ~(leaf l1) /\ upper_bound l1 y /\ y > x) -> (upper_bound l y).
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
  Fixpoint lower_bound (t : tree Z) (x : Z) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ y l r => x <= y /\ lower_bound l x /\ lower_bound r x
    end.
  Fixpoint upper_bound (t : tree Z) (x : Z) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ y l r => y <= x /\ upper_bound l x /\ upper_bound r x
    end.
  Fixpoint bst (t : tree Z) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ x l r => bst l /\ bst r /\ upper_bound l x /\ lower_bound r x
    end.

  Lemma tree_depth_node_lch : forall (l : tree Z), forall (l1 : tree Z), forall (l2 : tree Z), forall (n1 : Z), forall (n2 : Z), (depth l1 n1 /\ (depth l2 n2 /\ (lch l l1 /\ (rch l l2 /\ n1 >= n2)))) -> depth l (n1 + 1). Admitted.
  Lemma tree_depth_node_rch : forall (l : tree Z), forall (l1 : tree Z), forall (l2 : tree Z), forall (n1 : Z), forall (n2 : Z), (depth l1 n1 /\ (depth l2 n2 /\ (lch l l1 /\ (rch l l2 /\ n2 >= n1)))) -> depth l (n2 + 1). Admitted.
  Lemma tree_root_no_leaf : forall (l : tree Z) (x : Z), (root l x) -> ~(leaf l).
  Proof.
    intros [| x] x' Hr.
    - contradiction.
    - intros [].
  Qed.

  Lemma tree_leaf_or_root : forall (l : tree Z), leaf l \/ exists (x : Z), root l x.
  Proof.
    intros [| x].
    - left. reflexivity.
    - right. exists x. reflexivity.
  Qed.

  Lemma tree_node_bst : forall (l : tree Z) (l1 : tree Z) (l2 : tree Z) (x : Z),
    (bst l1 /\ bst l2 /\ lch l l1 /\ rch l l2 /\ root l x
    /\ ((not (leaf l1)) -> (upper_bound l1 x))
    /\ ((not (leaf l2)) -> (lower_bound l2 x)))
    -> (bst l).
  Proof.
    intros [| x] [| y] [| z] x' H;
    decompose [and] H; try contradiction;
    inversion H1; inversion H3; subst; simpl.
    - intuition.
    - simpl in H2. inversion H4. subst.
      simpl in H7. intuition.
    - simpl in H0. inversion H4. subst.
      simpl in H5. intuition.
    - inversion H4. subst.
      simpl in H0. simpl in H2.
      simpl in H5. simpl in H7. intuition.
  Qed.

  Lemma tree_lower_bound_base : forall (l : tree Z) (l1 : tree Z) (x : Z) (y : Z),
    (bst l /\ root l x /\ lch l l1 /\ leaf l1 /\ y < x) -> (lower_bound l y).
  Proof.
    intros [| x] [] x' y [Hb [Hr [Hlch [Hl Hlt]]]];
    try contradiction.
    simpl. inversion Hr. inversion Hlch. subst.
    simpl in Hb. intuition.
    induction t0.
    - reflexivity.
    - simpl. simpl in H1. simpl in H3. intuition.
  Qed.

  Lemma tree_lower_bound_other : forall (l : tree Z) (l1 : tree Z) (x : Z) (y : Z),
    (bst l /\ root l x /\ lch l l1 /\ ~(leaf l1) /\ lower_bound l1 y /\ y < x)
    -> (lower_bound l y).
  Proof.
    intros [| x] [] x' y [Hb [Hr [Hlch [Hnl [Hlb Hlt]]]]];
    try contradiction.
    simpl. inversion Hr. inversion Hlch. subst.
    simpl in Hb. intuition.
    induction t0.
    - reflexivity.
    - simpl. simpl in H. simpl in H5. intuition.
  Qed.

  Lemma tree_upper_bound_base : forall (l : tree Z) (l1 : tree Z) (x : Z) (y : Z),
    (bst l /\ root l x /\ rch l l1 /\ leaf l1 /\ y > x) -> (upper_bound l y).
  Proof.
    intros [| x] [] x' y [Hb [Hr [Hrch [Hl Hlt]]]];
    try contradiction.
    simpl. inversion Hr. inversion Hrch. subst.
    simpl in Hb. intuition.
    induction t.
    - reflexivity.
    - simpl. simpl in H. simpl in H0. intuition.
  Qed.

  Lemma tree_upper_bound_other : forall (l : tree Z) (l1 : tree Z) (x : Z) (y : Z),
    (bst l /\ root l x /\ rch l l1 /\ ~(leaf l1) /\ upper_bound l1 y /\ y > x)
    -> (upper_bound l y).
  Proof.
    intros [| x] [] x' y [Hb [Hr [Hrch [Hnl [Hlb Hlt]]]]];
    try contradiction.
    simpl. inversion Hr. inversion Hrch. subst.
    simpl in Hb. intuition.
    induction t.
    - reflexivity.
    - simpl. simpl in H. simpl in H1. intuition.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (d : Z), 0 <= d -> (forall (lo : Z), forall (hi : Z), lo < hi -> (forall (v : tree Z), (exists (lt : tree Z), exists (rt : tree Z), exists (d_2 : Z), exists (x : Z), d > 0 /\ (lo + 1) < hi /\ lo < x /\ x < hi /\ 0 <= (d - 1) /\ (d - 1) >= 0 /\ (d - 1) < d /\ (~leaf lt -> lower_bound lt lo) /\ (~leaf lt -> upper_bound lt x) /\ bst lt /\ (exists (n2 : Z), depth lt n2 /\ n2 <= (d - 1)) /\ 0 <= d_2 /\ d_2 >= 0 /\ d_2 < d /\ d_2 = (d - 1) /\ (~leaf rt -> lower_bound rt x) /\ (~leaf rt -> upper_bound rt hi) /\ bst rt /\ (exists (n3 : Z), depth rt n3 /\ n3 <= d_2) /\ root v x /\ lch v lt /\ rch v rt /\ (exists (nl : Z), exists (nr : Z), depth lt nl /\ depth rt nr /\ (nl > nr -> depth v (nl + 1)) /\ (nr >= nl -> depth v (nr + 1)))) -> (d > 0 /\ (~leaf v -> lower_bound v lo) /\ (~leaf v -> upper_bound v hi) /\ bst v /\ ~leaf v /\ (exists (n1 : Z), depth v n1 /\ n1 <= d)))).
  Proof.
    intros d Hd lo hi Hlh v [lt [rh [d2 [x H]]]].
    decompose [and] H. subst.
    assert (bst lt /\ bst rh /\ lch v lt /\ rch v rh /\ root v x /\ (~ leaf lt -> upper_bound lt x) /\ (~ leaf rh -> lower_bound rh x)) as Hq by intuition.
    remember (tree_node_bst v lt rh x Hq) as Hbst.
    repeat split; try assumption.
    - intros Hnl. destruct (tree_leaf_or_root lt).
      * apply (tree_lower_bound_base v lt x lo).
        repeat split; assumption.
      * destruct H14 as [x' Hr].
        apply tree_root_no_leaf in Hr.
        apply (tree_lower_bound_other v lt x lo).
        repeat split; try assumption.
        apply (H7 Hr).
    - intros Hnl. destruct (tree_leaf_or_root rh).
      * apply (tree_upper_bound_base v rh x hi).
        repeat split; try assumption. lia.
      * destruct H14 as [x' Hr].
        apply tree_root_no_leaf in Hr.
        apply (tree_upper_bound_other v rh x hi).
        repeat split; try assumption.
        apply (H16 Hr).
        lia.
    - apply (tree_root_no_leaf v x H19).
    - destruct H10 as [n2 [Hdn2 Hn2]].
      destruct H18 as [n3 [Hdn3 Hn3]].
      destruct (n2 >=? n3) eqn:Hnc.
      * exists (n2 + 1). split.
        + apply (tree_depth_node_lch v lt rh n2 n3).
          repeat split; try assumption.
          apply Z.geb_ge. assumption.
        + lia.
      * exists (n3 + 1). split.
        + apply (tree_depth_node_rch v lt rh n2 n3).
          repeat split; try assumption.
          lia.
        + lia.
  Qed.
End Goal.
