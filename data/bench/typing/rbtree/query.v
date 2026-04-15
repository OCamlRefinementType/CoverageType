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
  Parameter bool_gen : unit -> Prop.
  Parameter int_gen : unit -> Z.
  Parameter sizecheck : Z -> Prop.
  Parameter subs : Z -> Z.

  Axiom rbtree_positive_num_black_is_not_rb_leaf : forall (l : rbtree Z), forall (n : Z), (num_black l n /\ n > 0) -> ~rb_leaf l.
  Axiom rbtree_no_rb_leaf_exists_ch : forall (l : rbtree Z), exists (l1 : rbtree Z), exists (l2 : rbtree Z), ~rb_leaf l -> (rb_lch l l1 /\ rb_rch l l2).
  Axiom rbtree_no_rb_leaf_exists_rb_root : forall (l : rbtree Z), exists (x : Z), ~rb_leaf l -> rb_root l x.
  Axiom rbtree_no_rb_leaf_exists_rb_root_color : forall (l : rbtree Z), exists (x : bool), ~rb_leaf l -> rb_root_color l x.
  Axiom no_red_red_lt : forall (v : rbtree Z), forall (lt : rbtree Z), (no_red_red v /\ rb_lch v lt) -> no_red_red lt.
  Axiom no_red_red_rt : forall (v : rbtree Z), forall (rt : rbtree Z), (no_red_red v /\ rb_rch v rt) -> no_red_red rt.
  Axiom num_black_root_red_lt_same : forall (v : rbtree Z), forall (lt : rbtree Z), forall (h : Z), (rb_root_color v true /\ (num_black v h /\ rb_lch v lt)) -> num_black lt h.
  Axiom num_black_root_red_rt_same : forall (v : rbtree Z), forall (rt : rbtree Z), forall (h : Z), (rb_root_color v true /\ (num_black v h /\ rb_rch v rt)) -> num_black rt h.
  Axiom num_black_root_black_lt_minus_1 : forall (v : rbtree Z), forall (lt : rbtree Z), forall (h : Z), (rb_root_color v false /\ (num_black v h /\ rb_lch v lt)) -> num_black lt (h - 1).
  Axiom num_black_root_black_rt_minus_1 : forall (v : rbtree Z), forall (rt : rbtree Z), forall (h : Z), (rb_root_color v false /\ (num_black v h /\ rb_rch v rt)) -> num_black rt (h - 1).
  Axiom black_lt_black_num_black_gt_1 : forall (v : rbtree Z), forall (lt : rbtree Z), forall (h : Z), (num_black v h /\ (rb_lch v lt /\ (rb_root_color v false /\ rb_root_color lt false))) -> h > 1.
  Axiom black_rt_black_num_black_gt_1 : forall (v : rbtree Z), forall (rt : rbtree Z), forall (h : Z), (num_black v h /\ (rb_rch v rt /\ (rb_root_color v false /\ rb_root_color rt false))) -> h > 1.
  Axiom no_red_red_root_red_lt_not_red : forall (v : rbtree Z), forall (lt : rbtree Z), (no_red_red v /\ (rb_lch v lt /\ rb_root_color v true)) -> ~rb_root_color lt true.
  Axiom no_red_red_root_red_rt_not_red : forall (v : rbtree Z), forall (rt : rbtree Z), (no_red_red v /\ (rb_rch v rt /\ rb_root_color v true)) -> ~rb_root_color rt true.
  Axiom rbtree_num_black_0_rb_leaf : forall (l : rbtree Z), (num_black l 0 /\ ~(rb_root_color l true)) -> (rb_leaf l).
  Axiom rbtree_leaf_or_not : forall (l : rbtree Z), rb_leaf l \/ ~(rb_leaf l).
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
  Parameter bool_gen : unit -> Prop.
  Parameter int_gen : unit -> Z.
  Parameter sizecheck : Z -> Prop.
  Parameter subs : Z -> Z.

  Lemma rbtree_positive_num_black_is_not_rb_leaf : forall (l : rbtree Z), forall (n : Z), (num_black l n /\ n > 0) -> ~rb_leaf l. Admitted.
  Lemma rbtree_no_rb_leaf_exists_ch : forall (l : rbtree Z), exists (l1 : rbtree Z), exists (l2 : rbtree Z), ~rb_leaf l -> (rb_lch l l1 /\ rb_rch l l2). Admitted.
  Lemma rbtree_no_rb_leaf_exists_rb_root : forall (l : rbtree Z), exists (x : Z), ~rb_leaf l -> rb_root l x. Admitted.
  Lemma rbtree_no_rb_leaf_exists_rb_root_color : forall (l : rbtree Z), exists (x : bool), ~rb_leaf l -> rb_root_color l x. Admitted.
  Lemma no_red_red_lt : forall (v : rbtree Z), forall (lt : rbtree Z), (no_red_red v /\ rb_lch v lt) -> no_red_red lt. Admitted.
  Lemma no_red_red_rt : forall (v : rbtree Z), forall (rt : rbtree Z), (no_red_red v /\ rb_rch v rt) -> no_red_red rt. Admitted.
  Lemma num_black_root_red_lt_same : forall (v : rbtree Z), forall (lt : rbtree Z), forall (h : Z), (rb_root_color v true /\ (num_black v h /\ rb_lch v lt)) -> num_black lt h. Admitted.
  Lemma num_black_root_red_rt_same : forall (v : rbtree Z), forall (rt : rbtree Z), forall (h : Z), (rb_root_color v true /\ (num_black v h /\ rb_rch v rt)) -> num_black rt h. Admitted.
  Lemma num_black_root_black_lt_minus_1 : forall (v : rbtree Z), forall (lt : rbtree Z), forall (h : Z), (rb_root_color v false /\ (num_black v h /\ rb_lch v lt)) -> num_black lt (h - 1). Admitted.
  Lemma num_black_root_black_rt_minus_1 : forall (v : rbtree Z), forall (rt : rbtree Z), forall (h : Z), (rb_root_color v false /\ (num_black v h /\ rb_rch v rt)) -> num_black rt (h - 1). Admitted.
  Lemma black_lt_black_num_black_gt_1 : forall (v : rbtree Z), forall (lt : rbtree Z), forall (h : Z), (num_black v h /\ (rb_lch v lt /\ (rb_root_color v false /\ rb_root_color lt false))) -> h > 1. Admitted.
  Lemma black_rt_black_num_black_gt_1 : forall (v : rbtree Z), forall (rt : rbtree Z), forall (h : Z), (num_black v h /\ (rb_rch v rt /\ (rb_root_color v false /\ rb_root_color rt false))) -> h > 1. Admitted.
  Lemma no_red_red_root_red_lt_not_red : forall (v : rbtree Z), forall (lt : rbtree Z), (no_red_red v /\ (rb_lch v lt /\ rb_root_color v true)) -> ~rb_root_color lt true. Admitted.
  Lemma no_red_red_root_red_rt_not_red : forall (v : rbtree Z), forall (rt : rbtree Z), (no_red_red v /\ (rb_rch v rt /\ rb_root_color v true)) -> ~rb_root_color rt true. Admitted.
  Lemma rbtree_num_black_geq_0 : forall (l : rbtree Z) (n : Z), (num_black l n) -> (n >= 0).
  Proof.
    induction l; intros n Hnb; simpl in Hnb.
    - lia.
    - destruct b; intuition. apply IHl1 in H. lia.
  Qed.
  Lemma rbtree_num_black_0_rb_leaf : forall (l : rbtree Z), (num_black l 0 /\ ~(rb_root_color l true)) -> (rb_leaf l).
  Proof.
    intros [] [Hnb Hrr].
    - reflexivity.
    - simpl in Hnb. simpl in Hrr. destruct b.
      * intuition.
      * intuition. apply rbtree_num_black_geq_0 in H. contradiction.
  Qed.

  Lemma rbtree_leaf_or_not : forall (l : rbtree Z), rb_leaf l \/ ~(rb_leaf l).
  Proof.
    intros [].
    - left. reflexivity.
    - right. auto.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (inv : Z), inv >= 0 -> ((forall (h_17 : Z), (h_17 >= 0 /\ (True -> (h_17 + h_17) = inv) /\ (False -> ((h_17 + h_17) + 1) = inv)) -> (forall (v : rbtree Z), (num_black v h_17 /\ no_red_red v /\ (True -> ~rb_root_color v true) /\ (False -> (h_17 = 0 -> ~rb_root_color v false))) -> ((~h_17 = 0 <-> h_17 > 0) /\ ((h_17 = 0 /\ rb_leaf v) \/ (~h_17 = 0 /\ (exists (lt2 : rbtree Z), (h_17 - 1) >= 0 /\ (False -> ((h_17 - 1) + (h_17 - 1)) = (inv - 1)) /\ (True -> (((h_17 - 1) + (h_17 - 1)) + 1) = (inv - 1)) /\ (inv - 1) < inv /\ (inv - 1) >= 0 /\ num_black lt2 (h_17 - 1) /\ no_red_red lt2 /\ (False -> ~rb_root_color lt2 true) /\ (True -> ((h_17 - 1) = 0 -> ~rb_root_color lt2 false)) /\ (exists (rt2 : rbtree Z), (h_17 - 1) >= 0 /\ (False -> ((h_17 - 1) + (h_17 - 1)) = (inv - 1)) /\ (True -> (((h_17 - 1) + (h_17 - 1)) + 1) = (inv - 1)) /\ (inv - 1) < inv /\ (inv - 1) >= 0 /\ num_black rt2 (h_17 - 1) /\ no_red_red rt2 /\ (False -> ~rb_root_color rt2 true) /\ (True -> ((h_17 - 1) = 0 -> ~rb_root_color rt2 false)) /\ (exists (_x_44 : Z), rb_root_color v false /\ rb_root v _x_44 /\ rb_lch v lt2 /\ rb_rch v rt2)))))))) /\ (forall (h_18 : Z), (h_18 >= 0 /\ (False -> (h_18 + h_18) = inv) /\ (True -> ((h_18 + h_18) + 1) = inv)) -> (forall (v_0 : rbtree Z), (num_black v_0 h_18 /\ no_red_red v_0 /\ (False -> ~rb_root_color v_0 true) /\ (True -> (h_18 = 0 -> ~rb_root_color v_0 false))) -> ((~h_18 = 0 <-> h_18 > 0) /\ ((h_18 = 0 /\ (rb_leaf v_0 \/ (exists (_x_47 : rbtree Z), rb_leaf _x_47 /\ (exists (_x_48 : Z), exists (_x_49 : rbtree Z), rb_leaf _x_49 /\ rb_root_color v_0 true /\ rb_root v_0 _x_48 /\ rb_lch v_0 _x_49 /\ rb_rch v_0 _x_47)))) \/ (~h_18 = 0 /\ ((exists (lt3_2 : rbtree Z), h_18 >= 0 /\ (True -> (h_18 + h_18) = (inv - 1)) /\ (False -> ((h_18 + h_18) + 1) = (inv - 1)) /\ (inv - 1) < inv /\ (inv - 1) >= 0 /\ num_black lt3_2 h_18 /\ no_red_red lt3_2 /\ (True -> ~rb_root_color lt3_2 true) /\ (False -> (h_18 = 0 -> ~rb_root_color lt3_2 false)) /\ (exists (rt3_2 : rbtree Z), h_18 >= 0 /\ (True -> (h_18 + h_18) = (inv - 1)) /\ (False -> ((h_18 + h_18) + 1) = (inv - 1)) /\ (inv - 1) < inv /\ (inv - 1) >= 0 /\ num_black rt3_2 h_18 /\ no_red_red rt3_2 /\ (True -> ~rb_root_color rt3_2 true) /\ (False -> (h_18 = 0 -> ~rb_root_color rt3_2 false)) /\ (exists (_x_51 : Z), rb_root_color v_0 true /\ rb_root v_0 _x_51 /\ rb_lch v_0 lt3_2 /\ rb_rch v_0 rt3_2))) \/ (exists (lt4_2 : rbtree Z), (h_18 - 1) >= 0 /\ (False -> ((h_18 - 1) + (h_18 - 1)) = ((inv - 1) - 1)) /\ (True -> (((h_18 - 1) + (h_18 - 1)) + 1) = ((inv - 1) - 1)) /\ ((inv - 1) - 1) < inv /\ ((inv - 1) - 1) >= 0 /\ num_black lt4_2 (h_18 - 1) /\ no_red_red lt4_2 /\ (False -> ~rb_root_color lt4_2 true) /\ (True -> ((h_18 - 1) = 0 -> ~rb_root_color lt4_2 false)) /\ (exists (rt4_2 : rbtree Z), (h_18 - 1) >= 0 /\ (False -> ((h_18 - 1) + (h_18 - 1)) = ((inv - 1) - 1)) /\ (True -> (((h_18 - 1) + (h_18 - 1)) + 1) = ((inv - 1) - 1)) /\ ((inv - 1) - 1) < inv /\ ((inv - 1) - 1) >= 0 /\ num_black rt4_2 (h_18 - 1) /\ no_red_red rt4_2 /\ (False -> ~rb_root_color rt4_2 true) /\ (True -> ((h_18 - 1) = 0 -> ~rb_root_color rt4_2 false)) /\ (exists (_x_52 : Z), rb_root_color v_0 false /\ rb_root v_0 _x_52 /\ rb_lch v_0 lt4_2 /\ rb_rch v_0 rt4_2)))))))))).
  Proof.
    intros inv Hinv. split.
    - intros h [Hh [Ht Hf]] v [Hnb [Hrr [Ht1 Hf1]]]. intuition.
      destruct (h =? 0) eqn:Heq.
      * left. assert (h = 0) by lia. intuition. subst.
        apply rbtree_num_black_0_rb_leaf. intuition.
      * right. assert (h > 0) by lia.
        assert (~rb_leaf v) by (apply (rbtree_positive_num_black_is_not_rb_leaf v h); intuition).
        destruct (rbtree_no_rb_leaf_exists_rb_root v) as [x Hrt].
        destruct (rbtree_no_rb_leaf_exists_rb_root_color v) as [b Hb].
        destruct (rbtree_no_rb_leaf_exists_ch v) as [l [r Hch]].
        intuition.
        destruct b; try contradiction.
        exists l. intuition.
        + apply (num_black_root_black_lt_minus_1 v l). intuition.
        + apply (no_red_red_lt v l). intuition.
        + assert (h > 1) by (apply (black_lt_black_num_black_gt_1 v l); intuition). lia.
        + exists r. intuition.
          -- apply (num_black_root_black_rt_minus_1 v r). intuition.
          -- apply (no_red_red_rt v r). intuition.
          -- assert (h > 1) by (apply (black_rt_black_num_black_gt_1 v r); intuition). lia.
          -- exists x. intuition.
    - intros h [Hh [Hf Ht]] v [Hnb [Hrr [Hf1 Ht1]]]. intuition.
      destruct (h =? 0) eqn:Heq.
      * left. assert (h = 0) by lia.
        intuition. destruct (rbtree_leaf_or_not v). (* Not required by Z3? *)
        + left. assumption.
        + right.
          destruct (rbtree_no_rb_leaf_exists_rb_root v) as [x Hrt].
          destruct (rbtree_no_rb_leaf_exists_rb_root_color v) as [b Hb].
          destruct (rbtree_no_rb_leaf_exists_ch v) as [l [r Hch]].
          intuition. destruct b; try contradiction.
          exists r. subst. split.
          -- assert (~(rb_root_color r true)) by (apply (no_red_red_root_red_rt_not_red v r); intuition).
              assert (num_black r 0) by (apply (num_black_root_red_rt_same v r); intuition).
              apply rbtree_num_black_0_rb_leaf. intuition.
          -- exists x. exists l. intuition.
              assert (~(rb_root_color l true)) by (apply (no_red_red_root_red_lt_not_red v l); intuition).
              assert (num_black l 0) by (apply (num_black_root_red_lt_same v l); intuition).
              apply rbtree_num_black_0_rb_leaf. intuition.
      * right. assert (h > 0) by lia.
        assert (~rb_leaf v) by (apply (rbtree_positive_num_black_is_not_rb_leaf v h); intuition).
        destruct (rbtree_no_rb_leaf_exists_rb_root v) as [x Hrt].
        destruct (rbtree_no_rb_leaf_exists_rb_root_color v) as [b Hb].
        destruct (rbtree_no_rb_leaf_exists_ch v) as [l [r Hch]].
        intuition.
        destruct b.
        + left. exists l. intuition.
          -- apply (num_black_root_red_lt_same v l). intuition.
          -- apply (no_red_red_lt v l). intuition.
          -- apply (no_red_red_root_red_lt_not_red v l); intuition.
          -- exists r. intuition.
              ** apply (num_black_root_red_rt_same v r). intuition.
              ** apply (no_red_red_rt v r). intuition.
              ** apply (no_red_red_root_red_rt_not_red v r); intuition.
              ** exists x. intuition.
        + right. exists l. intuition.
          -- apply (num_black_root_black_lt_minus_1 v l). intuition.
          -- apply (no_red_red_lt v l). intuition.
          -- assert (h > 1) by (apply (black_lt_black_num_black_gt_1 v l); intuition). lia.
          -- exists r. intuition.
              ** apply (num_black_root_black_rt_minus_1 v r). intuition.
              ** apply (no_red_red_rt v r). intuition.
              ** assert (h > 1) by (apply (black_rt_black_num_black_gt_1 v r); intuition). lia.
              ** exists x. intuition.
  Qed.
End Goal.
