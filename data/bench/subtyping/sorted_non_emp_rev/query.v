From Stdlib Require Import BinInt.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.
From Stdlib Require Import Floats.
From Stdlib Require Import Lia.
Open Scope Z_scope.

Module Type Signatures.
  Parameter tree : forall (a : Type), Type.
  Parameter rbtree : forall (a : Type), Type.

  Parameter len : forall {a : Type}, list a -> Z -> Prop.
  Parameter emp : forall {a : Type}, list a -> Prop.
  Parameter hd : forall {a : Type}, list a -> a -> Prop.
  Parameter tl : forall {a : Type}, list a -> list a -> Prop.
  Parameter list_mem : forall {a : Type}, list a -> a -> Prop.
  Parameter sorted : list Z -> Prop.

  Axiom list_len_geq_0 : forall (l : list Z), forall (n : Z), len l n -> n >= 0.
  Axiom list_tl_len_plus_1 : forall (l : list Z), forall (l1 : list Z), forall (n : Z), tl l l1 -> (len l1 n <-> len l (n + 1)).
  Axiom list_positive_len_is_not_emp : forall (l : list Z), forall (n : Z), (len l n /\ n > 0) -> ~emp l.
  Axiom list_single_sorted : forall (l : list Z), (len l 1) -> (sorted l).
  Axiom list_sorted_hd : forall (l : list Z) (l1 : list Z) (x : Z) (y : Z), (tl l l1 /\ sorted l1 /\ hd l y /\ hd l1 x /\ y <= x) -> (sorted l).
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

  Fixpoint len {a : Type} (l : list a) (n : Z) : Prop :=
    match l with
    | nil => n = 0
    | cons _ xs => n > 0 /\ len xs (n - 1)
    end.
  Definition emp {a : Type} (l : list a) : Prop :=
    match l with
    | nil => True
    | cons _ _ => False
    end.
  Definition hd {a : Type} (l : list a) (n : a) : Prop :=
    match l with
    | nil => False
    | cons n' _ => n = n'
    end.
  Definition tl {a : Type} (l : list a) (xs : list a) : Prop :=
    match l with
    | nil => False
    | cons _ xs' => xs = xs'
    end.
  Fixpoint list_mem {a : Type} (l : list a) (x : a) : Prop :=
    match l with
    | nil => False
    | cons x' xs => (x = x') \/ list_mem xs x
    end.
  Fixpoint sorted (l : list Z) : Prop :=
    match l with
    | nil => True
    | cons x nil => True
    | cons x xs =>
      match xs with
      | nil => True
      | cons y _ => x <= y /\ sorted xs
      end
    end.

  Lemma list_len_geq_0 : forall (l : list Z), forall (n : Z), len l n -> n >= 0.
  Proof.
    intros l.
    induction l; intros n H; inversion H.
    - intuition.
    - apply IHl in H1. intuition.
  Qed.
  Lemma list_tl_len_plus_1 : forall (l : list Z), forall (l1 : list Z), forall (n : Z), tl l l1 -> len l1 n <-> len l (n + 1).
  Proof.
    intros [| x] l1 n Ht; split;
    try contradiction;
    inversion Ht; intros Hl.
    - simpl. split.
      * apply list_len_geq_0 in Hl.
        intuition.
      * replace (n + 1 - 1) with n by intuition.
        assumption.
    - simpl in Hl. destruct Hl.
      replace (n + 1 - 1) with n in H1 by intuition.
      assumption.
  Qed.
  Lemma list_positive_len_is_not_emp : forall (l : list Z), forall (n : Z), len l n /\ n > 0 -> ~emp l.
  Proof.
    intros [| x] n [Hl Hn].
    - inversion Hl as [Hn']. rewrite Hn' in Hn. inversion Hn.
    - intros H. contradiction.
  Qed.
  Lemma list_single_sorted : forall (l : list Z), (len l 1) -> (sorted l).
  Proof.
    intros [| x []] Hl.
    - discriminate.
    - reflexivity.
    - simpl in Hl. destruct Hl. destruct H0. lia.
  Qed.

  Lemma list_sorted_hd : forall (l : list Z) (l1 : list Z) (x : Z) (y : Z),
    (tl l l1 /\ sorted l1 /\ hd l y /\ hd l1 x /\ y <= x) -> (sorted l).
  Proof.
    intros [| x] [| y] x1 y1 [Ht [Hst [Hh [Hth Hle]]]]; try contradiction.
    inversion Ht. inversion Hh. inversion Hth. subst.
    simpl. simpl in Hst.
    intuition.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (s : Z), 0 <= s -> (forall (x : Z), forall (v : list Z), (exists (y : Z), exists (s1 : Z), exists (l : list Z), s > 0 /\ x <= y /\ 0 <= s1 /\ s1 < s /\ s1 = (s - 1) /\ len l s1 /\ sorted l /\ hd v y /\ tl v l /\ (~emp l -> (exists (u2 : Z), hd l u2 /\ y <= u2))) -> (~emp v /\ len v s /\ sorted v /\ (~emp v -> (exists (u1 : Z), hd v u1 /\ x <= u1)))).
  Proof.
    intros s Hs x v [y [s1 [l H]]].
    decompose [and] H. subst.
    destruct (list_tl_len_plus_1 v l (s - 1) H8).
    replace (s - 1 + 1) with s in * by lia.
    assert (~emp v) by (apply (list_positive_len_is_not_emp v s); intuition).
    intuition.
    - destruct (s =? 1) eqn:Hseq.
      * replace s with 1 in * by lia.
        apply list_single_sorted. assumption.
      * assert (s - 1 > 0) by lia.
        assert (~emp l) by (apply (list_positive_len_is_not_emp l (s - 1)); intuition).
        intuition.
        destruct H10 as [u2 [Hsh Hlu]].
        apply (list_sorted_hd v l u2 y).
        intuition.
    - exists y. intuition.
  Qed.
End Goal.
