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
  Parameter all_evens : list Z -> Prop.

  Axiom list_len_0_emp : forall (l : list Z), emp l -> len l 0.
  Axiom list_emp_all_even : forall (l : list Z), emp l -> all_evens l.
  Axiom list_len_geq_0 : forall (l : list Z), forall (n : Z), len l n -> n >= 0.
  Axiom list_tl_len_plus_1 : forall (l : list Z), forall (l1 : list Z), forall (n : Z), tl l l1 -> (len l1 n <-> len l (n + 1)).
  Axiom list_hd_even_all_evens : forall (l : list Z) (x : Z) (l1 : list Z), hd l x /\ (exists (n : Z), x = 2 * n) /\ tl l l1 /\ all_evens l1 -> all_evens l.
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
  Fixpoint all_evens (l : list Z) : Prop :=
    match l with
    | nil => True
    | cons x xs => (exists n, x = 2 * n) /\ all_evens xs
    end.

  Lemma list_len_0_emp : forall (l : list Z), emp l -> len l 0.
  Proof.
    intros [| x] H.
    - reflexivity.
    - contradiction.
  Qed.
  Lemma list_emp_all_even : forall (l : list Z), emp l -> all_evens l. Admitted.
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
  Lemma list_hd_even_all_evens : forall (l : list Z) (x : Z) (l1 : list Z),
    hd l x /\ (exists (n : Z), x = 2 * n) /\ tl l l1 /\ all_evens l1 -> all_evens l.
  Proof.
    intros [| x] x1 l1 [Hh [[n Hev] [Ht He]]].
    - reflexivity.
    - inversion Ht. rewrite H in He. simpl. intuition.
      inversion Hh. rewrite H0 in Hev.
      exists n. intuition.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (s : Z), 0 <= s -> (forall (v : list Z), (s = 0 /\ (exists (x : Z), exists (x2 : Z), exists (l2 : list Z), hd v x /\ x = (x2 * 2) /\ tl v l2 /\ emp l2)) -> (exists (n : Z), len v n /\ n <= (s + 1) /\ n > 0 /\ s = 0 /\ all_evens v)).
  Proof.
    intros s Hs v [Hse [x [x2 [l H]]]].
    intuition.
    exists 1.
    intuition.
    - apply list_len_0_emp in H3.
      destruct (list_tl_len_plus_1 _ _ 0 H1).
      intuition.
    - eapply list_hd_even_all_evens. intuition.
      apply H0. exists x2. intuition.
      apply H1. apply (list_emp_all_even _ H3).
  Qed.
End Goal.
