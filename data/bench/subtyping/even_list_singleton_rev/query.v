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

  Axiom list_no_emp_exists_tl : forall (l : list Z), exists (l1 : list Z), ~emp l -> tl l l1.
  Axiom list_no_emp_exists_hd : forall (l : list Z), exists (x : Z), ~emp l -> hd l x.
  Axiom list_positive_len_is_not_emp : forall (l : list Z), forall (n : Z), (len l n /\ n > 0) -> ~emp l.
  Axiom list_len_geq_0 : forall (l : list Z), forall (n : Z), len l n -> n >= 0.
  Axiom list_tl_len_plus_1 : forall (l : list Z), forall (l1 : list Z), forall (n : Z), tl l l1 -> (len l1 n <-> len l (n + 1)).
  Axiom list_len_0_emp_iff : forall (l : list Z), emp l <-> len l 0.
  Axiom list_is_even_destruct : forall (l : list Z) (l1 : list Z) (x : Z), exists (x2 : Z), (tl l l1 /\ hd l x /\ all_evens l) -> (all_evens l1 /\ x2 * 2 = x).
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

  Lemma list_no_emp_exists_tl : forall (l : list Z), exists (l1 : list Z), ~emp l -> tl l l1.
  Proof.
    intros [| x xs].
    - exists nil. intros []. reflexivity.
    - exists xs. intros H. simpl. reflexivity.
  Qed.
  Lemma list_no_emp_exists_hd : forall (l : list Z), exists (x : Z), ~emp l -> hd l x.
  Proof.
    intros [| x'].
    - exists 1. intros []. reflexivity.
    - exists x'. intros H. simpl. reflexivity.
  Qed.
  Lemma list_positive_len_is_not_emp : forall (l : list Z), forall (n : Z), len l n /\ n > 0 -> ~emp l.
  Proof.
    intros [| x] n [Hl Hn].
    - inversion Hl as [Hn']. rewrite Hn' in Hn. inversion Hn.
    - intros H. contradiction.
  Qed.
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
  Lemma list_len_0_emp_iff : forall (l : list Z), emp l <-> len l 0. Admitted.
  Lemma list_is_even_destruct : forall (l : list Z) (l1 : list Z) (x : Z), exists (x2 : Z),
    (tl l l1 /\ hd l x /\ all_evens l) -> (all_evens l1 /\ x2 * 2 = x).
  Proof.
    intros [] l1 x; exists (x / 2);
    intros [Ht [Hh Hev]].
    - contradiction.
    - simpl in Hev. destruct Hev as [[n Hn] Hev1].
      assert (z = 2 * n) by intuition. clear Hn.
      inversion Ht. inversion Hh. subst. intuition.
      replace (2 * n) with (n * 2) by lia.
      rewrite Zdiv.Z_div_mult; intuition.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (s : Z), 0 <= s -> (forall (v : list Z), (exists (n : Z), len v n /\ n <= (s + 1) /\ n > 0 /\ s = 0 /\ all_evens v) -> (s = 0 /\ (exists (x : Z), exists (x2 : Z), exists (l2 : list Z), hd v x /\ x = (x2 * 2) /\ tl v l2 /\ emp l2))).
  Proof.
    intros s Hs v [n H]. intuition.
    assert (len v n /\ n > 0) as Hq by intuition.
    apply list_positive_len_is_not_emp in Hq.
    destruct (list_no_emp_exists_hd v) as [x Hh].
    destruct (list_no_emp_exists_tl v) as [t Ht].
    destruct (list_is_even_destruct v t x) as [x2 Hex].
    exists x. exists x2. exists t.
    intuition.
    assert (n = 1) by lia. subst.
    destruct (list_tl_len_plus_1 v t 0 H5).
    replace (0 + 1) with 1 in H6 by lia.
    destruct (list_len_0_emp_iff t).
    intuition.
  Qed.
End Goal.
