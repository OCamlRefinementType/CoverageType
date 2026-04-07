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
  Parameter uniq : forall {a : Type}, list a -> Prop.

  Axiom list_hd_no_emp : forall (l : list Z), forall (x : Z), hd l x -> ~emp l.
  Axiom list_len_geq_0 : forall (l : list Z), forall (n : Z), len l n -> n >= 0.
  Axiom list_tl_len_plus_1 : forall (l : list Z) (l1 : list Z) (n : Z), tl l l1 -> (len l1 n <-> len l (n + 1)).
  Axiom list_tl_unique_parent : forall (l : list Z) (l1 : list Z) (n : Z), uniq l1 /\ tl l l1 /\ hd l n /\ ~(list_mem l1 n) -> uniq l.
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
  Fixpoint uniq {a : Type} (l : list a) : Prop :=
    match l with
    | nil => True
    | cons x xs => ~(list_mem xs x) /\ uniq xs
    end.

  Lemma list_hd_no_emp : forall (l : list Z), forall (x : Z), hd l x -> ~emp l.
  Proof.
    intros [| x'] x H.
    - contradiction.
    - intros []. 
  Qed.
  Lemma list_len_geq_0 : forall (l : list Z), forall (n : Z), len l n -> n >= 0.
  Proof.
    intros l.
    induction l; intros n H; inversion H.
    - intuition.
    - apply IHl in H1. intuition.
  Qed.
  Lemma list_tl_len_plus_1 : forall (l : list Z) (l1 : list Z) (n : Z),
    tl l l1 -> (len l1 n <-> len l (n + 1)).
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

  Lemma list_tl_unique_parent : forall (l : list Z) (l1 : list Z) (n : Z),
    uniq l1 /\ tl l l1 /\ hd l n /\ ~(list_mem l1 n) -> uniq l.
  Proof.
    intros [| x] l1 n [Htu [Ht [Hh Hm]]].
    - contradiction.
    - simpl. inversion Ht. subst. split.
      * inversion Hh. subst. assumption.
      * assumption.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (s : Z), 0 <= s -> (forall (v : list Z), (exists (x2 : Z), exists (l2 : list Z), s > 0 /\ (s - 1) >= 0 /\ (s - 1) < s /\ len l2 (s - 1) /\ uniq l2 /\ ~list_mem l2 x2 /\ hd v x2 /\ tl v l2) -> (exists (x1 : Z), exists (s1 : Z), exists (l1 : list Z), s > 0 /\ s1 >= 0 /\ s1 < s /\ s1 = (s - 1) /\ len l1 s1 /\ uniq l1 /\ ~list_mem l1 x1 /\ ~emp v /\ len v s /\ uniq v)).
  Proof.
    intros s Hs v [x [l H]].
    intuition.
    exists x. exists (s - 1). exists l.
    intuition.
    - apply (list_hd_no_emp _ _ H5) in H6. contradiction.
    - destruct (list_tl_len_plus_1 _ _ (s - 1) H7).
      replace (s - 1 + 1) with s in H6 by intuition.
      apply (H6 H2).
    - eapply list_tl_unique_parent.
      intuition. apply H3. apply H7. apply H5. intuition.
  Qed.
End Goal.
