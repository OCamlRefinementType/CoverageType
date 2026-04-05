From Stdlib Require Import BinInt.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.
From Stdlib Require Import Floats.
From Stdlib Require Import Lia.
Open Scope Z_scope.

Module Type Signatures.
Parameter tree : forall (a : Type), Type.

  Parameter len : forall {a : Type}, list a -> Z -> Prop.
  Parameter emp : forall {a : Type}, list a -> Prop.
  Parameter hd : forall {a : Type}, list a -> a -> Prop.
  Parameter tl : forall {a : Type}, list a -> list a -> Prop.
  Parameter list_mem : forall {a : Type}, list a -> a -> Prop.

  Axiom list_no_emp_exists_hd : forall (l : list Z), exists (x : Z), ~emp l -> hd l x.
  Axiom list_no_emp_exists_tl : forall (l : list Z), exists (l1 : list Z), ~emp l -> tl l l1.
  Axiom list_len_geq_0 : forall (l : list Z), forall (n : Z), len l n -> n >= 0.
  Axiom list_tl_len_plus_1 : forall (l : list Z), forall (l1 : list Z), forall (n : Z), tl l l1 -> (len l1 n <-> len l (n + 1)).
  Axiom list_hd_is_mem : forall (l : list Z) (u : Z), (hd l u) -> (list_mem l u).
  Axiom list_tl_mem : forall (l : list Z) (l1 : list Z) (u : Z), (tl l l1 /\ list_mem l1 u) -> (list_mem l u).
End Signatures.

Module Axioms : Signatures.
  Inductive tree' (a : Type) : Type :=
  | Leaf : tree' a
  | Node : a -> tree' a -> tree' a -> tree' a.
  Definition tree := tree'.

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

  Lemma list_no_emp_exists_hd : forall (l : list Z), exists (x : Z), ~emp l -> hd l x.
  Proof.
    intros [| x'].
    - exists 1. intros []. reflexivity.
    - exists x'. intros H. simpl. reflexivity.
  Qed.
  Lemma list_no_emp_exists_tl : forall (l : list Z), exists (l1 : list Z), ~emp l -> tl l l1.
  Proof.
    intros [| x xs].
    - exists nil. intros []. reflexivity.
    - exists xs. intros H. simpl. reflexivity.
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
  Lemma list_hd_is_mem : forall (l : list Z) (u : Z), (hd l u) -> (list_mem l u).
  Proof.
    intros [| x] u Hh.
    - contradiction.
    - inversion Hh. simpl. left. reflexivity.
  Qed.

  Lemma list_tl_mem : forall (l : list Z) (l1 : list Z) (u : Z), (tl l l1 /\ list_mem l1 u) -> (list_mem l u).
  Proof.
    intros [| x] [| y] u [Ht Hm]; try contradiction.
    inversion Ht. subst.
    simpl. simpl in Hm.
    right. assumption.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (s : Z), 0 <= s -> (forall (x : Z), forall (v : list Z), (s > 0 /\ ~emp v /\ len v s /\ (forall (u1 : Z), list_mem v u1 -> u1 = x)) -> (exists (_25 : list Z), s > 0 /\ (s - 1) >= 0 /\ (s - 1) < s /\ len _25 (s - 1) /\ (forall (u2 : Z), list_mem _25 u2 -> u2 = x) /\ hd v x /\ tl v _25)).
  Proof.
    intros s Hs x v [Hs1 [Hne [Hl H]]].
    destruct (list_no_emp_exists_hd v) as [x' Hh'].
    destruct (list_no_emp_exists_tl v) as [t Ht].
    exists t. intuition.
    - destruct (list_tl_len_plus_1 v t (s - 1) H1).
      replace (s - 1 + 1) with s in H3 by intuition.
      intuition.
    - assert (list_mem v u2) as Hu2 by (apply (list_tl_mem v t u2); intuition).
      apply (H u2 Hu2).
    - set (Hm := (list_hd_is_mem _ _ H0)).
      apply H in Hm. subst.
      assumption.
  Qed.
End Goal.
