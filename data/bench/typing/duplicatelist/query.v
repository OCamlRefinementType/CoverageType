From Stdlib Require Import BinInt.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.
From Stdlib Require Import Floats.
Open Scope Z_scope.

Module Type Signatures.
Parameter tree : forall (a : Type), Type.

  Parameter len : forall {a : Type}, list a -> Z -> Prop.
  Parameter emp : forall {a : Type}, list a -> Prop.
  Parameter hd : forall {a : Type}, list a -> a -> Prop.
  Parameter tl : forall {a : Type}, list a -> list a -> Prop.
  Parameter list_mem : forall {a : Type}, list a -> a -> Prop.
  Parameter sizecheck : Z -> Prop.
  Parameter subs : Z -> Z.

  Axiom list_len_0_emp_iff : forall (l : list Z), emp l <-> len l 0.
  Axiom list_len_geq_0 : forall (l : list Z), forall (n : Z), len l n -> n >= 0.
  Axiom list_tl_len_plus_1 : forall (l : list Z), forall (l1 : list Z), forall (n : Z), tl l l1 -> (len l1 n <-> len l (n + 1)).
  Axiom list_no_emp_exists_hd : forall (l : list Z), exists (x : Z), ~emp l -> hd l x.
  Axiom list_no_emp_exists_tl : forall (l : list Z), exists (l1 : list Z), ~emp l -> tl l l1.
  Axiom list_positive_len_is_not_emp : forall (l : list Z), forall (n : Z), (len l n /\ n > 0) -> ~emp l.
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
  Parameter sizecheck : Z -> Prop.
  Parameter subs : Z -> Z.

  Lemma list_len_0_emp_iff : forall (l : list Z), emp l <-> len l 0. Admitted.
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
  Lemma list_positive_len_is_not_emp : forall (l : list Z), forall (n : Z), len l n /\ n > 0 -> ~emp l.
  Proof.
    intros [| x] n [Hl Hn].
    - inversion Hl as [Hn']. rewrite Hn' in Hn. inversion Hn.
    - intros H. contradiction.
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

  Theorem goal : forall (s : Z), s >= 0 -> (forall (x : Z), forall (v : list Z), (len v s /\ (forall (u : Z), list_mem v u -> u = x)) -> ((~s = 0 <-> s > 0) /\ ((s = 0 /\ emp v) \/ (~s = 0 /\ (exists (_x_2 : list Z), (s - 1) < s /\ (s - 1) >= 0 /\ len _x_2 (s - 1) /\ (forall (u_0 : Z), list_mem _x_2 u_0 -> u_0 = x) /\ hd v x /\ tl v _x_2))))).
  Proof.
    intros s Hs x v [Hl Hdup].
    intuition.
    destruct (s =? 0) eqn:Hse.
    - left. assert (s = 0) by intuition.
      split; try assumption.
      subst.
      destruct (list_len_0_emp_iff v). intuition.
    - right. assert (s > 0) by intuition.
      assert (len v s /\ s > 0) as Hq by intuition.
      remember (list_positive_len_is_not_emp v s Hq) as Hne.
      destruct (list_no_emp_exists_hd v) as [x' Hh].
      destruct (list_no_emp_exists_tl v) as [t Ht].
      intuition.
      exists t. intuition.
      * destruct (list_tl_len_plus_1 v t (s - 1) H1).
        replace (s - 1 + 1) with s in H3 by intuition.
        intuition.
      * assert (list_mem v u_0) as Hu0 by (apply (list_tl_mem v t u_0); intuition).
        apply (Hdup u_0 Hu0).
      * set (Hm := (list_hd_is_mem _ _ H0)).
        apply Hdup in Hm. subst.
        assumption.
  Qed.
End Goal.
