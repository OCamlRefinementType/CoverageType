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
  Parameter all_evens : list Z -> Prop.
  Parameter bool_gen : unit -> Prop.
  Parameter int_gen : unit -> Z.
  Parameter sizecheck : Z -> Prop.
  Parameter double : Z -> Z.
  Parameter subs : Z -> Z.

  Axiom list_positive_len_is_not_emp : forall (l : list Z), forall (n : Z), (len l n /\ n > 0) -> ~emp l.
  Axiom list_len_geq_0 : forall (l : list Z), forall (n : Z), len l n -> n >= 0.
  Axiom list_no_emp_exists_hd : forall (l : list Z), exists (x : Z), ~emp l -> hd l x.
  Axiom list_no_emp_exists_tl : forall (l : list Z), exists (l1 : list Z), ~emp l -> tl l l1.
  Axiom list_tl_len_plus_1 : forall (l : list Z), forall (l1 : list Z), forall (n : Z), tl l l1 -> (len l1 n <-> len l (n + 1)).
  Axiom list_len_0_emp_iff : forall (l : list Z), emp l <-> len l 0.
  Axiom list_is_even_destruct : forall (l : list Z) (l1 : list Z) (x : Z), exists (x2 : Z), (tl l l1 /\ hd l x /\ all_evens l) -> (all_evens l1 /\ x2 * 2 = x).
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
  Fixpoint all_evens (l : list Z) : Prop :=
    match l with
    | nil => True
    | cons x xs => (exists n, x = 2 * n) /\ all_evens xs
    end.
  Parameter bool_gen : unit -> Prop.
  Parameter int_gen : unit -> Z.
  Parameter sizecheck : Z -> Prop.
  Parameter double : Z -> Z.
  Parameter subs : Z -> Z.

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
  Lemma list_len_0_emp_iff : forall (l : list Z), emp l <-> len l 0.
  Proof.
  intros [| x]; split.
    - reflexivity.
    - reflexivity.
    - contradiction.
    - simpl. intuition.
  Qed.

  Lemma list_is_even_destruct : forall (l : list Z) (l1 : list Z) (x : Z), exists (x2 : Z),
    (tl l l1 /\ hd l x /\ all_evens l) -> (all_evens l1 /\ x2 * 2 = x).
  Proof.
    intros [| n] l1 x.
    - exists 0. intros [Ht [Hh Hev]]. contradiction.
    - exists (n / 2). intros [Ht [Hh Hev]].
      inversion Hev as [[n' Hd] Hev'].
      inversion Ht. inversion Hh. subst.
      split; try assumption.
      replace (2 * n') with (n' * 2) by intuition.
      rewrite Zdiv.Z_div_mult; intuition.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (s : Z), 0 <= s -> (forall (v : list Z), (exists (n : Z), len v n /\ n <= (s + 1) /\ n > 0 /\ all_evens v) -> ((~s = 0 <-> s > 0) /\ ((s = 0 /\ (exists (_x_0 : list Z), emp _x_0 /\ (exists (_x_1 : Z), hd v (_x_1 * 2) /\ tl v _x_0))) \/ (~s = 0 /\ ((exists (_x_11 : list Z), emp _x_11 /\ (exists (_x_12 : Z), hd v (_x_12 * 2) /\ tl v _x_11)) \/ (exists (_x_17 : list Z), (s - 1) < s /\ 0 <= (s - 1) /\ (exists (n_5 : Z), len _x_17 n_5 /\ n_5 <= ((s - 1) + 1) /\ n_5 > 0 /\ all_evens _x_17) /\ (exists (_x_18 : Z), hd v (_x_18 * 2) /\ tl v _x_17))))))).
  Proof.
    intros s Hs v [n [Hl [Hnl [Hng Hev]]]].
    assert (len v n /\ n > 0) as Hp by intuition.
    remember (list_positive_len_is_not_emp v n Hp) as Hne.
    destruct (list_no_emp_exists_hd v) as [x Hh].
    destruct (list_no_emp_exists_tl v) as [t Ht].
    destruct (list_is_even_destruct v t x) as [x' Hx'].
    intuition. subst.
    destruct (s =? 0) eqn:Hse.
    - left. intuition. exists t.
      assert (n = 1) by intuition. subst. split.
      * destruct (list_tl_len_plus_1 v t 0 H0).
        replace (0 + 1) with 1 in H5 by intuition.
        destruct (list_len_0_emp_iff t).
        intuition.
      * exists x'. intuition.
    - right. intuition. destruct (n =? 1) eqn:Hne.
      * left. exists t.
        assert (n = 1) by intuition. subst. split.
        + destruct (list_tl_len_plus_1 v t 0 H0).
          replace (0 + 1) with 1 in H5 by intuition.
          destruct (list_len_0_emp_iff t).
          intuition.
        + exists x'. intuition.
      * right. exists t. intuition.
        + exists (n - 1).
          destruct (list_tl_len_plus_1 v t (n - 1) H0).
          replace (n - 1 + 1) with n in H5 by intuition.
          intuition.
        + exists x'. intuition.
  Qed.
End Goal.
