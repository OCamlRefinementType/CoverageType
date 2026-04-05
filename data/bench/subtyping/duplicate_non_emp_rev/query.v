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

  Axiom list_len_geq_0 : forall (l : list Z), forall (n : Z), len l n -> n >= 0.
  Axiom list_tl_len_plus_1 : forall (l : list Z), forall (l1 : list Z), forall (n : Z), tl l l1 -> (len l1 n <-> len l (n + 1)).
  Axiom list_positive_len_is_not_emp : forall (l : list Z), forall (n : Z), (len l n /\ n > 0) -> ~emp l.
  Axiom list_cons_mem : forall (l : list Z) (l1 : list Z) (u : Z), (tl l l1 /\ list_mem l u) -> (list_mem l1 u \/ hd l u).
  Axiom list_hd_unique : forall (l : list Z) (x : Z) (y : Z), (hd l x /\ hd l y) -> x = y.
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
  Lemma list_hd_unique : forall (l : list Z) (x : Z) (y : Z), (hd l x /\ hd l y) -> x = y.
  Proof.
    intros [| h] x y [Hh1 Hh2].
    - contradiction.
    - inversion Hh1. inversion Hh2. reflexivity.
  Qed.

  Lemma list_cons_mem : forall (l : list Z) (l1 : list Z) (u : Z),
    (tl l l1 /\ list_mem l u) -> (list_mem l1 u \/ hd l u).
  Proof.
    intros [| x] [| y] u [Ht Hm]; try contradiction;
    inversion Ht; subst; simpl in Hm.
    - right. simpl. intuition.
    - destruct (u =? x) eqn:Hu.
      * right. simpl. intuition.
      * left. simpl. intuition.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (s : Z), 0 <= s -> (forall (x : Z), forall (v : list Z), (exists (s1 : Z), exists (l : list Z), s > 0 /\ s1 >= 0 /\ s1 < s /\ s1 = (s - 1) /\ len l s1 /\ (forall (u1 : Z), list_mem l u1 -> u1 = x) /\ hd v x /\ tl v l) -> (s > 0 /\ ~emp v /\ len v s /\ (forall (u2 : Z), list_mem v u2 -> u2 = x))).
  Proof.
    intros s Hs x v [s1 [t H]].
    decompose [and] H. subst.
    destruct (list_tl_len_plus_1 v t (s - 1) H8).
    replace (s - 1 + 1) with s in H3 by intuition.
    intuition.
    - apply (list_positive_len_is_not_emp v s) in H3; intuition.
    - assert (tl v t /\ list_mem v u2) as Hq by intuition.
      destruct (list_cons_mem v t u2 Hq).
      * apply (H5 _ H17).
      * apply (list_hd_unique v u2 x). intuition.
  Qed.
End Goal.
