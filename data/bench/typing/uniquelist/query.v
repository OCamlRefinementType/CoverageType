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
  Parameter uniq : forall {a : Type}, list a -> Prop.
  Parameter int_gen : unit -> Z.
  Parameter sizecheck : Z -> Prop.
  Parameter subs : Z -> Z.

  Axiom list_len_geq_0 : forall (l : list Z), forall (n : Z), len l n -> n >= 0.
  Axiom list_len_0_emp_iff : forall (l : list Z), emp l <-> len l 0.
  Axiom list_tl_len_plus_1 : forall (l : list Z) (l1 : list Z) (n : Z), tl l l1 -> (len l1 n <-> len l (n + 1)).
  Axiom list_no_emp_exists_hd : forall (l : list Z), exists (x : Z), ~emp l -> hd l x.
  Axiom list_no_emp_exists_tl : forall (l : list Z), exists (l1 : list Z), ~emp l -> tl l l1.
  Axiom list_positive_len_is_not_emp : forall (l : list Z), forall (n : Z), len l n /\ n > 0 -> ~emp l.
  Axiom list_tl_unique : forall (l : list Z) (l1 : list Z), tl l l1 /\ uniq l -> uniq l1.
  Axiom list_hd_unique : forall (l : list Z) (l1 : list Z) (x : Z), tl l l1 /\ uniq l /\ hd l x -> ~ (list_mem l1 x).
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
  Fixpoint uniq {a : Type} (l : list a) : Prop :=
    match l with
    | nil => True
    | cons x xs => ~(list_mem xs x) /\ uniq xs
    end.
  Parameter int_gen : unit -> Z.
  Parameter sizecheck : Z -> Prop.
  Parameter subs : Z -> Z.

  Lemma list_len_geq_0 : forall (l : list Z), forall (n : Z), len l n -> n >= 0.
  Proof.
    intros l.
    induction l; intros n H; inversion H.
    - intuition.
    - apply IHl in H1. intuition.
  Qed.
  Lemma list_len_0_emp_iff : forall (l : list Z), emp l <-> len l 0. Admitted.
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

  Lemma list_tl_unique : forall (l : list Z) (l1 : list Z), tl l l1 /\ uniq l -> uniq l1.
  Proof.
    intros [| x] l1 [Ht Hu].
    - contradiction.
    - simpl in Hu. destruct Hu.
      inversion Ht. assumption.
  Qed.

  Lemma list_hd_unique : forall (l : list Z) (l1 : list Z) (x : Z),
    tl l l1 /\ uniq l /\ hd l x -> ~ (list_mem l1 x).
  Proof.
    intros [| x] l1 x1 [Ht [Hu Hh]].
    - contradiction.
    - simpl in Hu. destruct Hu as [Htm Htu].
      inversion Hh. inversion Ht.
      assumption.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (s : Z), s >= 0 -> (forall (v : list Z), (len v s /\ uniq v) -> ((~s = 0 <-> s > 0) /\ ((s = 0 /\ emp v) \/ (~s = 0 /\ (exists (l : list Z), (s - 1) < s /\ (s - 1) >= 0 /\ len l (s - 1) /\ uniq l /\ (exists (x : Z), ~list_mem l x /\ hd v x /\ tl v l)))))).
  Proof.
    intros s Hs v [Hl Hu].
    intuition.
    destruct (s =? 0) eqn:He.
    - left.
      replace s with 0 in * by intuition.
      destruct (list_len_0_emp_iff v).
      intuition.
    - right. intuition.
      assert (s > 0) by intuition.
      assert (~emp v) by (apply (list_positive_len_is_not_emp v s); intuition).
      destruct (list_no_emp_exists_tl v) as [t Ht].
      exists t. intuition.
      * destruct (list_tl_len_plus_1 v t (s - 1) H1).
        replace (s - 1 + 1) with s in H3 by intuition.
        intuition.
      * apply (list_tl_unique v t). intuition.
      * destruct (list_no_emp_exists_hd v) as [h Hh].
        exists h. split.
        apply (list_hd_unique v t). intuition.
        intuition.
  Qed.
End Goal.
