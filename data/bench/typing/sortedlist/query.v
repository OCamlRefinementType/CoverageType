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
  Parameter int_gen : unit -> Z.
  Parameter sizecheck : Z -> Prop.
  Parameter subs : Z -> Z.

  Axiom list_positive_len_is_not_emp : forall (l : list Z), forall (n : Z), (len l n /\ n > 0) -> ~emp l.
  Axiom list_len_0_emp_iff : forall (l : list Z), emp l <-> len l 0.
  Axiom list_len_geq_0 : forall (l : list Z), forall (n : Z), len l n -> n >= 0.
  Axiom list_tl_len_plus_1 : forall (l : list Z), forall (l1 : list Z), forall (n : Z), tl l l1 -> (len l1 n <-> len l (n + 1)).
  Axiom list_no_emp_exists_hd : forall (l : list Z), exists (x : Z), ~emp l -> hd l x.
  Axiom list_no_emp_exists_tl : forall (l : list Z), exists (l1 : list Z), ~emp l -> tl l l1.
  Axiom list_tl_sorted : forall (l : list Z) (l1 : list Z), tl l l1 /\ sorted l -> sorted l1.
  Axiom list_hd_sorted : forall (l : list Z) (l1 : list Z) (x : Z) (y : Z), (tl l l1 /\ sorted l) -> (emp l1 \/ ((hd l1 y /\ hd l x) -> (x <= y))).
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
  Parameter int_gen : unit -> Z.
  Parameter sizecheck : Z -> Prop.
  Parameter subs : Z -> Z.

  Lemma list_positive_len_is_not_emp : forall (l : list Z), forall (n : Z), len l n /\ n > 0 -> ~emp l.
  Proof.
    intros [| x] n [Hl Hn].
    - inversion Hl as [Hn']. rewrite Hn' in Hn. inversion Hn.
    - intros H. contradiction.
  Qed.
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
  Lemma list_tl_sorted : forall (l : list Z) (l1 : list Z), tl l l1 /\ sorted l -> sorted l1.
  Proof.
    intros [| x] [| y] [Ht Hs];
    try contradiction.
    - reflexivity.
    - inversion Ht. subst. simpl in Hs. destruct l0.
      * reflexivity.
      * simpl. intuition.
  Qed.

  Lemma list_hd_sorted : forall (l : list Z) (l1 : list Z) (x : Z) (y : Z),
    (tl l l1 /\ sorted l) -> (emp l1 \/ ((hd l1 y /\ hd l x) -> (x <= y))).
  Proof.
    intros [| x] [| y] x1 y1 [Ht Hs]; try contradiction.
    - left. reflexivity.
    - right. intros [Hh1 Hh2].
      inversion Ht. inversion Hh1. inversion Hh2.
      subst. simpl in Hs.
      intuition.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (s : Z), 0 <= s -> (forall (x : Z), forall (v : list Z), (len v s /\ sorted v /\ (~emp v -> (exists (u : Z), hd v u /\ x <= u))) -> ((~s = 0 <-> s > 0) /\ ((s = 0 /\ emp v) \/ (~s = 0 /\ (exists (y : Z), x <= y /\ (exists (l : list Z), (s - 1) < s /\ 0 <= (s - 1) /\ len l (s - 1) /\ sorted l /\ (~emp l -> (exists (u_0 : Z), hd l u_0 /\ y <= u_0)) /\ hd v y /\ tl v l)))))).
  Proof.
    intros s Hs x v [Hl [Hso He]].
    intuition.
    destruct (s =? 0) eqn:Hseq.
    - left.
      assert (s = 0) by lia. subst.
      destruct (list_len_0_emp_iff v).
      intuition.
    - right. assert (s > 0) by lia.
      split; try lia.
      assert (~emp v) by (apply (list_positive_len_is_not_emp v s); intuition).
      destruct (list_no_emp_exists_tl v) as [t Ht].
      intuition.
      destruct H1 as [u [Hh Hul]].
      exists u. split; try assumption. exists t.
      intuition.
      * apply (list_tl_len_plus_1 v t (s - 1) H2).
        replace (s - 1 + 1) with s by lia.
        assumption.
      * apply (list_tl_sorted v t). intuition.
      * destruct (list_no_emp_exists_hd t) as [u1 Hu1].
        exists u1. intuition.
        destruct (list_hd_sorted v t u u1).
        + intuition.
        + contradiction.
        + intuition.
  Qed.
End Goal.
