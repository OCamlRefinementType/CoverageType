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
  Parameter sorted : list Z -> Prop.

  Axiom list_no_emp_exists_hd : forall (l : list Z), exists (x : Z), ~emp l -> hd l x.
  Axiom list_no_emp_exists_tl : forall (l : list Z), exists (l1 : list Z), ~emp l -> tl l l1.
  Axiom list_len_geq_0 : forall (l : list Z), forall (n : Z), len l n -> n >= 0.
  Axiom list_tl_len_plus_1 : forall (l : list Z), forall (l1 : list Z), forall (n : Z), tl l l1 -> (len l1 n <-> len l (n + 1)).
  Axiom list_no_emp_pos_len : forall (l : list Z) (s : Z), ~ emp l /\ len l s -> s > 0.
  Axiom list_hd_sorted : forall (l : list Z) (l1 : list Z) (x : Z) (y : Z), tl l l1 /\ sorted l -> emp l1 \/ ((hd l1 y /\ hd l x) -> (x <= y)).
  Axiom list_tl_sorted : forall (l : list Z) (l1 : list Z), tl l l1 /\ sorted l -> sorted l1.
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
  Lemma list_no_emp_pos_len : forall (l : list Z) (s : Z), ~ emp l /\ len l s -> s > 0.
  Proof.
    intros [| x] s [He Hl].
    - simpl in He. contradiction.
    - inversion Hl. apply list_len_geq_0 in H0. intuition.
  Qed.

  Lemma list_hd_sorted : forall (l : list Z) (l1 : list Z) (x : Z) (y : Z),
    tl l l1 /\ sorted l -> emp l1 \/ ((hd l1 y /\ hd l x) -> (x <= y)).
  Proof.
    intros [| x1] [| y1] x y [Htl Hs]; try contradiction.
    - left. reflexivity.
    - right. intros [Hht Hhp].
      inversion Htl. inversion Hht. inversion Hhp.
      subst. simpl in Hs. intuition.
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
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (s : Z), 0 <= s -> (forall (x : Z), forall (v : list Z), (~emp v /\ len v s /\ sorted v /\ (~emp v -> (exists (u2 : Z), hd v u2 /\ x <= u2))) -> (exists (y : Z), exists (s1 : Z), exists (l : list Z), s > 0 /\ x <= y /\ 0 <= s1 /\ s1 < s /\ s1 = (s - 1) /\ len l s1 /\ sorted l /\ hd v y /\ tl v l /\ (~emp l -> (exists (u : Z), hd l u /\ y <= u)))).
  Proof.
    intros s Hs x v [He [Hl [Hsr [u [Hh Hle]]]]].
    assumption.
    destruct (list_no_emp_exists_tl v) as [v1 Htli].
    exists u. exists (s - 1). exists v1.
    intuition.
    - apply (list_no_emp_pos_len v). intuition.
    - assert (s > 0) by (apply (list_no_emp_pos_len v s); intuition). intuition.
    - destruct (list_tl_len_plus_1 v v1 (s - 1) H).
      apply H1. replace (s - 1 + 1) with s by intuition.
      assumption.
    - apply (list_tl_sorted v v1). intuition.
    - destruct (list_no_emp_exists_hd v1) as [u1 Htli].
      destruct (list_hd_sorted v v1 u u1).
      * intuition.
      * intuition.
      * exists u1. intuition.
  Qed.
End Goal.
