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

  Axiom list_len_0_emp : forall (l : list Z), emp l -> len l 0.
  Axiom list_emp_unique : forall (l : list Z), emp l -> uniq l.
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

  Lemma list_len_0_emp : forall (l : list Z), emp l -> len l 0.
  Proof.
    intros [| x] H.
    - reflexivity.
    - contradiction.
  Qed.
  Lemma list_emp_unique : forall (l : list Z), emp l -> uniq l.
  Proof.
    intros [| x] H.
    - reflexivity.
    - contradiction.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (s : Z), 0 <= s -> forall (v : list Z), emp v -> len v 0 /\ uniq v.
  Proof.
    intros s Hs v He.
    split.
    apply (list_len_0_emp v He).
    apply (list_emp_unique v He).
  Qed.
End Goal.
