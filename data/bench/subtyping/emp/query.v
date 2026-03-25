From Stdlib Require Import BinInt.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.
From Stdlib Require Import Floats.
Open Scope Z_scope.

Module Type Signatures.
Parameter tree : forall (a : Type), Type.

  Parameter TT : unit.
  Parameter bool_gen : unit -> Prop.
  Parameter int_gen : unit -> Z.
  Parameter nat_gen : unit -> Z.
  Parameter int_range_inc : Z -> Z -> Z.
  Parameter int_range_inex : Z -> Z -> Z.
  Parameter increment : Z -> Z.
  Parameter decrement : Z -> Z.
  Parameter lt_eq_one : Z -> Prop.
  Parameter gt_eq_int_gen : Z -> Z.
  Parameter sizecheck : Z -> Prop.
  Parameter subs : Z -> Z.
  Parameter dummy : unit.
  Parameter len : forall {a : Type}, list a -> Z -> Prop.
  Parameter emp : forall {a : Type}, list a -> Prop.
  Parameter hd : forall {a : Type}, list a -> a -> Prop.
  Parameter tl : forall {a : Type}, list a -> list a -> Prop.
  Parameter list_mem : forall {a : Type}, list a -> a -> Prop.
  Parameter sorted : forall {a : Type}, list a -> Prop.
  Parameter uniq : forall {a : Type}, list a -> Prop.
  Parameter listLen : forall {a : Type}, list a -> Z.
  Parameter depth : forall {a : Type}, tree a -> Z -> Prop.
  Parameter leaf : forall {a : Type}, tree a -> Prop.
  Parameter root : forall {a : Type}, tree a -> a -> Prop.
  Parameter lch : forall {a : Type}, tree a -> tree a -> Prop.
  Parameter rch : forall {a : Type}, tree a -> tree a -> Prop.
  Parameter tree_mem : forall {a : Type}, tree a -> a -> Prop.
  Parameter bst : forall {a : Type}, tree a -> Prop.
  Parameter heap : forall {a : Type}, tree a -> Prop.
  Parameter complete : forall {a : Type}, tree a -> Prop.
  Parameter treeNumNode : forall {a : Type}, tree a -> Z.


  Axiom list_len_0_emp : forall (l : list Z), emp l -> len l 0.
End Signatures.

Module Axioms : Signatures.

  Inductive tree' (a : Type) : Type :=
  | Leaf : tree' a
  | Node : a -> tree' a -> tree' a -> tree' a.
  Definition tree := tree'.
  

  Parameter TT : unit.
  Parameter bool_gen : unit -> Prop.
  Parameter int_gen : unit -> Z.
  Parameter nat_gen : unit -> Z.
  Parameter int_range_inc : Z -> Z -> Z.
  Parameter int_range_inex : Z -> Z -> Z.
  Parameter increment : Z -> Z.
  Parameter decrement : Z -> Z.
  Parameter lt_eq_one : Z -> Prop.
  Parameter gt_eq_int_gen : Z -> Z.
  Parameter sizecheck : Z -> Prop.
  Parameter subs : Z -> Z.
  Parameter dummy : unit.

  Fixpoint len {a : Type} (l : list a) (n : Z) : Prop :=
    match l with
    | nil => n = 0
    | cons _ xs => len xs (n - 1)
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
  
  Parameter sorted : forall {a : Type}, list a -> Prop.

  Fixpoint uniq {a : Type} (l : list a) : Prop :=
    match l with
    | nil => True
    | cons x xs => ~(list_mem xs x) /\ uniq xs
    end.
  
  Parameter listLen : forall {a : Type}, list a -> Z.
  Parameter depth : forall {a : Type}, tree a -> Z -> Prop.

  Definition leaf {a : Type} (t : tree a) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ _ _ _ => False
    end.
  

  Definition root {a : Type} (t : tree a) (x : a) : Prop :=
    match t with
    | Leaf _ => False
    | Node _ x' _ _ => x = x'
    end.
  
  Parameter lch : forall {a : Type}, tree a -> tree a -> Prop.
  Parameter rch : forall {a : Type}, tree a -> tree a -> Prop.
  Parameter tree_mem : forall {a : Type}, tree a -> a -> Prop.
  Parameter bst : forall {a : Type}, tree a -> Prop.
  Parameter heap : forall {a : Type}, tree a -> Prop.
  Parameter complete : forall {a : Type}, tree a -> Prop.
  Parameter treeNumNode : forall {a : Type}, tree a -> Z.


  Lemma list_len_0_emp : forall (l : list Z), emp l -> len l 0.
  Proof.
    intros [| x] H.
    - simpl. reflexivity.
    - contradiction.
  Qed.
End Axioms.

Module Goal.
  Import Axioms.

  Theorem goal : forall (s : Z), 0 <= s -> forall (v : list Z), emp v -> exists (n : Z), len v n /\ n <= s.
  Proof.
    intros s Hs v He.
    exists 0.
    intuition.
    apply (list_len_0_emp v He).
  Qed.
End Goal.
