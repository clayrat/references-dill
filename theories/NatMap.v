(** * Association lists with natural-number keys

    [NatMap A] is a transparent list representation. Positions retain their
    order and are independent of keys. Raw lists may contain duplicate keys;
    callers require [NoDup (natmap_domain m)] when uniqueness is needed. *)

From Stdlib Require Import List Arith Bool.
Import ListNotations.
From DILLref Require Import Prelude.

Definition NatMap (A : Type) : Type := list (nat * A).

Definition natmap_domain {A : Type} (m : NatMap A) : list nat := map fst m.

(** Lookup returns the first entry with the requested key. *)
Fixpoint natmap_lookup {A : Type} (k : nat) (m : NatMap A) : option A :=
  match m with
  | [] => None
  | (j, v) :: rest => if Nat.eqb k j then Some v else natmap_lookup k rest
  end.

(** Replacement preserves keys and order, updating every matching entry.
    An absent key leaves the map unchanged. With unique keys and a successful
    lookup, exactly one entry is replaced. *)
Definition natmap_replace {A : Type} (k : nat) (v : A) (m : NatMap A) : NatMap A :=
  map (fun p => (fst p, if Nat.eqb k (fst p) then v else snd p)) m.

Lemma natmap_replace_domain : forall {A : Type} k (v : A) m,
  natmap_domain (natmap_replace k v m) = natmap_domain m.
Proof. intros A k v m. induction m as [| [j w] m IH]; simpl; f_equal; auto. Qed.

Lemma natmap_lookup_in : forall {A : Type} k (v : A) m,
  In_opt v (natmap_lookup k m) -> In (k, v) m.
Proof.
  intros A k v m. induction m as [| [j w] m IH]; simpl; intros H; try contradiction.
  destruct (Nat.eqb k j) eqn:E; simpl in H.
  - apply Nat.eqb_eq in E. subst. left. reflexivity.
  - right. auto.
Qed.

Lemma natmap_lookup_replace : forall {A : Type} k (v old : A) m,
  In_opt old (natmap_lookup k m) -> In_opt v (natmap_lookup k (natmap_replace k v m)).
Proof.
  intros A k v old m. induction m as [| [j w] m IH]; simpl; intros H; try contradiction.
  destruct (Nat.eqb k j); simpl in *; auto.
Qed.

Lemma natmap_lookup_replace_other : forall {A : Type} k j (v : A) m,
  j <> k -> natmap_lookup j (natmap_replace k v m) = natmap_lookup j m.
Proof.
  intros A k j v m Hne. induction m as [| [l w] m IH]; simpl; auto.
  destruct (Nat.eqb j l) eqn:E; simpl; auto.
  destruct (Nat.eqb k l) eqn:F; auto.
  apply Nat.eqb_eq in E, F. congruence.
Qed.

(** A unique key identifies its list position regardless of the entry type. *)
Lemma natmap_key_index : forall {A : Type} (m : NatMap A) i j k a b,
  NoDup (natmap_domain m) -> In_opt (k, a) (nth_error m i) ->
  In_opt (k, b) (nth_error m j) -> i = j.
Proof.
  intros A m. induction m as [| [l c] m IH]; intros i j k a b Hnd Hi Hj;
    destruct i, j; simpl in *; try contradiction; auto.
  - inversion Hnd; subst. injection Hi as Hk Ha; subst.
    exfalso. apply H1. apply In_opt_eq_Some, nth_error_In, (in_map fst) in Hj.
    exact Hj.
  - inversion Hnd; subst. injection Hj as Hk Hb; subst.
    exfalso. apply H1. apply In_opt_eq_Some, nth_error_In, (in_map fst) in Hi.
    exact Hi.
  - inversion Hnd; subst. f_equal. eauto.
Qed.
