(** * Index maps and preservation of list entries

    Maps are total on natural numbers; scope bounds describe their valid
    inputs. Lifting fixes the new index zero and shifts the old images.
    Preserving list entries does not require injectivity or monotonicity:
    distinct positions carrying equal entries may have the same image. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From DILLref Require Import Prelude.

Definition id_ren (i : nat) : nat := i.

Definition up_ren (r : nat -> nat) (i : nat) : nat :=
  match i with 0 => 0 | S j => S (r j) end.

Lemma up_ren_ext : forall r s,
  (forall i, r i = s i) -> forall i, up_ren r i = up_ren s i.
Proof. intros r s H [| i]; simpl; auto. Qed.

Lemma up_ren_id : forall r,
  (forall i, r i = i) -> forall i, up_ren r i = i.
Proof. intros r H [| i]; simpl; auto. Qed.

Definition ren_scoped (n m : nat) (r : nat -> nat) : Prop :=
  forall i, i < n -> r i < m.

Lemma up_ren_scoped : forall n m r,
  ren_scoped n m r -> ren_scoped (S n) (S m) (up_ren r).
Proof.
  unfold ren_scoped. intros n m r H [| i] Hi; simpl; try lia.
  specialize (H i). lia.
Qed.

Lemma lookup_bound : forall {A : Type} (L : list A) i,
  Is_some (nth_error L i) -> i < length L.
Proof.
  intros A L i H. apply nth_error_Some. intros Hnone.
  unfold Is_some, Exists_opt in H. rewrite Hnone in H. exact H.
Qed.

Definition ren_context {A : Type} (G G' : list A) (r : nat -> nat) : Prop :=
  forall i a, In_opt a (nth_error G i) -> In_opt a (nth_error G' (r i)).

Lemma up_ren_context : forall {A : Type} (G G' : list A) r a,
  ren_context G G' r -> ren_context (a :: G) (a :: G') (up_ren r).
Proof. unfold ren_context. intros A G G' r a H [| i] b Hb; simpl in *; auto. Qed.

Lemma ren_context_id : forall {A : Type} (G : list A), ren_context G G id_ren.
Proof. unfold ren_context, id_ren. auto. Qed.

Lemma ren_context_shift : forall {A : Type} (G : list A) a,
  ren_context G (a :: G) S.
Proof. unfold ren_context. intros. exact H. Qed.

(** Identify the first two positions and shift subsequent positions down. *)
Definition contract_ren (i : nat) : nat :=
  match i with 0 => 0 | S j => j end.

(** Adjacent exchange at the front; lifting handles exchange at greater depth. *)
Definition exchange_ren (i : nat) : nat :=
  match i with 0 => 1 | 1 => 0 | S (S j) => S (S j) end.
