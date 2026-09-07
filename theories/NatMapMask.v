(** * Keys selected by a positional mask

    Availability refers to an entry's position, independently of its key
    and payload. Unique keys are needed to turn disjoint positions into
    disjoint keys; the raw map representation does not enforce uniqueness. *)

From Stdlib Require Import List.
From DILLref Require Import Prelude NatMap Mask.

Definition masked_key {A : Type} (m : NatMap A) (U : mask) (k : nat) : Prop :=
  exists i a, In_opt (k, a) (nth_error m i) /\ In_opt true (nth_error U i).

Lemma masked_key_mono : forall {A : Type} (m : NatMap A) U V k,
  mask_le U V -> masked_key m U k -> masked_key m V k.
Proof.
  intros A m U V k Hle [i [a [Hm HU]]]. exists i, a.
  split; eauto using mask_le_nth.
Qed.

Lemma masked_key_domain : forall {A : Type} (m : NatMap A) U k,
  masked_key m U k -> In k (natmap_domain m).
Proof.
  intros A m U k [i [a [H _]]].
  apply In_opt_eq_Some, nth_error_In, (in_map fst) in H. exact H.
Qed.

Lemma masked_key_disjoint : forall {A : Type} (m : NatMap A) U U1 U2 k,
  NoDup (natmap_domain m) -> SplitM U U1 U2 ->
  masked_key m U1 k -> masked_key m U2 k -> False.
Proof.
  intros A m U U1 U2 k Hnd Hsplit [i [a [Hi Hui]]] [j [b [Hj Huj]]].
  assert (i = j) by (eapply natmap_key_index; eassumption). subst j.
  eapply splitM_no_overlap; eassumption.
Qed.
