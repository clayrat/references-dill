(** * Option utilities

    [In_opt x o] states that [o] contains exactly [x]. Judgments and lemmas
    about lookups use it instead of the equation [o = Some x], so that a
    concrete lookup reduces by [simpl] to an equality of the contained value
    or to [False]. [In_opt_eq_Some] converts to the equational form when a
    standard-library lemma needs it. *)

Definition Exists_opt {A : Type} (P : A -> Prop) (value : option A) : Prop :=
  match value with
  | Some actual => P actual
  | None => False
  end.

Definition In_opt {A : Type} (expected : A) : option A -> Prop :=
  Exists_opt (eq expected).

Lemma In_opt_eq_Some {A : Type} (expected : A) (value : option A) :
  In_opt expected value <-> value = Some expected.
Proof.
  destruct value as [actual |]; cbn [In_opt Exists_opt].
  - split; intros equal.
    + rewrite <- equal; reflexivity.
    + inversion equal; reflexivity.
  - split; intros impossible.
    + contradiction.
    + discriminate.
Qed.
