(** * Option utilities

    [In_opt x o] states that [o] contains exactly [x]. Judgments and lemmas
    about lookups use it instead of the equation [o = Some x], so that a
    concrete lookup reduces by [simpl] to an equality of the contained value
    or to [False]. [In_opt_eq_Some] converts to the equational form when a
    standard-library lemma needs it. [Is_some o] records only that [o]
    contains a value, when the value itself is irrelevant.

    [bind] sequences partial computations and [guard] imposes a boolean
    side condition. Both unfold under [cbn], so a proof about a function
    written with them sees the underlying case analysis. *)

Definition Exists_opt {A : Type} (P : A -> Prop) (value : option A) : Prop :=
  match value with
  | Some actual => P actual
  | None => False
  end.

Definition In_opt {A : Type} (expected : A) : option A -> Prop :=
  Exists_opt (eq expected).

Definition Is_some {A : Type} (value : option A) : Prop :=
  Exists_opt (fun _ => True) value.

Lemma In_opt_Is_some {A : Type} {expected : A} {value : option A} :
  In_opt expected value -> Is_some value.
Proof. destruct value; cbn [In_opt Is_some Exists_opt]; auto. Qed.

Lemma Is_some_exists {A : Type} (value : option A) :
  Is_some value <-> exists actual, In_opt actual value.
Proof.
  destruct value as [actual |]; cbn [In_opt Is_some Exists_opt].
  - split.
    + intros _. exists actual. reflexivity.
    + auto.
  - split; [contradiction | intros [? impossible]; contradiction].
Qed.

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

Lemma In_opt_Some {A : Type} {expected : A} {value : option A} :
  In_opt expected value -> value = Some expected.
Proof. apply In_opt_eq_Some. Qed.

Lemma Some_In_opt {A : Type} {expected : A} {value : option A} :
  value = Some expected -> In_opt expected value.
Proof. apply In_opt_eq_Some. Qed.

Definition bind {A B : Type} (r : option A) (k : A -> option B) : option B :=
  match r with
  | Some x => k x
  | None => None
  end.
Arguments bind {A B} r k /.

Definition guard {A : Type} (ok : bool) (r : option A) : option A :=
  if ok then r else None.
Arguments guard {A} ok r /.

Lemma In_opt_bind {A B : Type} (r : option A) (k : A -> option B) (y : B) :
  In_opt y (bind r k) <-> Exists_opt (fun x => In_opt y (k x)) r.
Proof. destruct r; cbn; split; auto. Qed.

Lemma In_opt_guard {A : Type} (ok : bool) (r : option A) (y : A) :
  In_opt y (guard ok r) <-> ok = true /\ In_opt y r.
Proof.
  destruct ok; cbn.
  - split; [auto | intros [_ H]; exact H].
  - split; [contradiction | intros [H _]; discriminate].
Qed.
