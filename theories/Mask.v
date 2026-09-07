(** * Availability masks

    A mask records availability at fixed positions: [true] is available and
    [false] is consumed or absent. Consumption never removes a position.
    The transparent alias keeps masks as ordinary lists; [wf_mask] relates
    their length to a separately supplied scope.

    This module contains mask operations, inclusion and pointwise splitting.
    Their interpretations as embeddings and context splits are developed in
    [OPE.v] and [Split.v]. *)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.
From DILLref Require Import Prelude.

Definition mask : Type := list bool.

Definition wf_mask {A : Type} (L : list A) (U : mask) : Prop :=
  length U = length L.

(** ** Mask constructors by scope size

    These functions depend only on the number of positions. Contexts and
    their entries are supplied separately by embedding and typing judgments. *)

Definition mask_id (n : nat) : mask := repeat true n.

(** Embed an [n]-position scope below one new, unavailable position. *)
Definition mask_wk (n : nat) : mask := false :: mask_id n.

Definition mask_zero (n : nat) : mask := repeat false n.

(** Exactly one position is available. An out-of-scope index selects none;
    the variable typing rule separately requires a successful lookup. *)
Fixpoint mask_single (n i : nat) : mask :=
  match n, i with
  | 0, _ => []
  | S n', 0 => true :: mask_zero n'
  | S n', S i' => false :: mask_single n' i'
  end.

(** [mask_comp U V] first restricts by [U], then by [V] inside the kept
    positions. The [true]-with-empty-[V] branch is unreachable for
    well-formed inputs and is chosen to drop the position. *)
Fixpoint mask_comp (U V : mask) : mask :=
  match U with
  | [] => []
  | false :: U' => false :: mask_comp U' V
  | true :: U' =>
      match V with
      | v :: V' => v :: mask_comp U' V'
      | [] => false :: mask_comp U' []
      end
  end.

Definition mask_compl (U : mask) : mask := map negb U.

(** ** Composition laws

    The inner mask has one position for each [true] in the outer mask.
    This numerical condition expresses compatibility without any context
    entries or embedding derivation. *)
Fixpoint mask_count (U : mask) : nat :=
  match U with
  | [] => 0
  | true :: U' => S (mask_count U')
  | false :: U' => mask_count U'
  end.

Lemma mask_comp_id_l : forall U,
  mask_comp (mask_id (length U)) U = U.
Proof. induction U; simpl; f_equal; assumption. Qed.

Lemma mask_comp_id_r : forall U,
  mask_comp U (mask_id (mask_count U)) = U.
Proof. induction U as [| [] U IH]; simpl; f_equal; assumption. Qed.

Lemma mask_comp_assoc : forall U V W,
  length V = mask_count U ->
  mask_comp (mask_comp U V) W = mask_comp U (mask_comp V W).
Proof.
  induction U as [| [] U IH]; intros V W Hlen; simpl; auto.
  - destruct V as [| [|] V]; simpl in Hlen; try discriminate; simpl.
    + destruct W; simpl; f_equal; apply IH; lia.
    + f_equal. apply IH. lia.
  - f_equal. apply IH. exact Hlen.
Qed.

(** ** Masks over a fixed scope

    Inclusion and intersection compare positions in the same full scope.
    Unlike [mask_comp], neither operation reindexes through a smaller scope.
    Inclusion enforces equal lengths; executable intersection is specified
    on equal-length inputs and truncates malformed inputs. *)

Inductive mask_le : mask -> mask -> Prop :=
  | MaskLeNil : mask_le [] []
  | MaskLeOff : forall b U V, mask_le U V -> mask_le (false :: U) (b :: V)
  | MaskLeOn : forall U V, mask_le U V -> mask_le (true :: U) (true :: V).

Fixpoint mask_meet (U V : mask) : mask :=
  match U, V with
  | u :: U', v :: V' => (u && v) :: mask_meet U' V'
  | _, _ => []
  end.

Lemma mask_le_length : forall U V, mask_le U V -> length U = length V.
Proof. intros U V H. induction H; simpl; congruence. Qed.

Lemma mask_le_refl : forall U, mask_le U U.
Proof. induction U as [| [] U IH]; constructor; assumption. Qed.

Lemma mask_le_trans : forall U V W,
  mask_le U V -> mask_le V W -> mask_le U W.
Proof.
  intros U V W H. revert W. induction H; intros W HW;
    inversion HW; subst; constructor; eauto.
Qed.

Lemma mask_le_antisym : forall U V,
  mask_le U V -> mask_le V U -> U = V.
Proof.
  intros U V H. induction H; intros HV; inversion HV; subst;
    f_equal; auto.
Qed.

Lemma mask_le_nth : forall U V i,
  mask_le U V -> In_opt true (nth_error U i) -> In_opt true (nth_error V i).
Proof.
  intros U V i H. revert i. induction H; intros [| i] Hi;
    simpl in *; try discriminate; try contradiction; auto.
Qed.

Lemma mask_meet_length : forall U V,
  length U = length V -> length (mask_meet U V) = length U.
Proof.
  induction U; destruct V; simpl; intros H; try discriminate;
    f_equal; auto.
Qed.

Lemma mask_meet_comm : forall U V, mask_meet U V = mask_meet V U.
Proof.
  induction U; destruct V; simpl; auto. rewrite andb_comm, IHU. reflexivity.
Qed.

Lemma mask_meet_assoc : forall U V W,
  mask_meet (mask_meet U V) W = mask_meet U (mask_meet V W).
Proof.
  induction U; destruct V, W; simpl; auto.
  rewrite andb_assoc, IHU. reflexivity.
Qed.

Lemma mask_meet_idem : forall U, mask_meet U U = U.
Proof. induction U; simpl; auto. rewrite andb_diag, IHU. reflexivity. Qed.

Lemma mask_meet_le_l : forall U V,
  length U = length V -> mask_le (mask_meet U V) U.
Proof.
  induction U as [| [] U IH]; intros [| [] V] H; simpl in *;
    try discriminate; constructor; apply IH; lia.
Qed.

Lemma mask_meet_le_r : forall U V,
  length U = length V -> mask_le (mask_meet U V) V.
Proof. intros. rewrite mask_meet_comm. apply mask_meet_le_l. lia. Qed.

Lemma mask_meet_greatest : forall W U V,
  mask_le W U -> mask_le W V -> mask_le W (mask_meet U V).
Proof.
  intros W U V H. revert V. induction H; intros R HV;
    inversion HV; subst; simpl; constructor; auto.
Qed.

Lemma mask_zero_length : forall n, length (mask_zero n) = n.
Proof. intros. apply repeat_length. Qed.

Lemma mask_single_length : forall n i, length (mask_single n i) = n.
Proof.
  induction n; intros [| i]; simpl; auto.
  rewrite mask_zero_length. reflexivity.
Qed.

Lemma mask_single_nth : forall n i,
  i < n -> In_opt true (nth_error (mask_single n i) i).
Proof.
  induction n as [| n IH]; intros [| i] Hi; simpl in *; try lia; auto.
  apply IH. lia.
Qed.

Lemma mask_zero_no_true : forall n i,
  ~ In_opt true (nth_error (mask_zero n) i).
Proof.
  induction n; intros [| i]; simpl; try discriminate; auto.
Qed.

Lemma mask_zero_le : forall n U, length U = n -> mask_le (mask_zero n) U.
Proof.
  induction n; destruct U; simpl; intros H;
    try discriminate; constructor; apply IHn; lia.
Qed.

Lemma mask_le_zero : forall n U, mask_le U (mask_zero n) -> U = mask_zero n.
Proof.
  intros n U H. apply mask_le_antisym; [exact H | ].
  apply mask_zero_le.
  rewrite (mask_le_length _ _ H), mask_zero_length. reflexivity.
Qed.

Lemma mask_meet_wf : forall {A : Type} (L : list A) U V,
  wf_mask L U -> wf_mask L V -> wf_mask L (mask_meet U V).
Proof.
  unfold wf_mask. intros. rewrite mask_meet_length; lia.
Qed.

(** ** Pointwise splitting of masks

    [SplitM I U F]: every available position of [I] is available in exactly
    one of [U] and [F]; an unavailable position is available in neither. *)
Inductive SplitM : mask -> mask -> mask -> Prop :=
  | SplitMNil : SplitM [] [] []
  | SplitMOff : forall I U F,
      SplitM I U F -> SplitM (false :: I) (false :: U) (false :: F)
  | SplitMLeft : forall I U F,
      SplitM I U F -> SplitM (true :: I) (true :: U) (false :: F)
  | SplitMRight : forall I U F,
      SplitM I U F -> SplitM (true :: I) (false :: U) (true :: F).

Lemma splitM_length : forall I U F,
  SplitM I U F -> length U = length I /\ length F = length I.
Proof. intros I U F H. induction H; simpl; lia. Qed.

Lemma splitM_comm : forall I U F, SplitM I U F -> SplitM I F U.
Proof. intros I U F H. induction H; constructor; assumption. Qed.

(** The remainder is relative to the input mask: unavailable positions must
    stay unavailable. Plain Boolean complementation would resurrect them. *)
Definition mask_diff (I U : mask) : mask :=
  mask_meet I (mask_compl U).

Lemma splitM_le_l : forall I U F, SplitM I U F -> mask_le U I.
Proof. intros I U F H. induction H; constructor; assumption. Qed.

Lemma splitM_le_r : forall I U F, SplitM I U F -> mask_le F I.
Proof. intros. eapply splitM_le_l, splitM_comm; eassumption. Qed.

Lemma splitM_no_overlap : forall I U F i,
  SplitM I U F -> In_opt true (nth_error U i) -> In_opt true (nth_error F i) -> False.
Proof.
  intros I U F i H. revert i. induction H; intros [| i] HU HF;
    simpl in *; try discriminate; eauto.
Qed.

Lemma splitM_diff : forall I U,
  mask_le U I -> SplitM I U (mask_diff I U).
Proof.
  intros I U H. induction H; unfold mask_diff in *; simpl.
  - constructor.
  - destruct b; constructor; assumption.
  - constructor. assumption.
Qed.

Lemma splitM_remainder : forall I U F,
  SplitM I U F -> F = mask_diff I U.
Proof. intros I U F H. induction H; unfold mask_diff in *; simpl; congruence. Qed.

Lemma splitM_iff : forall I U F,
  SplitM I U F <-> mask_le U I /\ F = mask_diff I U.
Proof.
  split.
  - intros H. split; [eapply splitM_le_l | apply splitM_remainder]; eassumption.
  - intros [H ->]. apply splitM_diff, H.
Qed.

Lemma splitM_right_unique : forall I U F F',
  SplitM I U F -> SplitM I U F' -> F = F'.
Proof. intros. rewrite (splitM_remainder _ _ _ H), (splitM_remainder _ _ _ H0). reflexivity. Qed.

Lemma splitM_left : forall I, SplitM I I (mask_zero (length I)).
Proof. induction I as [| [] I IH]; simpl; constructor; assumption. Qed.

Lemma splitM_right : forall I, SplitM I (mask_zero (length I)) I.
Proof. intros. apply splitM_comm, splitM_left. Qed.

Lemma splitM_zero : forall n,
  SplitM (mask_zero n) (mask_zero n) (mask_zero n).
Proof. induction n; simpl; constructor; assumption. Qed.

Lemma splitM_assoc : forall I AB C A B,
  SplitM I AB C -> SplitM AB A B ->
  exists BC, SplitM I A BC /\ SplitM BC B C.
Proof.
  intros I AB C A B H. revert A B.
  induction H; intros A B HAB;
    inversion HAB as [| ? ? ? HAB' | ? ? ? HAB' | ? ? ? HAB']; subst.
  - exists []. split; constructor.
  - destruct (IHSplitM _ _ HAB') as [BC [H1 H3]].
    exists (false :: BC). split; constructor; assumption.
  - destruct (IHSplitM _ _ HAB') as [BC [H1 H3]].
    exists (false :: BC). split; constructor; assumption.
  - destruct (IHSplitM _ _ HAB') as [BC [H1 H3]].
    exists (true :: BC). split; constructor; assumption.
  - destruct (IHSplitM _ _ HAB') as [BC [H1 H3]].
    exists (true :: BC). split; constructor; assumption.
Qed.

Lemma splitM_unassoc : forall I A BC B C,
  SplitM I A BC -> SplitM BC B C ->
  exists AB, SplitM I AB C /\ SplitM AB A B.
Proof.
  intros I A BC B C H1 H2.
  apply splitM_comm in H1. apply splitM_comm in H2.
  destruct (splitM_assoc _ _ _ _ _ H1 H2) as [AB [H3 H4]].
  exists AB. split; apply splitM_comm; assumption.
Qed.

Lemma splitM_wf_whole : forall {A : Type} (L : list A) I U F,
  SplitM I U F -> wf_mask L U -> wf_mask L I.
Proof.
  unfold wf_mask. intros A L I U F H HU.
  destruct (splitM_length _ _ _ H). lia.
Qed.

(** Shrinking one part preserves disjointness with the other part. *)
Lemma splitM_subright : forall I U F,
  SplitM I U F -> forall F', mask_le F' F ->
  exists I', SplitM I' U F' /\ mask_le I' I.
Proof.
  intros I U F H. induction H; intros F' Hle; inversion Hle; subst;
    try solve [exists []; split; constructor].
  all: match goal with Htail : mask_le _ _ |- _ =>
    destruct (IHSplitM _ Htail) as [I' [Hs Hi]] end;
    eexists; split; constructor; eassumption.
Qed.

Lemma splitM_zero_right_inv : forall I U n,
  SplitM I U (mask_zero n) -> I = U.
Proof.
  induction I as [| b I IH]; intros U [| n] H; inversion H; subst; simpl in *;
    f_equal; eauto.
Qed.
