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

(** Decidable equality is kept computational so algorithms do not depend on
    proof-producing list equality after extraction. *)
Fixpoint mask_eqb (U V : mask) : bool :=
  match U, V with
  | [], [] => true
  | u :: U', v :: V' => Bool.eqb u v && mask_eqb U' V'
  | _, _ => false
  end.

Lemma mask_eqb_refl : forall U, mask_eqb U U = true.
Proof. induction U as [| [] U IH]; simpl; auto. Qed.

Lemma mask_eqb_eq : forall U V, mask_eqb U V = true -> U = V.
Proof.
  induction U as [| u U IH]; destruct V as [| v V]; simpl; intros H;
    try discriminate; auto.
  apply andb_true_iff in H. destruct H as [Huv Htail].
  apply Bool.eqb_prop in Huv. subst. f_equal. apply IH, Htail.
Qed.

Lemma mask_eqb_iff : forall U V, mask_eqb U V = true <-> U = V.
Proof.
  split; [apply mask_eqb_eq | intros ->; apply mask_eqb_refl].
Qed.

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

(** Consume one available position while retaining every position in the
    mask. Failure distinguishes an absent or already unavailable position. *)
Fixpoint mask_consume (i : nat) (U : mask) : option mask :=
  match i, U with
  | 0, true :: U' => Some (false :: U')
  | S i', b :: U' =>
      match mask_consume i' U' with
      | Some V => Some (b :: V)
      | None => None
      end
  | _, _ => None
  end.

Lemma mask_consume_available : forall I i O,
  In_opt O (mask_consume i I) -> In_opt true (nth_error I i).
Proof.
  induction I as [| b I IH]; intros [| i] O H; apply In_opt_Some in H;
    simpl in H; try discriminate.
  - destruct b; simpl in H; try discriminate. inversion H. reflexivity.
  - destruct (mask_consume i I) eqn:E; try discriminate.
    inversion H; subst. simpl. eapply IH, Some_In_opt, E.
Qed.

Lemma mask_consume_complete : forall I i,
  In_opt true (nth_error I i) -> exists O, In_opt O (mask_consume i I).
Proof.
  induction I as [| b I IH]; intros [| i] H; simpl in H; try contradiction.
  - destruct b; simpl in H.
    + eexists. reflexivity.
    + discriminate.
  - destruct (IH i H) as [O E]. simpl. rewrite (In_opt_Some E).
    eexists. reflexivity.
Qed.

Lemma mask_consume_iff : forall I i,
  (exists O, In_opt O (mask_consume i I)) <-> In_opt true (nth_error I i).
Proof.
  split.
  - intros [O H]. eapply mask_consume_available, H.
  - apply mask_consume_complete.
Qed.

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

(** Union is used in proofs to describe positions consumed by at least one
    additive alternative. The checker computes the dual operation
    [mask_meet] on leftovers. *)
Fixpoint mask_join (U V : mask) : mask :=
  match U, V with
  | u :: U', v :: V' => (u || v) :: mask_join U' V'
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

Lemma mask_le_tail : forall u v U V,
  mask_le (u :: U) (v :: V) -> mask_le U V.
Proof. intros u v U V H. inversion H; subst; assumption. Qed.

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

Lemma mask_join_length : forall U V,
  length U = length V -> length (mask_join U V) = length U.
Proof.
  induction U; destruct V; simpl; intros H; try discriminate;
    f_equal; auto.
Qed.

Lemma mask_join_comm : forall U V, mask_join U V = mask_join V U.
Proof.
  induction U; destruct V; simpl; auto. rewrite orb_comm, IHU. reflexivity.
Qed.

Lemma mask_le_join_l : forall U V,
  length U = length V -> mask_le U (mask_join U V).
Proof.
  induction U as [| u U IH]; destruct V as [| v V]; simpl; intros H;
    try discriminate; try constructor.
  destruct u, v; simpl; constructor; apply IH; lia.
Qed.

Lemma mask_le_join_r : forall U V,
  length U = length V -> mask_le V (mask_join U V).
Proof. intros. rewrite mask_join_comm. apply mask_le_join_l. lia. Qed.

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

Lemma splitM_left_unique : forall I U U' F,
  SplitM I U F -> SplitM I U' F -> U = U'.
Proof.
  intros. apply splitM_comm in H, H0.
  eapply splitM_right_unique; eassumption.
Qed.

Lemma splitM_left : forall I, SplitM I I (mask_zero (length I)).
Proof. induction I as [| [] I IH]; simpl; constructor; assumption. Qed.

Lemma splitM_right : forall I, SplitM I (mask_zero (length I)) I.
Proof. intros. apply splitM_comm, splitM_left. Qed.

Lemma splitM_zero_left_inv : forall I F n,
  SplitM I (mask_zero n) F -> I = F.
Proof.
  induction I as [| b I IH]; intros F [| n] H; inversion H; subst; simpl in *;
    f_equal; eauto.
Qed.

(** Successful consumption is the executable complement of the singleton
    demand at the selected position. *)
Lemma mask_consume_split : forall I i O,
  In_opt O (mask_consume i I) ->
  SplitM I (mask_single (length I) i) O.
Proof.
  induction I as [| b I IH]; intros [| i] O H; apply In_opt_Some in H;
    simpl in H; try discriminate.
  - destruct b; try discriminate. inversion H; subst. simpl.
    apply SplitMLeft, splitM_right.
  - destruct (mask_consume i I) eqn:E; try discriminate.
    inversion H; subst. simpl. destruct b.
    + apply SplitMRight. eapply IH, Some_In_opt, E.
    + apply SplitMOff. eapply IH, Some_In_opt, E.
Qed.

Lemma mask_consume_le : forall I i O,
  In_opt O (mask_consume i I) -> mask_le O I.
Proof. intros. eapply splitM_le_r, mask_consume_split, H. Qed.

Lemma mask_consume_length : forall I i O,
  In_opt O (mask_consume i I) -> length O = length I.
Proof.
  intros I i O H. apply mask_consume_split in H.
  destruct (splitM_length _ _ _ H). assumption.
Qed.

Lemma mask_consume_of_split : forall I i O,
  In_opt true (nth_error I i) ->
  SplitM I (mask_single (length I) i) O ->
  In_opt O (mask_consume i I).
Proof.
  intros I i O Havailable Hsplit.
  destruct (mask_consume_complete _ _ Havailable) as [F Hconsume].
  pose proof (mask_consume_split _ _ _ Hconsume) as Hcomputed.
  pose proof (splitM_right_unique _ _ _ _ Hcomputed Hsplit) as ->.
  exact Hconsume.
Qed.

Lemma splitM_tail : forall i u f I U F,
  SplitM (i :: I) (u :: U) (f :: F) -> SplitM I U F.
Proof. intros i u f I U F H. inversion H; subst; assumption. Qed.

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

(** Additive alternatives consume the union of their demands and leave the
    intersection of their remainders. *)
Lemma splitM_join_remainders : forall I U1 F1 U2 F2,
  SplitM I U1 F1 -> SplitM I U2 F2 ->
  SplitM I (mask_join U1 U2) (mask_meet F1 F2).
Proof.
  intros I U1 F1 U2 F2 H1. revert U2 F2.
  induction H1; intros U2 F2 H2; inversion H2; subst; simpl;
    constructor; eauto.
Qed.

(** Adding available positions to the whole mask preserves an existing
    demand and passes the added positions to the remainder. *)
Lemma splitM_extend : forall I U F,
  SplitM I U F -> forall J, mask_le I J ->
  exists P, SplitM J U P /\ mask_le F P.
Proof.
  intros I U F Hsplit J Hle. revert U F Hsplit.
  induction Hle; intros demand remainder Hsplit; inversion Hsplit; subst.
  - exists []. split; constructor.
  - match goal with
    | IH : forall U F, SplitM _ U F -> _, Htail : SplitM _ _ _ |- _ =>
        destruct (IH _ _ Htail) as [P [Hs Hp]]
    end.
    destruct b; eexists; split; constructor; eassumption.
  - match goal with
    | IH : forall U F, SplitM _ U F -> _, Htail : SplitM _ _ _ |- _ =>
        destruct (IH _ _ Htail) as [P [Hs Hp]]
    end;
    eexists; split; constructor; eassumption.
  - match goal with
    | IH : forall U F, SplitM _ U F -> _, Htail : SplitM _ _ _ |- _ =>
        destruct (IH _ _ Htail) as [P [Hs Hp]]
    end.
    exists (true :: P). split; constructor; assumption.
Qed.

(** Reducing a demand returns the removed positions to the remainder. *)
Lemma splitM_shrink_left : forall I U F,
  SplitM I U F -> forall V, mask_le V U ->
  exists O, SplitM I V O /\ mask_le F O.
Proof.
  intros I U F Hsplit V Hle. revert I F Hsplit.
  induction Hle; intros whole remainder Hsplit; inversion Hsplit; subst.
  - exists []. split; constructor.
  - match goal with
    | IH : forall I F, SplitM I _ F -> _, Htail : SplitM _ _ _ |- _ =>
        destruct (IH _ _ Htail) as [O [Hs Ho]]
    end.
    exists (false :: O). split; constructor; assumption.
  - match goal with
    | IH : forall I F, SplitM I _ F -> _, Htail : SplitM _ _ _ |- _ =>
        destruct (IH _ _ Htail) as [O [Hs Ho]]
    end.
    exists (true :: O). split; constructor; assumption.
  - match goal with
    | IH : forall I F, SplitM I _ F -> _, Htail : SplitM _ _ _ |- _ =>
        destruct (IH _ _ Htail) as [O [Hs Ho]]
    end.
    exists (true :: O). split; constructor; assumption.
  - match goal with
    | IH : forall I F, SplitM I _ F -> _, Htail : SplitM _ _ _ |- _ =>
        destruct (IH _ _ Htail) as [O [Hs Ho]]
    end.
    exists (false :: O). split; constructor; assumption.
Qed.

(** Reassociate a sequential demand and transport it to another frame. *)
Lemma splitM_frame_sequence : forall I C1 O1 C2 O C J P,
  SplitM I C1 O1 -> SplitM O1 C2 O ->
  SplitM I C O -> SplitM J C P ->
  exists P1, SplitM J C1 P1 /\ SplitM P1 C2 P.
Proof.
  intros I C1 O1 C2 O C J P H1 H2 Htotal Hframe.
  destruct (splitM_unassoc _ _ _ _ _ H1 H2) as [C' [Hwhole Hparts]].
  pose proof (splitM_left_unique _ _ _ _ Hwhole Htotal) as HC. subst C'.
  eapply splitM_assoc; eassumption.
Qed.

(** Transport both additive demands through a frame whose demand is their
    union. The transported remainders still intersect to the framed result. *)
Lemma splitM_frame_meet : forall I C1 O1 C2 O2 C J P,
  SplitM I C1 O1 -> SplitM I C2 O2 ->
  SplitM I C (mask_meet O1 O2) -> SplitM J C P ->
  exists P1 P2, SplitM J C1 P1 /\ SplitM J C2 P2 /\
    mask_meet P1 P2 = P.
Proof.
  intros I C1 O1 C2 O2 C J P H1 H2 Htotal Hframe.
  pose proof (splitM_join_remainders _ _ _ _ _ H1 H2) as Hjoin.
  pose proof (splitM_left_unique _ _ _ _ Hjoin Htotal) as HC. subst C.
  pose proof (splitM_length _ _ _ H1) as [HC1 _].
  pose proof (splitM_length _ _ _ H2) as [HC2 _].
  assert (Hlen : length C1 = length C2) by lia.
  assert (HC1J : mask_le C1 J).
  { eapply mask_le_trans; [apply mask_le_join_l; exact Hlen | ].
    eapply splitM_le_l, Hframe. }
  assert (HC2J : mask_le C2 J).
  { eapply mask_le_trans; [apply mask_le_join_r; exact Hlen | ].
    eapply splitM_le_l, Hframe. }
  pose proof (splitM_diff _ _ HC1J) as HJ1.
  pose proof (splitM_diff _ _ HC2J) as HJ2.
  pose proof (splitM_join_remainders _ _ _ _ _ HJ1 HJ2) as HJjoin.
  exists (mask_diff J C1), (mask_diff J C2). repeat split; try assumption.
  symmetry. eapply splitM_right_unique; eassumption.
Qed.
