(** * Order-preserving context splitting

    [Split l ls rs] says that [l] is an interleaving of [ls] and [rs]: every
    element of [l] goes to exactly one side and both sides keep the order of
    [l]. This is the multiplicative division of the resource zone used by
    application, tensor pairs and the other two-premise constructs.

    It is deliberately not a permutation: [Split [x; y] [y; x] []] fails while
    [Permutation [x; y] ([y; x] ++ [])] holds. Exchange is a separate lemma;
    with de Bruijn indices it also renames the term.

    A split is the same thing as an availability mask together with its
    complement ([OPE.v]), and splitting masks pointwise ([SplitU]) is the same
    as splitting the positioned views of the scope. *)

From Stdlib Require Import List Permutation Arith Lia.
Import ListNotations.
From DILLref Require Import OPE.

Section Split.
  Context {A : Type}.

  Inductive Split : list A -> list A -> list A -> Prop :=
    | SplitNil : Split [] [] []
    | SplitL : forall x l ls rs, Split l ls rs -> Split (x :: l) (x :: ls) rs
    | SplitR : forall x l ls rs, Split l ls rs -> Split (x :: l) ls (x :: rs).

  (** ** Units *)

  Lemma split_left : forall l, Split l l [].
  Proof. induction l; constructor; assumption. Qed.

  Lemma split_right : forall l, Split l [] l.
  Proof. induction l; constructor; assumption. Qed.

  Lemma split_nil_inv : forall ls rs, Split [] ls rs -> ls = [] /\ rs = [].
  Proof. intros ls rs H. inversion H. auto. Qed.

  Lemma split_left_inv : forall l ls, Split l ls [] -> ls = l.
  Proof.
    intros l ls H. remember [] as rs. induction H; subst.
    - reflexivity.
    - f_equal. auto.
    - discriminate.
  Qed.

  Lemma split_right_inv : forall l rs, Split l [] rs -> rs = l.
  Proof.
    intros l rs H. remember [] as ls. induction H; subst.
    - reflexivity.
    - discriminate.
    - f_equal. auto.
  Qed.

  Lemma split_cons_inv : forall x l ls rs,
    Split (x :: l) ls rs ->
    (exists ls', ls = x :: ls' /\ Split l ls' rs) \/
    (exists rs', rs = x :: rs' /\ Split l ls rs').
  Proof.
    intros x l ls rs H. inversion H; subst; [left | right]; eexists; eauto.
  Qed.

  (** ** Commutativity *)

  Lemma split_comm : forall l ls rs, Split l ls rs -> Split l rs ls.
  Proof. intros l ls rs H. induction H; constructor; assumption. Qed.

  (** ** Associativity

      Regrouping a three-way division produces the intermediate part as a
      witness; it is unique but only its existence is needed. *)

  Lemma split_assoc : forall l ab c a b,
    Split l ab c -> Split ab a b ->
    exists bc, Split l a bc /\ Split bc b c.
  Proof.
    intros l ab c a b H. revert a b.
    induction H as [| x l ls rs H IH | x l ls rs H IH]; intros a b Hab.
    - inversion Hab; subst. exists []. split; constructor.
    - inversion Hab as [| ? ? ? ? Hab' | ? ? ? ? Hab']; subst.
      + destruct (IH _ _ Hab') as [bc [H1 H2]].
        exists bc. split; [constructor | ]; assumption.
      + destruct (IH _ _ Hab') as [bc [H1 H2]].
        exists (x :: bc). split; constructor; assumption.
    - destruct (IH _ _ Hab) as [bc [H1 H2]].
      exists (x :: bc). split; constructor; assumption.
  Qed.

  Lemma split_unassoc : forall l a bc b c,
    Split l a bc -> Split bc b c ->
    exists ab, Split l ab c /\ Split ab a b.
  Proof.
    intros l a bc b c H1 H2.
    apply split_comm in H1. apply split_comm in H2.
    destruct (split_assoc _ _ _ _ _ H1 H2) as [ab [H3 H4]].
    exists ab. split; apply split_comm; assumption.
  Qed.

  (** ** Relation to lists *)

  Lemma split_length : forall l ls rs,
    Split l ls rs -> length l = length ls + length rs.
  Proof.
    intros l ls rs H. induction H; simpl; auto.
    rewrite IHSplit. symmetry. apply PeanoNat.Nat.add_succ_r.
  Qed.

  Lemma split_in : forall l ls rs,
    Split l ls rs -> forall x, In x l <-> In x ls \/ In x rs.
  Proof.
    intros l ls rs H x. induction H; simpl; tauto.
  Qed.

  Lemma split_permutation : forall l ls rs,
    Split l ls rs -> Permutation l (ls ++ rs).
  Proof.
    intros l ls rs H. induction H; simpl.
    - constructor.
    - constructor. assumption.
    - eapply Permutation_trans; [apply perm_skip; exact IHSplit | ].
      apply Permutation_middle.
  Qed.

  Lemma split_app : forall ls rs, Split (ls ++ rs) ls rs.
  Proof.
    induction ls; simpl; intros.
    - apply split_right.
    - constructor. apply IHls.
  Qed.

  (** ** Complementary masks are a [Split] *)

  Definition mask_compl (U : list bool) : list bool := map negb U.

  Lemma ope_compl_split : forall L U G G',
    ope L U G -> ope L (mask_compl U) G' -> Split L G G'.
  Proof.
    intros L U G G' H. revert G'.
    induction H as [| x L U G H IH | x L U G H IH]; intros G' H'; simpl in H'.
    - inversion H'; subst. constructor.
    - inversion H'; subst. constructor. apply IH. assumption.
    - inversion H'; subst. constructor. apply IH. assumption.
  Qed.

  Lemma split_ope_compl : forall L G G',
    Split L G G' -> exists U, ope L U G /\ ope L (mask_compl U) G'.
  Proof.
    intros L G G' H.
    induction H as [| x l ls rs H [U [HU HU']] | x l ls rs H [U [HU HU']]].
    - exists []. split; constructor.
    - exists (true :: U). split; simpl; constructor; assumption.
    - exists (false :: U). split; simpl; constructor; assumption.
  Qed.

  (** TODO: transport of [Split] along permutations of the whole list and
      the converse of [split_permutation] up to reordering inside the parts,
      which is what relates [Split] to [active_split] in the SCIR development.
      TODO: pointwise intersection of masks for affine branch leftovers. *)
End Split.

(** ** Pointwise splitting of masks

    [SplitU I U F]: every available position of [I] is available in exactly
    one of [U] and [F]; an unavailable position is available in neither. *)
Inductive SplitU : list bool -> list bool -> list bool -> Prop :=
  | SplitU_nil : SplitU [] [] []
  | SplitU_off : forall I U F,
      SplitU I U F -> SplitU (false :: I) (false :: U) (false :: F)
  | SplitU_left : forall I U F,
      SplitU I U F -> SplitU (true :: I) (true :: U) (false :: F)
  | SplitU_right : forall I U F,
      SplitU I U F -> SplitU (true :: I) (false :: U) (true :: F).

Lemma splitU_length : forall I U F,
  SplitU I U F -> length U = length I /\ length F = length I.
Proof. intros I U F H. induction H; simpl; lia. Qed.

Lemma splitU_comm : forall I U F, SplitU I U F -> SplitU I F U.
Proof. intros I U F H. induction H; constructor; assumption. Qed.

Lemma splitU_view : forall I U F,
  SplitU I U F ->
  forall {A : Type} n (L : list A),
    Split (view_from n L I) (view_from n L U) (view_from n L F).
Proof.
  intros I U F H. induction H; intros A n [| x L]; simpl; try constructor;
    try apply IHSplitU; constructor.
Qed.

(** The converse relies on positions: with types alone two resources of the
    same type could not be told apart. *)
Lemma view_splitU : forall {A : Type} (L : list A) I U F n,
  wf_mask L I -> wf_mask L U -> wf_mask L F ->
  Split (view_from n L I) (view_from n L U) (view_from n L F) ->
  SplitU I U F.
Proof.
  unfold wf_mask. intros A L.
  induction L as [| x L IH]; intros [| i I] [| u U] [| f F] n HI HU HF H;
    simpl in *; try discriminate.
  - constructor.
  - injection HI as HI. injection HU as HU. injection HF as HF.
    assert (Hpos : forall U', ~ In (n, x) (view_from (S n) L U')).
    { intros U' Hin. apply view_from_pos in Hin. lia. }
    destruct i.
    + (* the position is available: it goes to exactly one side *)
      apply split_cons_inv in H.
      destruct H as [[ls' [Hls H]] | [rs' [Hrs H]]].
      * destruct u; simpl in Hls.
        2: { exfalso. eapply Hpos. rewrite Hls. left. reflexivity. }
        injection Hls as Hls; subst ls'. destruct f; simpl in H.
        { exfalso. eapply Hpos. eapply split_in; [exact H | right].
          left. reflexivity. }
        constructor. eapply IH; eassumption.
      * destruct f; simpl in Hrs.
        2: { exfalso. eapply Hpos. rewrite Hrs. left. reflexivity. }
        injection Hrs as Hrs; subst rs'. destruct u; simpl in H.
        { exfalso. eapply Hpos. eapply split_in; [exact H | left].
          left. reflexivity. }
        constructor. eapply IH; eassumption.
    + (* the position is unavailable in [I], hence in both parts *)
      destruct u; simpl in H.
      { exfalso. eapply Hpos. eapply split_in; [exact H | left].
        left. reflexivity. }
      destruct f; simpl in H.
      { exfalso. eapply Hpos. eapply split_in; [exact H | right].
        left. reflexivity. }
      constructor. eapply IH; eassumption.
Qed.
