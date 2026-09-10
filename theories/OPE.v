(** * Order-preserving embeddings as availability masks

    A mask [U : mask] over a scope [L] selects the positions that are
    still available; consuming a resource flips its position to [false]
    without removing it from [L], so every other index keeps its meaning.

    Read as a relation, a mask is an order-preserving embedding (OPE, also
    called a thinning): [ope L U G] says that [U] embeds the sub-scope [G]
    into [L], [true] keeping a position and [false] dropping it. This is the
    same [drop]/[keep] shape as the OPEs of the normalization-by-evaluation
    development for System T; here the embedding is ordinary data, contexts
    are not indexed by it, and variables are plain de Bruijn numbers, so the
    category laws follow by direct induction.

    Positions are kept in [view] so that two resources of the same type
    remain distinguishable; this is what makes the correspondence between
    mask splitting and list splitting in [Split.v] exact. *)

From Stdlib Require Import List Arith Lia.
From DILLref Require Import Prelude Mask.
Import ListNotations.

Section OPE.
  Context {A : Type}.

  (** ** Masks as embeddings *)

  Inductive ope : list A -> mask -> list A -> Prop :=
    | OpeNil : ope [] [] []
    | OpeDrop : forall x L U G, ope L U G -> ope (x :: L) (false :: U) G
    | OpeKeep : forall x L U G, ope L U G -> ope (x :: L) (true :: U) (x :: G).

  (** The elements selected by a mask: the available resource context. *)
  Fixpoint select (L : list A) (U : mask) : list A :=
    match L, U with
    | x :: L', true :: U' => x :: select L' U'
    | _ :: L', false :: U' => select L' U'
    | _, _ => []
    end.

  (** Selected elements together with their positions in the full scope,
      counted from [n]. *)
  Fixpoint view_from (n : nat) (L : list A) (U : mask) : list (nat * A) :=
    match L, U with
    | x :: L', true :: U' => (n, x) :: view_from (S n) L' U'
    | _ :: L', false :: U' => view_from (S n) L' U'
    | _, _ => []
    end.

  Definition view (L : list A) (U : mask) : list (nat * A) :=
    view_from 0 L U.

  Lemma ope_length : forall L U G, ope L U G -> wf_mask L U.
  Proof. unfold wf_mask. intros L U G H. induction H; simpl; auto. Qed.

  Lemma ope_count : forall L U G, ope L U G -> mask_count U = length G.
  Proof. intros L U G H. induction H; simpl; congruence. Qed.

  Lemma ope_select : forall L U, wf_mask L U -> ope L U (select L U).
  Proof.
    unfold wf_mask. induction L as [| x L IH]; intros [| [|] U] H;
      simpl in *; try discriminate; constructor; apply IH; auto.
  Qed.

  Lemma ope_unique : forall L U G, ope L U G -> G = select L U.
  Proof. intros L U G H. induction H; simpl; subst; reflexivity. Qed.

  Lemma ope_iff : forall L U G, ope L U G <-> wf_mask L U /\ G = select L U.
  Proof.
    split.
    - intros H. split; [eapply ope_length | apply ope_unique]; eassumption.
    - intros [H ->]. apply ope_select, H.
  Qed.

  Lemma select_view : forall n L U, map snd (view_from n L U) = select L U.
  Proof.
    intros n L. revert n. induction L as [| x L IH]; intros n [| [|] U];
      simpl; auto. f_equal. apply IH.
  Qed.

  Lemma view_from_pos : forall n L U m x,
    In (m, x) (view_from n L U) -> n <= m.
  Proof.
    intros n L. revert n. induction L as [| y L IH]; intros n [| [|] U] m x H;
      simpl in H; try contradiction.
    - destruct H as [H | H].
      + injection H as -> ->. lia.
      + apply IH in H. lia.
    - apply IH in H. lia.
  Qed.

  (** ** Identity, weakening and composition *)

  Lemma ope_id : forall L, ope L (mask_id (length L)) L.
  Proof. induction L; simpl; constructor; assumption. Qed.

  (** [G] embeds into [x :: G] by dropping the new position. *)
  Lemma ope_wk : forall x G, ope (x :: G) (mask_wk (length G)) G.
  Proof. intros. constructor. apply ope_id. Qed.

  Lemma ope_comp : forall L U G V H,
    ope L U G -> ope G V H -> ope L (mask_comp U V) H.
  Proof.
    intros L U G V H HU. revert V H.
    induction HU as [| x L U G HU IH | x L U G HU IH]; intros V H HV.
    - inversion HV; subst. constructor.
    - simpl. constructor. apply IH, HV.
    - inversion HV; subst; simpl; constructor; apply IH; assumption.
  Qed.

  Lemma ope_comp_id_l : forall L U G,
    ope L U G -> mask_comp (mask_id (length L)) U = U.
  Proof.
    intros L U G H. pose proof (ope_length _ _ _ H) as Hlen.
    unfold wf_mask in Hlen. rewrite <- Hlen. apply mask_comp_id_l.
  Qed.

  Lemma ope_comp_id_r : forall L U G,
    ope L U G -> mask_comp U (mask_id (length G)) = U.
  Proof.
    intros L U G H. rewrite <- (ope_count _ _ _ H). apply mask_comp_id_r.
  Qed.

  Lemma ope_comp_assoc : forall L U G V H W,
    ope L U G -> ope G V H ->
    mask_comp (mask_comp U V) W = mask_comp U (mask_comp V W).
  Proof.
    intros L U G V H W HU HV. apply mask_comp_assoc.
    rewrite (ope_count _ _ _ HU). apply (ope_length _ _ _ HV).
  Qed.

  (** ** Action on de Bruijn indices

      [ope_index U i] maps index [i] of the embedded scope to its index in
      the full scope: every dropped position in front of it shifts it by
      one. *)
  Fixpoint ope_index (U : mask) (i : nat) : nat :=
    match U with
    | [] => i
    | true :: U' => match i with 0 => 0 | S i' => S (ope_index U' i') end
    | false :: U' => S (ope_index U' i)
    end.

  Lemma ope_index_nth : forall L U G i a,
    ope L U G -> In_opt a (nth_error G i) -> In_opt a (nth_error L (ope_index U i)).
  Proof.
    intros L U G i a H. revert i.
    induction H as [| x L U G H IH | x L U G H IH]; intros i Hi; simpl.
    - destruct i; simpl in Hi; contradiction.
    - apply IH, Hi.
    - destruct i; simpl in *; [exact Hi | apply IH, Hi].
  Qed.

  Lemma ope_index_id : forall n i, ope_index (mask_id n) i = i.
  Proof.
    induction n as [| n IH]; intros i; simpl.
    - reflexivity.
    - destruct i; simpl; [reflexivity | f_equal; apply IH].
  Qed.

  Lemma ope_index_comp : forall L U G V H i,
    ope L U G -> ope G V H -> ope_index (mask_comp U V) i = ope_index U (ope_index V i).
  Proof.
    intros L U G V H i HU. revert V H i.
    induction HU as [| x L U G HU IH | x L U G HU IH]; intros V H i HV.
    - inversion HV; subst. reflexivity.
    - simpl. f_equal. eapply IH, HV.
    - inversion HV; subst; simpl.
      + f_equal. eapply IH; eassumption.
      + destruct i; simpl; [reflexivity | f_equal; eapply IH; eassumption].
  Qed.

End OPE.

Section MaskViews.
  Context {A : Type}.

  Lemma mask_zero_view : forall (L : list A) n,
    view_from n L (mask_zero (length L)) = [].
  Proof. induction L; intros; simpl; auto. Qed.

  Lemma mask_le_view_from : forall U V,
    mask_le U V -> forall (L : list A) n, wf_mask L V ->
    exists W, ope (view_from n L V) W (view_from n L U).
  Proof.
    intros U V H. induction H; intros [| a L] n Hlen;
      unfold wf_mask in Hlen; simpl in Hlen; try discriminate.
    - exists []. constructor.
    - destruct (IHmask_le L (S n)) as [W HW]; [unfold wf_mask; lia | ].
      destruct b; simpl; [exists (false :: W); constructor | exists W]; auto.
    - destruct (IHmask_le L (S n)) as [W HW]; [unfold wf_mask; lia | ].
      exists (true :: W). simpl. constructor. exact HW.
  Qed.

  Lemma mask_le_view : forall (L : list A) U V,
    mask_le U V -> wf_mask L V -> exists W, ope (view L V) W (view L U).
  Proof. intros. eapply mask_le_view_from; eassumption. Qed.
End MaskViews.

(** Transport of usage masks through an embedding of the full scope. *)
Lemma ope_mask_zero : forall {A : Type} (L : list A) E K,
  ope L E K -> mask_comp E (mask_zero (length K)) = mask_zero (length L).
Proof. intros A L E K H. induction H; unfold mask_zero in *; simpl; congruence. Qed.

Lemma ope_mask_single : forall {A : Type} (L : list A) E K i,
  ope L E K -> Is_some (nth_error K i) ->
  mask_comp E (mask_single (length K) i) = mask_single (length L) (ope_index E i).
Proof.
  intros A L E K i H Hsome. apply Is_some_exists in Hsome.
  destruct Hsome as [a Hi]. revert i a Hi.
  induction H; intros [| i] a Hi; simpl in *; try contradiction; f_equal; eauto.
  apply ope_mask_zero, H.
Qed.

Lemma ope_splitM : forall {A : Type} (L : list A) E K,
  ope L E K -> forall I U F, SplitM I U F -> wf_mask K I ->
  SplitM (mask_comp E I) (mask_comp E U) (mask_comp E F).
Proof.
  intros A L E K H. induction H as [| x L E K H IH | x L E K H IH]; intros I U F Hs Hw.
  - unfold wf_mask in Hw. simpl in Hw. destruct I; try discriminate.
    inversion Hs; constructor.
  - simpl. constructor. eapply IH; eassumption.
  - inversion Hs; subst; unfold wf_mask in Hw; simpl in Hw; try discriminate;
      simpl; constructor; eapply IH; eauto; unfold wf_mask; lia.
Qed.

Lemma ope_mask_le : forall {A : Type} (L : list A) E K,
  ope L E K -> forall U V, mask_le U V -> wf_mask K U ->
  mask_le (mask_comp E U) (mask_comp E V).
Proof.
  intros A L E K H. induction H as [| x L E K H IH | x L E K H IH]; intros U V Hle Hw.
  - unfold wf_mask in Hw. simpl in Hw. destruct U; try discriminate.
    inversion Hle; constructor.
  - simpl. constructor. eapply IH; eassumption.
  - inversion Hle; subst; unfold wf_mask in Hw; simpl in Hw; try discriminate;
      simpl; constructor; eapply IH; eauto; unfold wf_mask; lia.
Qed.
