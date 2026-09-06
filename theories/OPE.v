(** * Order-preserving embeddings as availability masks

    A mask [U : list bool] over a scope [L] selects the positions that are
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

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

Section OPE.
  Context {A : Type}.

  (** ** Masks as embeddings *)

  Inductive ope : list A -> list bool -> list A -> Prop :=
    | ope_nil : ope [] [] []
    | ope_drop : forall x L U G, ope L U G -> ope (x :: L) (false :: U) G
    | ope_keep : forall x L U G, ope L U G -> ope (x :: L) (true :: U) (x :: G).

  (** The elements selected by a mask: the available resource context. *)
  Fixpoint select (L : list A) (U : list bool) : list A :=
    match L, U with
    | x :: L', true :: U' => x :: select L' U'
    | _ :: L', false :: U' => select L' U'
    | _, _ => []
    end.

  (** Selected elements together with their positions in the full scope,
      counted from [n]. *)
  Fixpoint view_from (n : nat) (L : list A) (U : list bool) : list (nat * A) :=
    match L, U with
    | x :: L', true :: U' => (n, x) :: view_from (S n) L' U'
    | _ :: L', false :: U' => view_from (S n) L' U'
    | _, _ => []
    end.

  Definition view (L : list A) (U : list bool) : list (nat * A) :=
    view_from 0 L U.

  Definition wf_mask (L : list A) (U : list bool) : Prop :=
    length U = length L.

  Lemma ope_length : forall L U G, ope L U G -> wf_mask L U.
  Proof. unfold wf_mask. intros L U G H. induction H; simpl; auto. Qed.

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

  Definition mask_id (L : list A) : list bool := repeat true (length L).

  Lemma ope_id : forall L, ope L (mask_id L) L.
  Proof. induction L; simpl; constructor; assumption. Qed.

  (** [G] embeds into [x :: G] by dropping the new position. *)
  Definition mask_wk (G : list A) : list bool := false :: mask_id G.

  Lemma ope_wk : forall x G, ope (x :: G) (mask_wk G) G.
  Proof. intros. constructor. apply ope_id. Qed.

  (** [mask_comp U V] first restricts by [U], then by [V] inside the kept
      positions. The [true]-with-empty-[V] branch is unreachable for
      well-formed inputs and is chosen to drop the position. *)
  Fixpoint mask_comp (U V : list bool) : list bool :=
    match U with
    | [] => []
    | false :: U' => false :: mask_comp U' V
    | true :: U' =>
        match V with
        | v :: V' => v :: mask_comp U' V'
        | [] => false :: mask_comp U' []
        end
    end.

  Lemma ope_comp : forall L U G V H,
    ope L U G -> ope G V H -> ope L (mask_comp U V) H.
  Proof.
    intros L U G V H HU. revert V H.
    induction HU as [| x L U G HU IH | x L U G HU IH]; intros V H HV.
    - inversion HV; subst. constructor.
    - simpl. constructor. apply IH, HV.
    - inversion HV; subst; simpl; constructor; apply IH; assumption.
  Qed.

  Lemma mask_comp_id_l : forall L U G, ope L U G -> mask_comp (mask_id L) U = U.
  Proof. intros L U G H. induction H; simpl; f_equal; assumption. Qed.

  Lemma mask_comp_id_r : forall L U G, ope L U G -> mask_comp U (mask_id G) = U.
  Proof. intros L U G H. induction H; simpl; f_equal; assumption. Qed.

  Lemma mask_comp_assoc : forall L U G V H W,
    ope L U G -> ope G V H ->
    mask_comp (mask_comp U V) W = mask_comp U (mask_comp V W).
  Proof.
    intros L U G V H W HU. revert V H W.
    induction HU as [| x L U G HU IH | x L U G HU IH]; intros V H W HV.
    - reflexivity.
    - simpl. f_equal. eapply IH, HV.
    - inversion HV; subst; simpl.
      + f_equal. eapply IH; eassumption.
      + destruct W as [| w W]; simpl; f_equal; eapply IH; eassumption.
  Qed.

  (** ** Action on de Bruijn indices

      [ren U i] maps index [i] of the embedded scope to its index in the full
      scope: every dropped position in front of it shifts it by one. *)
  Fixpoint ren (U : list bool) (i : nat) : nat :=
    match U with
    | [] => i
    | true :: U' => match i with 0 => 0 | S i' => S (ren U' i') end
    | false :: U' => S (ren U' i)
    end.

  Lemma ren_nth : forall L U G i a,
    ope L U G -> nth_error G i = Some a -> nth_error L (ren U i) = Some a.
  Proof.
    intros L U G i a H. revert i.
    induction H as [| x L U G H IH | x L U G H IH]; intros i Hi; simpl.
    - destruct i; discriminate.
    - apply IH, Hi.
    - destruct i; simpl in *; [exact Hi | apply IH, Hi].
  Qed.

  Lemma ren_id : forall L i, ren (mask_id L) i = i.
  Proof.
    induction L as [| x L IH]; intros i; simpl.
    - reflexivity.
    - destruct i; simpl; [reflexivity | f_equal; apply IH].
  Qed.

  Lemma ren_comp : forall L U G V H i,
    ope L U G -> ope G V H -> ren (mask_comp U V) i = ren U (ren V i).
  Proof.
    intros L U G V H i HU. revert V H i.
    induction HU as [| x L U G HU IH | x L U G HU IH]; intros V H i HV.
    - inversion HV; subst. reflexivity.
    - simpl. f_equal. eapply IH, HV.
    - inversion HV; subst; simpl.
      + f_equal. eapply IH; eassumption.
      + destruct i; simpl; [reflexivity | f_equal; eapply IH; eassumption].
  Qed.

  (** TODO: the sub-mask order [F ≤ O] between leftovers and its reading as
      an embedding [view L F ↪ view L O]; renaming of terms along [ren] for
      the two zones. *)
End OPE.
