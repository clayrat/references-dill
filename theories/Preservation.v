(** * Preservation of store balance

    Location ownership is represented by signature fragments divided with
    [Split]. Allocation, strong update and deallocation therefore transform
    keyed contexts directly; no positional address masks cross store edits. *)

From Stdlib Require Import List Bool Arith Lia.
From DILLref Require Import Prelude Ty Syntax Index Mask Split Scoping Renaming Substitution.
From DILLref Require Import NatMap Store Semantics StoreTyping StoreTypingInversion.
From DILLref Require Import StoreTypingSubst EvaluationContext.
Import ListNotations.
Local Opaque split_incl.

(** ** Pure redexes *)


Lemma pure_redex_preservation_small : forall f R e e' a,
  pure_redex e e' -> has_type_with_loc f [] [] [] R e a ->
  exists Q,
    (f = Linear -> Q = R) /\ split_incl Q R /\
    has_type_with_loc f [] [] [] Q e' a.
Proof.
  intros f R e e' a Hred Htype.
  destruct (has_type_with_loc_generation_closed _ _ _ _ _ Htype)
    as [R0 [Hlinear [HR0 Hhead]]].
  destruct Hred; cbn [has_type_with_loc_head] in Hhead.
  - destruct Hhead as [U1 [U2 [R1 [R2 [b [HU [HR [Hfun Harg]]]]]]]].
    apply splitM_nil_inv in HU. destruct HU as [-> ->].
    destruct (has_type_with_loc_generation_closed _ _ _ _ _ Hfun)
      as [Qf [Hfunlin [HQf Hfunhead]]].
    cbn [has_type_with_loc_head] in Hfunhead.
    destruct Hfunhead as [c [Heq Hbody]]. inversion Heq; subst.
    destruct HQf as [F HF].
    destruct (split_interchange _ _ _ _ _ _ _ HR HF (split_left R2))
      as [P [D [HR0P [HP HD]]]].
    apply split_left_inv in HD. subst D.
    exists P. repeat split.
    + intros Hf. specialize (Hlinear Hf). subst R0.
      specialize (Hfunlin Hf). subst Qf.
      apply split_same_left_inv in HF. subst F.
      apply split_left_inv in HR0P. exact HR0P.
    + eapply split_incl_left_trans; eassumption.
    + eapply has_type_with_loc_subst_l; [exact Hbody | exact Harg | constructor | exact HP].
  - destruct Hhead as [U1 [U2 [R1 [R2 [HU [HR [Hunit Hbody]]]]]]].
    apply splitM_nil_inv in HU. destruct HU as [-> ->].
    destruct (has_type_with_loc_generation_closed _ _ _ _ _ Hunit)
      as [Qu [Hunitlin [HQu Hunithead]]].
    cbn [has_type_with_loc_head] in Hunithead. destruct Hunithead as [_ [_ ->]].
    exists R2. repeat split.
    + intros Hf. specialize (Hlinear Hf). subst R0.
      specialize (Hunitlin Hf). subst R1.
      apply split_right_inv. exact HR.
    + eapply split_incl_right_trans; eassumption.
    + exact Hbody.
  - destruct Hhead as [U1 [U2 [Rp [Rb [b [c [HU [HR [Hp Hb]]]]]]]]].
    apply splitM_nil_inv in HU. destruct HU as [-> ->].
    destruct (has_type_with_loc_generation_closed _ _ _ _ _ Hp)
      as [Qp [Hplin [HQp Hphead]]].
    cbn [has_type_with_loc_head] in Hphead.
    destruct Hphead as [Up1 [Up2 [Rv1 [Rv2 [d [g
      [Heq [HUp [HRp [Hv1 Hv2]]]]]]]]]].
    injection Heq as Ed Eg. subst d g.
    apply splitM_nil_inv in HUp. destruct HUp as [-> ->].
    destruct HQp as [D HD].
    destruct (split_interchange _ _ _ _ _ _ _ HR HD (split_left Rb))
      as [P [unused [HR0P [HP HDrop]]]].
    apply split_left_inv in HDrop. subst unused.
    destruct (split_assoc _ _ _ _ _ HP HRp) as [Tail [Hfirst Htail]].
    exists P. repeat split.
    + intros Hf. specialize (Hlinear Hf). subst R0.
      specialize (Hplin Hf). subst Qp.
      apply split_same_left_inv in HD. subst D.
      apply split_left_inv in HR0P. exact HR0P.
    + eapply split_incl_left_trans; eassumption.
    + assert (Hclosed : scoped 0 0 v2).
      { change (scoped (length ([] : list ty)) (length ([] : list ty)) v2).
        eapply has_type_with_loc_scoped; exact Hv2. }
      pose proof (has_type_with_loc_weaken_resource
        f [] [] [] Rv2 v2 c b Hv2) as Hweaken.
      simpl in Hweaken.
      assert (Erename : rename id_ren Nat.succ v2 = v2).
      { apply rename_scoped_identity with (g := 0) (l := 0).
        - exact Hclosed.
        - reflexivity.
        - intros; lia. }
      rewrite Erename in Hweaken.
      assert (Hsub2 : has_type_with_loc f [] [b] [true] Tail
          (subst_l v2 body) a).
      { eapply has_type_with_loc_subst_l with
          (G := []) (L := [b]) (U := [true]) (V := [false]) (W := [true])
          (a := c) (Rbody := Rb) (Rarg := Rv2) (R := Tail).
        - exact Hb.
        - exact Hweaken.
        - repeat constructor.
        - apply split_comm. exact Htail. }
      eapply has_type_with_loc_subst_l with
        (G := []) (L := []) (U := []) (V := []) (W := [])
        (a := b) (Rbody := Tail) (Rarg := Rv1) (R := P).
      * exact Hsub2.
      * exact Hv1.
      * constructor.
      * apply split_comm. exact Hfirst.
  - destruct Hhead as [b Hwith].
    destruct (has_type_with_loc_generation_closed _ _ _ _ _ Hwith)
      as [Qw [Hwlin [HQw Hwhead]]].
    cbn [has_type_with_loc_head] in Hwhead.
    destruct Hwhead as [c [d [Heq [He1 He2]]]]. inversion Heq; subst.
    exists Qw. repeat split.
    + intros Hf. specialize (Hlinear Hf). subst R0. apply Hwlin. exact Hf.
    + eapply split_incl_trans; eassumption.
    + exact He1.
  - destruct Hhead as [b Hwith].
    destruct (has_type_with_loc_generation_closed _ _ _ _ _ Hwith)
      as [Qw [Hwlin [HQw Hwhead]]].
    cbn [has_type_with_loc_head] in Hwhead.
    destruct Hwhead as [c [d [Heq [He1 He2]]]]. inversion Heq; subst.
    exists Qw. repeat split.
    + intros Hf. specialize (Hlinear Hf). subst R0. apply Hwlin. exact Hf.
    + eapply split_incl_trans; eassumption.
    + exact He2.
  - destruct Hhead as [U1 [U2 [R1 [R2 [b [HU [HR [Hbang Hbody]]]]]]]].
    apply splitM_nil_inv in HU. destruct HU as [-> ->].
    destruct (has_type_with_loc_generation_closed _ _ _ _ _ Hbang)
      as [Qb [Hblin [HQb Hbhead]]].
    cbn [has_type_with_loc_head] in Hbhead.
    destruct Hbhead as [c [Heq [_ [E Hsuspended]]]]. inversion Heq; subst.
    exists R2. repeat split.
    + intros Hf. specialize (Hlinear Hf). subst R0.
      specialize (Hblin Hf). subst R1.
      apply split_right_inv. exact HR.
    + eapply split_incl_right_trans; eassumption.
    + eapply has_type_with_loc_subst_u; eassumption.
  - destruct Hhead as [-> Hnat].
    destruct (has_type_with_loc_generation_closed _ _ _ _ _ Hnat)
      as [Qn [Hnlin [HQn Hnhead]]].
    cbn [has_type_with_loc_head] in Hnhead. destruct Hnhead as [_ [_ ->]].
    exists []. repeat split.
    + intros Hf. specialize (Hlinear Hf). subst R0.
      apply Hnlin. exact Hf.
    + eapply split_incl_trans; eassumption.
    + apply TyLocNat.
  - destruct Hhead as [Uc [Ur [Us [Uz [Rc [Rr [Rs [Rz
      [HU1 [HU2 [HR1 [HR2 [Hcount [Hstep Hseed]]]]]]]]]]]]]].
    apply splitM_nil_inv in HU1. destruct HU1 as [-> ->].
    apply splitM_nil_inv in HU2. destruct HU2 as [-> ->].
    destruct (has_type_with_loc_generation_closed _ _ _ _ _ Hcount)
      as [Qc [Hclin [HQc Hchead]]].
    cbn [has_type_with_loc_head] in Hchead. destruct Hchead as [_ [_ ->]].
    destruct (has_type_with_loc_generation_closed _ _ _ _ _ Hstep)
      as [Qs [Hslin [HQs Hshead]]].
    cbn [has_type_with_loc_head] in Hshead.
    destruct Hshead as [step_ty [Heq [_ [E Hstepbody]]]]. inversion Heq; subst.
    exists Rz. repeat split.
    + intros Hf. specialize (Hlinear Hf). subst R0.
      specialize (Hclin Hf). subst Rc.
      specialize (Hslin Hf). subst Rs.
      apply split_right_inv in HR1. subst Rr.
      apply split_right_inv in HR2. exact HR2.
    + eapply split_incl_right_trans; [exact HR2 | ].
      eapply split_incl_right_trans; eassumption.
    + exact Hseed.
  - destruct Hhead as [Uc [Ur [Us [Uz [Rc [Rr [Rs [Rz
      [HU1 [HU2 [HR1 [HR2 [Hcount [Hstep Hseed]]]]]]]]]]]]]].
    apply splitM_nil_inv in HU1. destruct HU1 as [-> ->].
    apply splitM_nil_inv in HU2. destruct HU2 as [-> ->].
    destruct (has_type_with_loc_generation_closed _ _ _ _ _ Hcount)
      as [Qc [Hclin [HQc Hchead]]].
    cbn [has_type_with_loc_head] in Hchead. destruct Hchead as [_ [_ ->]].
    destruct (has_type_with_loc_generation_closed _ _ _ _ _ Hstep)
      as [Qs [Hslin [HQs Hshead]]].
    cbn [has_type_with_loc_head] in Hshead.
    destruct Hshead as [step_ty [Heq [_ [E Hstepbody]]]]. inversion Heq; subst.
    exists Rz. repeat split.
    + intros Hf. specialize (Hlinear Hf). subst R0.
      specialize (Hclin Hf). subst Rc.
      specialize (Hslin Hf). subst Rs.
      apply split_right_inv in HR1. subst Rr.
      apply split_right_inv in HR2. exact HR2.
    + eapply split_incl_right_trans; [exact HR2 | ].
      eapply split_incl_right_trans; eassumption.
    + eapply TyLocIter with (Uc := []) (Ur := []) (Us := []) (Uz := [])
        (Rc := []) (Rr := Rz) (Rs := []) (Rz := Rz).
      * constructor.
      * constructor.
      * apply split_right.
      * apply split_right.
      * apply TyLocNat.
      * apply TyLocBang. exact Hstepbody.
      * eapply TyLocApp with (U1 := []) (U2 := []) (R1 := []) (R2 := Rz).
        -- constructor.
        -- apply split_right.
        -- exact Hstepbody.
        -- exact Hseed.
  - destruct Hhead as [Uc [Ub [Rc [Rb [HU [HR [Hcond [He1 He2]]]]]]]].
    apply splitM_nil_inv in HU. destruct HU as [-> ->].
    destruct (has_type_with_loc_generation_closed _ _ _ _ _ Hcond)
      as [Qc [Hclin [HQc Hchead]]].
    cbn [has_type_with_loc_head] in Hchead. destruct Hchead as [_ [_ ->]].
    exists Rb. repeat split.
    + intros Hf. specialize (Hlinear Hf). subst R0.
      specialize (Hclin Hf). subst Rc.
      apply split_right_inv. exact HR.
    + eapply split_incl_right_trans; eassumption.
    + exact He1.
  - destruct Hhead as [Uc [Ub [Rc [Rb [HU [HR [Hcond [He1 He2]]]]]]]].
    apply splitM_nil_inv in HU. destruct HU as [-> ->].
    destruct (has_type_with_loc_generation_closed _ _ _ _ _ Hcond)
      as [Qc [Hclin [HQc Hchead]]].
    cbn [has_type_with_loc_head] in Hchead. destruct Hchead as [_ [_ ->]].
    exists Rb. repeat split.
    + intros Hf. specialize (Hlinear Hf). subst R0.
      specialize (Hclin Hf). subst Rc.
      apply split_right_inv. exact HR.
    + eapply split_incl_right_trans; eassumption.
    + exact He2.
Qed.

Lemma pure_redex_preservation : forall f R e e' a,
  pure_redex e e' -> has_type_with_loc f [] [] [] R e a ->
  has_type_with_loc f [] [] [] R e' a.
Proof.
  intros f R e e' a Hred Htype.
  destruct (pure_redex_preservation_small _ _ _ _ _ Hred Htype)
    as [Q [Hlinear [HQ Hresult]]].
  destruct f.
  - specialize (Hlinear eq_refl). subst Q. exact Hresult.
  - eapply TyLocWeak; [exact Hresult | apply mask_le_refl | exact HQ].
Qed.

(** ** Resource frames *)

Inductive frame_change : flag -> store_sig -> store_sig -> Prop :=
  | FrameLinear : forall F, frame_change Linear F F
  | FrameAffine : forall F F',
      split_incl F F' -> frame_change Affine F F'.

Lemma frame_change_refl : forall f F, frame_change f F F.
Proof. destruct f; constructor; apply split_incl_refl. Qed.

Lemma frame_change_split : forall f Whole Whole' Part Frame,
  frame_change f Whole Whole' -> Split Whole Part Frame ->
  exists Frame', Split Whole' Part Frame' /\ frame_change f Frame Frame'.
Proof.
  intros f Whole Whole' Part Frame Hchange Hsplit. destruct Hchange.
  - exists Frame. split; [exact Hsplit | constructor].
  - destruct H as [Extra Hinclude].
    destruct (split_assoc _ _ _ _ _ Hinclude Hsplit)
      as [Frame' [Hwhole Hframe]].
    exists Frame'. split; [exact Hwhole | constructor].
    eapply split_incl_left. exact Hframe.
Qed.

Lemma focus_partition : forall (Full Joint Term Cells Frame Active Sibling : store_sig),
  Split Full Joint Frame -> Split Joint Term Cells ->
  Split Term Active Sibling ->
  exists Focus Outer,
    Split Focus Active Cells /\ Split Full Focus Outer /\
    Split Outer Sibling Frame.
Proof.
  intros Full Joint Term Cells Frame Active Sibling Hfull Hjoint Hterm.
  destruct (split_interchange _ _ _ _ _ _ _ Hjoint Hterm (split_left Cells))
    as [Focus [Discard [Hwithin [Hfocus Hdiscard]]]].
  apply split_left_inv in Hdiscard. subst Discard.
  destruct (split_assoc _ _ _ _ _ Hfull Hwithin)
    as [Outer [Houter Hparts]].
  exists Focus, Outer. repeat split; assumption.
Qed.

Lemma unfocus_partition : forall (Full Focus Outer Active Cells Sibling Frame : store_sig),
  Split Full Focus Outer -> Split Focus Active Cells ->
  Split Outer Sibling Frame ->
  exists Term Joint,
    Split Term Active Sibling /\ Split Joint Term Cells /\
    Split Full Joint Frame.
Proof.
  intros Full Focus Outer Active Cells Sibling Frame Hfull Hfocus Houter.
  destruct (split_interchange _ _ _ _ _ _ _ Hfull Hfocus Houter)
    as [Term [Rest [Htop [Hterm Hrest]]]].
  destruct (split_unassoc _ _ _ _ _ Htop Hrest)
    as [Joint [Hjoint Hparts]].
  exists Term, Joint. repeat split; assumption.
Qed.

Definition joint_typed (f : flag) (S : store_sig) (s : store)
    (e : term) (a : ty) (R C J F : store_sig) : Prop :=
  NoDup (natmap_domain S) /\ cells_typed f S s C /\
  has_type_with_loc f [] [] [] R e a /\
  Split J R C /\ Split S J F.

Definition joint_preservation_result (f : flag) (F : store_sig)
    (s : store) (e : term) (a : ty) : Prop :=
  exists S R C J F',
    joint_typed f S s e a R C J F' /\ frame_change f F F'.

Lemma pure_joint_preservation : forall f S s e e' a R C J F,
  pure_redex e e' -> joint_typed f S s e a R C J F ->
  joint_preservation_result f F s e' a.
Proof.
  intros f S s e e' a R C J F Hred
    [Hnd [Hcells [Htype [Hjoint Hfull]]]].
  exists S, R, C, J, F. split.
  - repeat split; eauto using pure_redex_preservation.
  - apply frame_change_refl.
Qed.

Lemma normalize_joint_head : forall f S s e a R C J F,
  joint_typed f S s e a R C J F ->
  exists Q J0 F0,
    has_type_with_loc_head f [] [] [] Q e a /\
    Split J0 Q C /\ Split S J0 F0 /\
    (forall s' e', joint_preservation_result f F0 s' e' a ->
      joint_preservation_result f F s' e' a).
Proof.
  intros f S s e a R C J F
    [Hnd [Hcells [Htype [Hjoint Hfull]]]].
  destruct (has_type_with_loc_generation_closed _ _ _ _ _ Htype)
    as [Q [Hlinear [HQ Hhead]]].
  destruct HQ as [unused HQ].
  destruct (split_interchange _ _ _ _ _ _ _ Hjoint HQ (split_left C))
    as [J0 [D [HJ [HJ0 HD]]]].
  apply split_left_inv in HD. subst D.
  destruct (split_assoc _ _ _ _ _ Hfull HJ) as [F0 [HS HF0]].
  exists Q, J0, F0. repeat split; try assumption.
  intros s' e' [T [Q' [C' [J' [F0'
    [[Hnd' [Hcells' [Htype' [Hjoint' Hfull']]]] Hchange]]]]]].
  destruct (frame_change_split _ _ _ _ _ Hchange HF0)
    as [F' [HF0' Hframe]].
  destruct (unfocus_partition _ _ _ _ _ _ _ Hfull' Hjoint' HF0')
    as [R' [Jout [HR' [HJout HT]]]].
  assert (Htypedout : has_type_with_loc f [] [] [] R' e' a).
  { destruct f.
    - specialize (Hlinear eq_refl). subst Q.
      apply split_same_left_inv in HQ. subst unused.
      apply split_left_inv in HR'. subst R'. exact Htype'.
    - eapply TyLocWeak; [exact Htype' | apply mask_le_refl | ].
      eapply split_incl_left. exact HR'. }
  exists T, R', C', Jout, F'. split.
  - split; [exact Hnd' | ]. split; [exact Hcells' | ].
    split; [exact Htypedout | ]. split; [exact HJout | exact HT].
  - exact Hframe.
Qed.

Local Ltac normalize_joint Htyped :=
  destruct (normalize_joint_head _ _ _ _ _ _ _ _ _ Htyped)
    as [Q [J0 [F0 [Hhead [Hjoint [Hfull Hrestore]]]]]].

(** A context step isolates the active child from both the cell owners and
    the inactive child.  The induction hypothesis may change the active
    fragment and the store signature; [Split] then puts the unchanged sibling
    back without transporting it through an ambient positional mask. *)
Lemma focused_joint_preservation : forall
    f S s s' active' wrapped active_ty result_ty
    Active Sibling Term Cells Joint Frame,
  NoDup (natmap_domain S) -> cells_typed f S s Cells ->
  Split Term Active Sibling -> Split Joint Term Cells -> Split S Joint Frame ->
  (forall Focus Outer,
    Split Focus Active Cells -> Split S Focus Outer ->
    joint_preservation_result f Outer s' active' active_ty) ->
  (forall Active' Term',
    has_type_with_loc f [] [] [] Active' active' active_ty ->
    Split Term' Active' Sibling ->
    has_type_with_loc f [] [] [] Term' wrapped result_ty) ->
  joint_preservation_result f Frame s' wrapped result_ty.
Proof.
  intros f S s s' active' wrapped active_ty result_ty
    Active Sibling Term Cells Joint Frame Hnd Hcells
    Hterm Hjoint Hfull Hstep Hwrap.
  destruct (focus_partition _ _ _ _ _ _ _ Hfull Hjoint Hterm)
    as [Focus [Outer [Hfocus [Htop Houter]]]].
  destruct (Hstep Focus Outer Hfocus Htop)
    as [S' [Active' [Cells' [Focus' [Outer'
      [[Hnd' [Hcells' [Hactive' [Hfocus' Hfull']]]] Hchange]]]]]].
  destruct (frame_change_split _ _ _ _ _ Hchange Houter)
    as [Frame' [Houter' Hframe]].
  destruct (unfocus_partition _ _ _ _ _ _ _ Hfull' Hfocus' Houter')
    as [Term' [Joint' [Hterm' [Hjoint' Htop']]]].
  exists S', Term', Cells', Joint', Frame'. split.
  - split; [exact Hnd' | ]. split; [exact Hcells' | ].
    split; [eapply Hwrap; eassumption | ].
    split; [exact Hjoint' | exact Htop'].
  - exact Hframe.
Qed.

(** Allocation moves the value's ownership from the term partition into a
    fresh cell.  The new location becomes the sole owner in the result term. *)
Lemma new_value_joint_preservation : forall f S s v a R C J F,
  value v -> joint_typed f S s (New v) (TRef a) R C J F ->
  joint_preservation_result f F
    (store_insert (fresh s) v s) (Loc (fresh s)) (TRef a).
Proof.
  intros f S s v a R C J F Hvalue Htyped.
  normalize_joint Htyped.
  destruct Htyped as [Hnd [Hcells _]].
  cbn [has_type_with_loc_head] in Hhead.
  destruct Hhead as [b [Heq Hvalue_typed]]. inversion Heq; subst b.
  assert (Hfresh : ~ In (fresh s) (natmap_domain S)).
  { rewrite (cells_typed_domain _ _ _ _ Hcells). apply fresh_not_allocated. }
  apply Hrestore.
  exists (store_sig_insert (fresh s) a S), [(fresh s, a)], J0,
    ((fresh s, a) :: J0), F0. split.
  - split.
    + apply natmap_insert_nodup. exact Hfresh. exact Hnd.
    + split.
      * eapply CellsCons; eassumption.
      * split.
        { constructor. }
        split.
        { apply SplitL. apply split_right. }
        { apply SplitL. exact Hfull. }
  - apply frame_change_refl.
Qed.

(** Strong update changes the type attached to the selected key in every
    enclosing partition.  Disjointness shows that the cell payload, the old
    payload returned by [swap], and the external frame do not contain that
    key, so their fragments remain literally unchanged. *)
Lemma swap_value_joint_preservation : forall f S s l v old a b R C J F,
  value v -> In_opt old (natmap_lookup l s) ->
  joint_typed f S s (Swap (Loc l) v) (TTensor a (TRef b)) R C J F ->
  joint_preservation_result f F (store_update l v s)
    (Pair old (Loc l)) (TTensor a (TRef b)).
Proof.
  intros f S s l v old a b R C J F Hvalue Hlookup Htyped.
  normalize_joint Htyped.
  destruct Htyped as [Hnd [Hcells _]].
  cbn [has_type_with_loc_head] in Hhead.
  destruct Hhead as [U1 [U2 [Rloc [Rv [a0 [b0 Hhead]]]]]].
  destruct Hhead as [Heq [HU [HR [Hloc Hnew]]]].
  inversion Heq; subst a0 b0. apply splitM_nil_inv in HU as [-> ->].

  destruct (has_type_with_loc_generation_closed _ _ _ _ _ Hloc)
    as [Qloc [Hloc_linear [HQloc Hloc_head]]].
  cbn [has_type_with_loc_head] in Hloc_head.
  destruct Hloc_head as [a0 [HeqLoc [_ EQloc]]].
  inversion HeqLoc; subst a0. subst Qloc.
  destruct HQloc as [Lframe Hloc_part].
  assert (Hloc_frame_linear : f = Linear -> Lframe = []).
  { intros Hf. specialize (Hloc_linear Hf). subst Rloc.
    apply split_same_left_inv in Hloc_part. exact Hloc_part. }

  assert (HinRloc : In (l, a) Rloc).
  { eapply split_in; [exact Hloc_part | left; simpl; auto]. }
  assert (HinQ : In (l, a) Q).
  { eapply split_in; [exact HR | left; exact HinRloc]. }
  assert (HinJ : In (l, a) J0).
  { eapply split_in; [exact Hjoint | left; exact HinQ]. }
  assert (HinS : In (l, a) S).
  { eapply split_in; [exact Hfull | left; exact HinJ]. }
  apply In_nth_error in HinS as [i Hi].
  assert (Hsig : In_opt (l, a) (nth_error S i)).
  { apply Some_In_opt. exact Hi. }
  destruct (cells_typed_nth _ _ _ _ _ _ _ Hcells Hsig)
    as [stored Hstored].
  assert (Hstore_nd : NoDup (natmap_domain s)).
  { rewrite <- (cells_typed_domain _ _ _ _ Hcells). exact Hnd. }
  assert (Hstored_in : In (l, stored) s).
  { eapply nth_error_In with (n := i).
    apply In_opt_eq_Some in Hstored. exact Hstored. }
  assert (stored = old).
  { eapply natmap_lookup_member_unique; eassumption. }
  subst stored.
  destruct (cells_typed_replace _ _ _ _ _ _ _ _ _ _ _
      Hnd Hcells Hsig Hstored Hvalue Hnew)
    as [W [Other [Hold [Hold_typed [HC Hcells_update]]]]].

  destruct (split_interchange _ _ _ _ _ _ _ Hjoint HR HC)
    as [Term0 [Cells0 [HJ0 [HTerm HCells]]]].
  assert (HinRloc_dom : In l (natmap_domain Rloc)).
  { apply (in_map fst) in HinRloc. exact HinRloc. }
  assert (HinTerm_dom : In l (natmap_domain Term0)).
  { eapply split_domain_left; eassumption. }
  assert (HinJ_dom : In l (natmap_domain J0)).
  { eapply split_domain_left; eassumption. }
  assert (HndJ : NoDup (natmap_domain J0)).
  { eapply split_nodup_left; [apply split_map with (f := fst) in Hfull;
      exact Hfull | exact Hnd]. }
  assert (HndTerm : NoDup (natmap_domain Term0)).
  { eapply split_nodup_left; [apply split_map with (f := fst) in HJ0;
      exact HJ0 | exact HndJ]. }
  assert (HndRloc : NoDup (natmap_domain Rloc)).
  { eapply split_nodup_left; [apply split_map with (f := fst) in HTerm;
      exact HTerm | exact HndTerm]. }
  assert (HnotCells : ~ In l (natmap_domain Cells0)).
  { eapply split_domain_disjoint; eassumption. }
  assert (HnotFrame : ~ In l (natmap_domain F0)).
  { eapply split_domain_disjoint; eassumption. }
  assert (HnotW : ~ In l (natmap_domain W)).
  { eapply split_domain_disjoint; eassumption. }
  assert (HnotLframe : ~ In l (natmap_domain Lframe)).
  { eapply split_domain_disjoint; [exact Hloc_part | exact HndRloc | ].
    simpl. auto. }

  pose proof (split_store_sig_update l b _ _ _ HJ0) as HJ_update.
  rewrite (store_sig_update_absent l b Cells0 HnotCells) in HJ_update.
  pose proof (split_store_sig_update l b _ _ _ Hfull) as Hfull_update.
  rewrite (store_sig_update_absent l b F0 HnotFrame) in Hfull_update.
  pose proof (split_store_sig_update l b _ _ _ HTerm) as Hterm_update.
  rewrite (store_sig_update_absent l b W HnotW) in Hterm_update.
  pose proof (split_store_sig_update l b _ _ _ Hloc_part) as Hloc_update.
  rewrite store_sig_update_single,
    (store_sig_update_absent l b Lframe HnotLframe) in Hloc_update.
  destruct (split_interchange _ _ _ _ _ _ _ Hterm_update Hloc_update
      (split_left W))
    as [PairCtx [Rest [Hterm_result [Hpair Hrest]]]].
  apply split_left_inv in Hrest. subst Rest.
  assert (Hpair_typed : has_type_with_loc f [] [] [] PairCtx
      (Pair old (Loc l)) (TTensor a (TRef b))).
  { eapply TyLocPair.
    - constructor.
    - apply split_comm. exact Hpair.
    - exact Hold_typed.
    - constructor. }
  assert (Hterm_typed : has_type_with_loc f [] [] []
      (store_sig_update l b Term0) (Pair old (Loc l))
      (TTensor a (TRef b))).
  { destruct f.
    - specialize (Hloc_frame_linear eq_refl). subst Lframe.
      apply split_left_inv in Hterm_result. subst PairCtx. exact Hpair_typed.
    - eapply TyLocWeak; [exact Hpair_typed | apply mask_le_refl | ].
      eapply split_incl_left. exact Hterm_result. }
  apply Hrestore.
  exists (store_sig_update l b S), (store_sig_update l b Term0), Cells0,
    (store_sig_update l b J0), F0. split.
  - split.
    + rewrite store_sig_update_domain. exact Hnd.
    + split.
      * apply Hcells_update. exact HCells.
      * split; [exact Hterm_typed | ].
        split; [exact HJ_update | exact Hfull_update].
  - apply frame_change_refl.
Qed.

(** Deallocation removes the selected key.  Resources owned by the discarded
    unit payload become part of the affine frame; linear typing forces that
    payload fragment to be empty. *)
Lemma free_loc_joint_preservation : forall f S s l R C J F,
  In_opt Unit (natmap_lookup l s) ->
  joint_typed f S s (Free (Loc l)) TUnit R C J F ->
  joint_preservation_result f F (store_remove l s) Unit TUnit.
Proof.
  intros f S s l R C J F Hlookup Htyped.
  normalize_joint Htyped.
  destruct Htyped as [Hnd [Hcells _]].
  cbn [has_type_with_loc_head] in Hhead.
  destruct Hhead as [_ Hloc].
  destruct (has_type_with_loc_generation_closed _ _ _ _ _ Hloc)
    as [Qloc [Hloc_linear [HQloc Hloc_head]]].
  cbn [has_type_with_loc_head] in Hloc_head.
  destruct Hloc_head as [a0 [Heq [_ EQloc]]].
  inversion Heq; subst a0. subst Qloc.
  destruct HQloc as [Lframe Hloc_part].
  assert (Hloc_frame_linear : f = Linear -> Lframe = []).
  { intros Hf. specialize (Hloc_linear Hf). subst Q.
    apply split_same_left_inv in Hloc_part. exact Hloc_part. }

  assert (HinQ : In (l, TUnit) Q).
  { eapply split_in; [exact Hloc_part | left; simpl; auto]. }
  assert (HinJ : In (l, TUnit) J0).
  { eapply split_in; [exact Hjoint | left; exact HinQ]. }
  assert (HinS : In (l, TUnit) S).
  { eapply split_in; [exact Hfull | left; exact HinJ]. }
  apply In_nth_error in HinS as [i Hi].
  assert (Hsig : In_opt (l, TUnit) (nth_error S i)).
  { apply Some_In_opt. exact Hi. }
  destruct (cells_typed_nth _ _ _ _ _ _ _ Hcells Hsig)
    as [stored Hstored].
  assert (Hstore_nd : NoDup (natmap_domain s)).
  { rewrite <- (cells_typed_domain _ _ _ _ Hcells). exact Hnd. }
  assert (Hstored_in : In (l, stored) s).
  { eapply nth_error_In with (n := i).
    apply In_opt_eq_Some in Hstored. exact Hstored. }
  assert (stored = Unit).
  { eapply natmap_lookup_member_unique; eassumption. }
  subst stored.
  destruct (cells_typed_remove _ _ _ _ _ _ Hnd Hcells Hsig Hstored)
    as [W [Other [Hunit [HC Hcells_remove]]]].

  assert (HinQ_dom : In l (natmap_domain Q)).
  { apply (in_map fst) in HinQ. exact HinQ. }
  assert (HinJ_dom : In l (natmap_domain J0)).
  { eapply split_domain_left; eassumption. }
  assert (HndJ : NoDup (natmap_domain J0)).
  { eapply split_nodup_left; [apply split_map with (f := fst) in Hfull;
      exact Hfull | exact Hnd]. }
  assert (HndQ : NoDup (natmap_domain Q)).
  { eapply split_nodup_left; [apply split_map with (f := fst) in Hjoint;
      exact Hjoint | exact HndJ]. }
  assert (HnotC : ~ In l (natmap_domain C)).
  { eapply split_domain_disjoint; eassumption. }
  assert (HnotF : ~ In l (natmap_domain F0)).
  { eapply split_domain_disjoint; eassumption. }
  assert (HnotLframe : ~ In l (natmap_domain Lframe)).
  { eapply split_domain_disjoint; [exact Hloc_part | exact HndQ | ].
    simpl. auto. }

  pose proof (split_store_sig_remove l _ _ _ Hloc_part) as Hloc_remove.
  rewrite store_sig_remove_single,
    (store_sig_remove_absent l Lframe HnotLframe) in Hloc_remove.
  apply split_right_inv in Hloc_remove.
  pose proof (split_store_sig_remove l _ _ _ Hjoint) as Hjoint_remove.
  rewrite (store_sig_remove_absent l C HnotC), <- Hloc_remove
    in Hjoint_remove.
  pose proof (split_store_sig_remove l _ _ _ Hfull) as Hfull_remove.
  rewrite (store_sig_remove_absent l F0 HnotF) in Hfull_remove.
  destruct (split_interchange _ _ _ _ _ _ _ Hjoint_remove
      (split_left Lframe) (split_comm _ _ _ HC))
    as [Joint' [Discard [Hjoint' [Hterm' Hdiscard]]]].
  apply split_right_inv in Hdiscard. subst Discard.
  destruct (split_assoc _ _ _ _ _ Hfull_remove Hjoint')
    as [Frame' [Hfull' Hframe']].
  assert (Hunit_result : has_type_with_loc f [] [] [] Lframe Unit TUnit).
  { destruct f.
    - specialize (Hloc_frame_linear eq_refl). subst Lframe. constructor.
    - eapply TyLocWeak; [constructor | apply mask_le_refl | ].
      exact (split_incl_left Lframe [] Lframe (split_right Lframe)). }
  assert (Hframe_change : frame_change f F0 Frame').
  { destruct f.
    - destruct (runtime_unit_resources _ _ _ _ _ Hunit) as [_ ->].
      apply split_right_inv in Hframe'. subst Frame'. constructor.
    - constructor. exact (split_incl_right Frame' W F0 Hframe'). }
  apply Hrestore.
  exists (store_sig_remove l S), Lframe, Other, Joint', Frame'. split.
  - split.
    + apply natmap_remove_nodup. exact Hnd.
    + split; [exact Hcells_remove | ]. split; [exact Hunit_result | ].
      split; [exact Hterm' | exact Hfull'].
  - exact Hframe_change.
Qed.

(** ** Preservation for the relational evaluator *)

Lemma joint_head_preservation : forall s redex event s' reduct
    f S result R C J F,
  head_step (s, redex) event (s', reduct) ->
  joint_typed f S s redex result R C J F ->
  joint_preservation_result f F s' reduct result.
Proof.
  intros s redex event s' reduct f S result R C J F Hhead Htyped.
  inversion Hhead; subst; clear Hhead.
  - eapply pure_joint_preservation; eassumption.
  - normalize_joint Htyped.
    cbn [has_type_with_loc_head] in Hhead.
    destruct Hhead as [a [-> _]].
    eapply new_value_joint_preservation; eassumption.
  - normalize_joint Htyped.
    cbn [has_type_with_loc_head] in Hhead.
    destruct Hhead as [U1 [U2 [R1 [R2 [a [b [-> _]]]]]]].
    eapply swap_value_joint_preservation; eassumption.
  - normalize_joint Htyped.
    cbn [has_type_with_loc_head] in Hhead. destruct Hhead as [-> _].
    eapply free_loc_joint_preservation; eassumption.
Qed.

(** Preservation factors into a typed context frame and one head reduction.
    The context frame is unchanged; only the focused term and the cells it
    owns participate in the primitive preservation argument. *)
Theorem joint_preservation : forall c c',
  small_step c c' -> forall f S result R C J F,
  joint_typed f S (fst c) (snd c) result R C J F ->
  joint_preservation_result f F (fst c') (snd c') result.
Proof.
  intros [s e] [s' e'] Hstep f S result R C J F Htyped.
  cbn [fst snd] in *.
  apply (proj1 (small_step_decompose s e s' e')) in Hstep.
  destruct Hstep as
    [K [redex [reduct [event [-> [-> [Hcbv Hhead]]]]]]].
  destruct Htyped as [Hnd [Hcells [Hplug [Hjoint Hfull]]]].
  destruct (typed_eval_context_decompose_closed
      f [] K Hcbv redex R result Hplug)
    as [Rh [ah [Hcontext Hredex]]].
  destruct (typed_eval_context_store_frame _ _ _ _ _ _ _ _ _ _ Hcontext)
    as [Sibling [Hterm Hfill]].
  eapply focused_joint_preservation with
    (Active := Rh) (Sibling := Sibling) (Term := R) (Cells := C)
    (Joint := J) (active_ty := ah);
    [exact Hnd | exact Hcells | exact Hterm | exact Hjoint | exact Hfull | | ].
  - intros Focus Outer Hfocus Htop.
    eapply joint_head_preservation; [exact Hhead | ].
    split; [exact Hnd | ]. split; [exact Hcells | ].
    split; [exact Hredex | ]. split; [exact Hfocus | exact Htop].
  - intros Active' Term' Hreduct Hsplit.
    eapply Hfill; eassumption.
Qed.

Theorem preservation : forall f s e s' e' a,
  small_step (s, e) (s', e') ->
  store_balance f s e a -> store_balance f s' e' a.
Proof.
  intros f s e s' e' a Hstep
    [S Rterm Rrest Rcells Rfree
      Hnd Hcells Hterm Hterm_rest Hcells_free Hmode].
  destruct (split_unassoc _ _ _ _ _ Hterm_rest Hcells_free)
    as [Joint [Hfull Hjoint]].
  assert (Htyped : joint_typed f S s e a Rterm Rcells Joint Rfree).
  { split; [exact Hnd | ]. split; [exact Hcells | ].
    split; [exact Hterm | ]. split; [exact Hjoint | exact Hfull]. }
  destruct (joint_preservation (s, e) (s', e') Hstep
      f S a Rterm Rcells Joint Rfree Htyped)
    as [S' [Rterm' [Rcells' [Joint' [Rfree'
      [[Hnd' [Hcells' [Hterm' [Hjoint' Hfull']]]] Hframe]]]]]].
  destruct (split_assoc _ _ _ _ _ Hfull' Hjoint')
    as [Rrest' [Hterm_rest' Hcells_free']].
  eapply StoreBalance with (S := S') (Rterm := Rterm')
    (Rrest := Rrest') (Rcells := Rcells') (Rfree := Rfree');
    try eassumption.
  destruct f.
  - specialize (Hmode eq_refl). subst Rfree. inversion Hframe; subst.
    intros _. reflexivity.
  - discriminate.
Qed.

Corollary step_preservation : forall f c c' a,
  step c = SStep c' ->
  store_balance f (fst c) (snd c) a ->
  store_balance f (fst c') (snd c') a.
Proof.
  intros f [s e] [s' e'] a Hstep Htyped. cbn [fst snd] in *.
  eapply preservation; [apply step_sound; exact Hstep | exact Htyped].
Qed.

(** ** Preservation of ownership acyclicity *)

Lemma focus_joint_typed : forall f S s active active_ty Active Sibling
    Term Cells Joint Frame,
  NoDup (natmap_domain S) -> cells_typed f S s Cells ->
  has_type_with_loc f [] [] [] Active active active_ty ->
  Split Term Active Sibling -> Split Joint Term Cells -> Split S Joint Frame ->
  exists Focus Outer,
    joint_typed f S s active active_ty Active Cells Focus Outer.
Proof.
  intros f S s active active_ty Active Sibling Term Cells Joint Frame
    Hnd Hcells Hactive Hterm Hjoint Hfull.
  destruct (focus_partition _ _ _ _ _ _ _ Hfull Hjoint Hterm)
    as [Focus [Outer [Hfocus [Htop _]]]].
  exists Focus, Outer. split; [exact Hnd | ]. split; [exact Hcells | ].
  split; [exact Hactive | ]. split; [exact Hfocus | exact Htop].
Qed.

Lemma joint_term_locations_allocated : forall f S s e a R C J F l,
  joint_typed f S s e a R C J F ->
  In l (locations e) -> In l (natmap_domain s).
Proof.
  intros f S s e a R C J F l
    [Hnd [Hcells [Hterm [Hjoint Hfull]]]] Hloc.
  rewrite <- (cells_typed_domain _ _ _ _ Hcells).
  eapply split_domain_left; [exact Hfull | ].
  eapply split_domain_left; [exact Hjoint | ].
  eapply runtime_locations_owned; eassumption.
Qed.

Lemma joint_cell_edges_allocated : forall f S s e a R C J F x l,
  joint_typed f S s e a R C J F ->
  store_edge s x l -> In l (natmap_domain s).
Proof.
  intros f S s e a R C J F x l
    [Hnd [Hcells [Hterm [Hjoint Hfull]]]] Hedge.
  rewrite <- (cells_typed_domain _ _ _ _ Hcells).
  eapply split_domain_left; [exact Hfull | ].
  eapply split_domain_right; [exact Hjoint | ].
  eapply cells_locations_owned; eassumption.
Qed.

Lemma joint_root_no_incoming : forall f S s e a R C J F l,
  joint_typed f S s e a R C J F -> In l (locations e) ->
  forall x, ~ store_edge s x l.
Proof.
  intros f S s e a R C J F l
    [Hnd [Hcells [Hterm [Hjoint Hfull]]]] Hloc x Hedge.
  assert (HndJ : NoDup (natmap_domain J)).
  { eapply split_nodup_left; [apply split_map with (f := fst) in Hfull;
      exact Hfull | exact Hnd]. }
  apply split_map with (f := fst) in Hjoint.
  eapply split_disjoint with
    (l := natmap_domain J) (ls := natmap_domain R)
    (rs := natmap_domain C) (x := l); eauto.
  - eapply runtime_locations_owned; eassumption.
  - eapply cells_locations_owned; eassumption.
Qed.

Lemma joint_new_acyclic : forall f S s v a R C J F,
  joint_typed f S s (New v) a R C J F -> store_acyclic s ->
  store_acyclic (store_insert (fresh s) v s).
Proof.
  intros f S s v a R C J F Htyped Hacy.
  apply store_acyclic_insert; [exact Hacy | | ].
  - intros x Hedge. apply (fresh_not_allocated s).
    eapply joint_cell_edges_allocated; eassumption.
  - intros Hloc. apply (fresh_not_allocated s).
    eapply joint_term_locations_allocated; [exact Htyped | ].
    cbn. exact Hloc.
Qed.

Lemma joint_swap_acyclic : forall f S s l v a R C J F,
  joint_typed f S s (Swap (Loc l) v) a R C J F -> store_acyclic s ->
  store_acyclic (store_update l v s).
Proof.
  intros f S s l v a R C J F Htyped Hacy.
  pose proof Htyped as Htyped_copy.
  destruct Htyped as [Hnd [Hcells [Hterm [Hjoint Hfull]]]].
  apply store_acyclic_replace; [exact Hacy | | ].
  - eapply joint_root_no_incoming; [exact Htyped_copy | simpl; auto].
  - eapply runtime_swap_no_self_reference; [| exact Hterm].
    assert (HndJ : NoDup (natmap_domain J)).
    { eapply split_nodup_left; [apply split_map with (f := fst) in Hfull;
        exact Hfull | exact Hnd]. }
    eapply split_nodup_left; [apply split_map with (f := fst) in Hjoint;
      exact Hjoint | exact HndJ].
Qed.

Lemma joint_head_ownership_acyclic_preserved : forall
    s redex event s' reduct f S result R C J F,
  head_step (s, redex) event (s', reduct) ->
  joint_typed f S s redex result R C J F ->
  store_acyclic s -> store_acyclic s'.
Proof.
  intros s redex event s' reduct f S result R C J F Hhead Htyped Hacy.
  inversion Hhead; subst.
  - exact Hacy.
  - eapply joint_new_acyclic; eassumption.
  - eapply joint_swap_acyclic; eassumption.
  - apply store_acyclic_remove. exact Hacy.
Qed.

Theorem joint_ownership_acyclic_preserved : forall c c',
  small_step c c' -> forall f S result R C J F,
  joint_typed f S (fst c) (snd c) result R C J F ->
  store_acyclic (fst c) -> store_acyclic (fst c').
Proof.
  intros [s e] [s' e'] Hstep f S result R C J F Htyped Hacy.
  cbn [fst snd] in *.
  apply (proj1 (small_step_decompose s e s' e')) in Hstep.
  destruct Hstep as
    [K [redex [reduct [event [-> [-> [Hcbv Hhead]]]]]]].
  destruct Htyped as [Hnd [Hcells [Hplug [Hjoint Hfull]]]].
  destruct (typed_eval_context_decompose_closed
      f [] K Hcbv redex R result Hplug)
    as [Rh [ah [Hcontext Hredex]]].
  destruct (typed_eval_context_store_frame _ _ _ _ _ _ _ _ _ _ Hcontext)
    as [Sibling [Hterm _]].
  destruct (focus_joint_typed _ _ _ _ _ _ _ _ _ _ _
      Hnd Hcells Hredex Hterm Hjoint Hfull)
    as [Focus [Outer Hfocused]].
  eapply joint_head_ownership_acyclic_preserved; eassumption.
Qed.

Theorem ownership_acyclic_preserved : forall f s e s' e' a,
  small_step (s, e) (s', e') ->
  configuration_typed f s e a -> store_acyclic s'.
Proof.
  intros f s e s' e' a Hstep [Hbalance Hacy].
  destruct Hbalance as
    [S Rterm Rrest Rcells Rfree
      Hnd Hcells Hterm Hterm_rest Hcells_free Hmode].
  destruct (split_unassoc _ _ _ _ _ Hterm_rest Hcells_free)
    as [Joint [Hfull Hjoint]].
  eapply joint_ownership_acyclic_preserved with
    (c := (s, e)) (c' := (s', e'))
    (S := S) (R := Rterm) (C := Rcells) (J := Joint) (F := Rfree).
  - exact Hstep.
  - split; [exact Hnd | ]. split; [exact Hcells | ].
    split; [exact Hterm | ]. split; [exact Hjoint | exact Hfull].
  - exact Hacy.
Qed.

Corollary configuration_preservation : forall f s e s' e' a,
  small_step (s, e) (s', e') ->
  configuration_typed f s e a -> configuration_typed f s' e' a.
Proof.
  intros f s e s' e' a Hstep Htyped. split.
  - eapply preservation; [exact Hstep | exact (proj1 Htyped)].
  - eapply ownership_acyclic_preserved; eassumption.
Qed.

Corollary step_configuration_preservation : forall f c c' a,
  step c = SStep c' ->
  configuration_typed f (fst c) (snd c) a ->
  configuration_typed f (fst c') (snd c') a.
Proof.
  intros f [s e] [s' e'] a Hstep Htyped. cbn [fst snd] in *.
  eapply configuration_preservation;
    [apply step_sound; exact Hstep | exact Htyped].
Qed.
