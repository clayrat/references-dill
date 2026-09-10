(** * Renaming and substitution for terms with locations

    Lexical resources retain their de Bruijn scope and masks. Substitution
    images may own keyed location contexts; [Split] combines those contexts
    without introducing positional address masks. Shared images own no
    locations because they may be copied or discarded. *)

From Stdlib Require Import List Bool Arith Lia.
From DILLref Require Import Prelude Ty Syntax Index Mask OPE Split Renaming Substitution.
From DILLref Require Import Store StoreTyping.
Import ListNotations.

Lemma has_type_with_loc_lexical_mask : forall f G L U R e a,
  has_type_with_loc f G L U R e a -> wf_mask L U.
Proof. intros. eapply has_type_with_loc_mask; eassumption. Qed.

(** ** Lexical renaming *)

Lemma has_type_with_loc_rename : forall f G L U R e a,
  has_type_with_loc f G L U R e a -> forall G' L' ru E,
  ren_context G G' ru -> ope L' E L ->
  has_type_with_loc f G' L' (mask_comp E U) R
    (rename ru (ope_index E) e) a.
Proof.
  intros f G L U R e a H. induction H; intros G' L' ru E HG HE; simpl;
    try rewrite (ope_mask_zero _ _ _ HE).
  - rewrite (ope_mask_single _ _ _ _ HE (In_opt_Is_some H)).
    apply TyLocLVar. eapply ope_index_nth; eassumption.
  - apply TyLocUVar. apply HG, H.
  - apply TyLoc.
  - apply TyLocLam.
    change (has_type_with_loc f G' (a :: L')
      (mask_comp (true :: E) (true :: U)) R
      (rename ru (ope_index (true :: E)) e) b).
    apply IHhas_type_with_loc; [exact HG | constructor; exact HE].
  - eapply TyLocApp; eauto using ope_splitM, has_type_with_loc_lexical_mask,
      splitM_wf_whole.
  - apply TyLocUnit.
  - eapply TyLocLetUnit; eauto using ope_splitM, has_type_with_loc_lexical_mask,
      splitM_wf_whole.
  - eapply TyLocPair; eauto using ope_splitM, has_type_with_loc_lexical_mask,
      splitM_wf_whole.
  - eapply TyLocLetPair.
    + eapply ope_splitM; eauto using has_type_with_loc_lexical_mask,
        splitM_wf_whole.
    + exact H0.
    + eapply IHhas_type_with_loc1; eassumption.
    + change (has_type_with_loc f G' (b :: a :: L')
        (mask_comp (true :: true :: E) (true :: true :: U2)) R2
        (rename ru (ope_index (true :: true :: E)) e2) c).
      apply IHhas_type_with_loc2; [exact HG | constructor; constructor; exact HE].
  - apply TyLocWith; eauto.
  - eapply TyLocFst; eauto.
  - eapply TyLocSnd; eauto.
  - apply TyLocBang. rewrite <- (ope_mask_zero _ _ _ HE). eauto.
  - eapply TyLocLetBang; eauto using ope_splitM, has_type_with_loc_lexical_mask,
      splitM_wf_whole, up_ren_context.
  - apply TyLocNat.
  - apply TyLocSucc; eauto.
  - eapply TyLocIter; eauto using ope_splitM, has_type_with_loc_lexical_mask,
      splitM_wf_whole.
  - apply TyLocBool.
  - eapply TyLocIf; eauto using ope_splitM, has_type_with_loc_lexical_mask,
      splitM_wf_whole.
  - apply TyLocNew; eauto.
  - eapply TyLocSwap; eauto using ope_splitM, has_type_with_loc_lexical_mask,
      splitM_wf_whole.
  - apply TyLocFree; eauto.
  - eapply TyLocWeak; eauto using ope_mask_le, has_type_with_loc_lexical_mask.
Qed.

Lemma has_type_with_loc_rename_shared : forall f G L U R e a G' ru,
  has_type_with_loc f G L U R e a -> ren_context G G' ru ->
  has_type_with_loc f G' L U R (rename ru id_ren e) a.
Proof.
  intros f G L U R e a G' ru H Hr.
  pose proof (has_type_with_loc_rename _ _ _ _ _ _ _ H G' L ru
    (mask_id (length L)) Hr (ope_id L)) as Ht.
  rewrite (ope_comp_id_l _ _ _
    (ope_select _ _ (has_type_with_loc_mask _ _ _ _ _ _ _ H))) in Ht.
  erewrite rename_ext in Ht; [exact Ht | reflexivity | apply ope_index_id].
Qed.

Lemma has_type_with_loc_weaken_shared : forall f G L U R e a b,
  has_type_with_loc f G L U R e a ->
  has_type_with_loc f (b :: G) L U R (rename Nat.succ id_ren e) a.
Proof. intros. eapply has_type_with_loc_rename_shared; eauto using ren_context_shift. Qed.

Lemma has_type_with_loc_weaken_resource : forall f G L U R e a b,
  has_type_with_loc f G L U R e a ->
  has_type_with_loc f G (b :: L) (false :: U) R
    (rename id_ren Nat.succ e) a.
Proof.
  intros f G L U R e a b H.
  pose proof (has_type_with_loc_rename _ _ _ _ _ _ _ H G (b :: L) id_ren
    (mask_wk (length L)) (ren_context_id G) (ope_wk b L)) as Ht.
  unfold mask_wk in Ht. simpl in Ht.
  rewrite (ope_comp_id_l _ _ _
    (ope_select _ _ (has_type_with_loc_mask _ _ _ _ _ _ _ H))) in Ht.
  erewrite rename_ext in Ht; [exact Ht | reflexivity | ].
  intros i. simpl. rewrite ope_index_id. reflexivity.
Qed.

(** ** Substitution environments *)

Definition runtime_shared_env
    (f : flag) (G L K : list ty) (sub : nat -> term) : Prop :=
  forall i a, In_opt a (nth_error K i) ->
  has_type_with_loc f G L (mask_zero (length L)) [] (sub i) a.

Inductive runtime_linear_env (f : flag) (G L : list ty) :
    list ty -> mask -> (nat -> term) -> mask -> store_sig -> Prop :=
  | RTEnvNil : forall sub,
      runtime_linear_env f G L [] [] sub (mask_zero (length L)) []
  | RTEnvOff : forall a K I sub V R,
      runtime_linear_env f G L K I (fun i => sub (Nat.succ i)) V R ->
      runtime_linear_env f G L (a :: K) (false :: I) sub V R
  | RTEnvOn : forall a K I sub V R Vi Ri Vt Rt,
      SplitM V Vi Vt -> Split R Ri Rt ->
      has_type_with_loc f G L Vi Ri (sub 0) a ->
      runtime_linear_env f G L K I (fun i => sub (Nat.succ i)) Vt Rt ->
      runtime_linear_env f G L (a :: K) (true :: I) sub V R.

Lemma runtime_linear_env_source_wf : forall f G L K I sub V R,
  runtime_linear_env f G L K I sub V R -> wf_mask K I.
Proof. intros f G L K I sub V R H. induction H; unfold wf_mask in *; simpl; auto. Qed.

Lemma runtime_linear_env_target_wf : forall f G L K I sub V R,
  runtime_linear_env f G L K I sub V R -> wf_mask L V.
Proof.
  intros f G L K I sub V R H. induction H.
  - apply mask_zero_length.
  - exact IHruntime_linear_env.
  - eapply splitM_wf_whole; eauto using has_type_with_loc_lexical_mask.
Qed.

Lemma runtime_linear_env_ext : forall f G L K I sub V R,
  runtime_linear_env f G L K I sub V R ->
  forall sub', (forall i, sub i = sub' i) ->
  runtime_linear_env f G L K I sub' V R.
Proof.
  intros f G L K I sub V R H. induction H; intros sub' Heq; econstructor; eauto.
  rewrite <- Heq. exact H1.
Qed.

Lemma runtime_linear_env_empty : forall f G L K sub,
  runtime_linear_env f G L K (mask_zero (length K)) sub
    (mask_zero (length L)) [].
Proof. intros f G L K. induction K; intros; simpl; constructor; auto. Qed.

Lemma runtime_linear_env_zero : forall f G L K sub V R,
  runtime_linear_env f G L K (mask_zero (length K)) sub V R ->
  V = mask_zero (length L) /\ R = [].
Proof.
  intros f G L K. induction K; intros sub V R H; inversion H; subst; auto.
  eapply IHK; eassumption.
Qed.

Lemma runtime_linear_env_single : forall f G L K i a sub V R,
  In_opt a (nth_error K i) ->
  runtime_linear_env f G L K (mask_single (length K) i) sub V R ->
  has_type_with_loc f G L V R (sub i) a.
Proof.
  intros f G L K. induction K as [| b K IH]; intros [| i] a sub V R Hnth Henv;
    simpl in Hnth; try contradiction; inversion Henv; subst.
  - match goal with
    | Htail : runtime_linear_env _ _ _ K (mask_zero _) _ _ _ |- _ =>
        apply runtime_linear_env_zero in Htail; destruct Htail; subst
    end.
    match goal with Hs : SplitM _ _ (mask_zero _) |- _ =>
      apply splitM_zero_right_inv in Hs; subst end.
    match goal with Hs : Split _ _ [] |- _ =>
      apply split_left_inv in Hs; subst end.
    assumption.
  - eapply IH with (i := i) (sub := fun j => sub (Nat.succ j)); eassumption.
Qed.

Lemma runtime_linear_env_split : forall f G L K I sub V R,
  runtime_linear_env f G L K I sub V R -> forall I1 I2,
  SplitM I I1 I2 ->
  exists V1 V2 R1 R2,
    SplitM V V1 V2 /\ Split R R1 R2 /\
    runtime_linear_env f G L K I1 sub V1 R1 /\
    runtime_linear_env f G L K I2 sub V2 R2.
Proof.
  intros f G L K I sub V R Henv. induction Henv; intros I1 I2 Hsource;
    inversion Hsource; subst.
  - exists (mask_zero (length L)), (mask_zero (length L)), [], [].
    repeat split; try apply splitM_zero; constructor.
  - destruct (IHHenv _ _ H0)
      as [V1 [V2 [R1 [R2 [HV [HR [He1 He2]]]]]]].
    exists V1, V2, R1, R2. repeat split; try assumption; constructor; assumption.
  - match goal with Htail : SplitM _ _ _ |- _ =>
      destruct (IHHenv _ _ Htail)
        as [V1 [V2 [R1 [R2 [HV [HR [He1 He2]]]]]]] end.
    destruct (splitM_unassoc _ _ _ _ _ H HV) as [Vleft [HVout HVparts]].
    destruct (split_unassoc _ _ _ _ _ H0 HR) as [Rleft [HRout HRparts]].
    exists Vleft, V2, Rleft, R2. repeat split; try assumption.
    + eapply RTEnvOn; eassumption.
    + constructor. exact He2.
  - match goal with Htail : SplitM _ _ _ |- _ =>
      destruct (IHHenv _ _ Htail)
        as [V1 [V2 [R1 [R2 [HV [HR [He1 He2]]]]]]] end.
    destruct (splitM_assoc _ _ _ _ _ (splitM_comm _ _ _ H) HV)
      as [Vright [HVout HVparts]].
    destruct (split_assoc _ _ _ _ _ (split_comm _ _ _ H0) HR)
      as [Rright [HRout HRparts]].
    exists V1, Vright, R1, Rright. repeat split; try assumption.
    + constructor. exact He1.
    + eapply RTEnvOn with (Vi := Vi) (Ri := Ri) (Vt := V2) (Rt := R2).
      * apply splitM_comm. exact HVparts.
      * apply split_comm. exact HRparts.
      * exact H1.
      * exact He2.
Qed.

Lemma runtime_linear_env_restrict : forall f G L K I sub V R,
  runtime_linear_env f G L K I sub V R -> forall J,
  mask_le J I ->
  exists V' R',
    runtime_linear_env f G L K J sub V' R' /\
    mask_le V' V /\ split_incl R' R.
Proof.
  intros f G L K I sub V R Henv. induction Henv; intros J Hle;
    inversion Hle; subst.
  - exists (mask_zero (length L)), []. repeat split;
      try constructor; try apply mask_le_refl; apply split_incl_refl.
  - match goal with Htail : mask_le _ _ |- _ =>
      destruct (IHHenv _ Htail) as [V' [R' [He [HV HR]]]] end.
    exists V', R'. repeat split; try assumption. constructor. exact He.
  - match goal with Htail : mask_le _ _ |- _ =>
      destruct (IHHenv _ Htail) as [V' [R' [He [HV HR]]]] end.
    exists V', R'. repeat split; try assumption.
    + constructor. exact He.
    + eapply mask_le_trans; [exact HV | eapply splitM_le_r; exact H].
    + eapply split_incl_trans; [exact HR | eapply split_incl_right; exact H0].
  - match goal with Htail : mask_le _ _ |- _ =>
      destruct (IHHenv _ Htail) as [Vt' [Rt' [He [HV HR]]]] end.
    destruct (splitM_subright _ _ _ H _ HV) as [V' [HVs HVle]].
    destruct HR as [Rf HR].
    destruct (split_unassoc _ _ _ _ _ H0 HR) as [R' [HRincl HRparts]].
    exists V', R'. repeat split; try assumption.
    + eapply RTEnvOn; eassumption.
    + eapply split_incl_left. exact HRincl.
Qed.

Lemma runtime_shared_env_shift_l : forall f G L K sub a,
  runtime_shared_env f G L K sub ->
  runtime_shared_env f G (a :: L) K (shift_l sub).
Proof.
  unfold runtime_shared_env, shift_l. intros.
  change (has_type_with_loc f G (a :: L) (false :: mask_zero (length L)) []
    (rename id_ren Nat.succ (sub i)) a0).
  apply has_type_with_loc_weaken_resource. eauto.
Qed.

Lemma runtime_shared_env_up_u : forall f G L K sub a,
  runtime_shared_env f G L K sub ->
  runtime_shared_env f (a :: G) L (a :: K) (up_subst_u sub).
Proof.
  unfold runtime_shared_env. intros f G L K sub a H [| i] b Hi; simpl in *.
  - subst. apply TyLocUVar. reflexivity.
  - unfold shift_u. apply has_type_with_loc_weaken_shared. eauto.
Qed.

Lemma runtime_linear_env_shift_l : forall f G L K I sub V R,
  runtime_linear_env f G L K I sub V R -> forall a,
  runtime_linear_env f G (a :: L) K I (shift_l sub) (false :: V) R.
Proof.
  intros f G L K I sub V R Henv. induction Henv; intros b; simpl.
  - apply RTEnvNil.
  - constructor. apply IHHenv.
  - eapply RTEnvOn.
    + constructor. exact H.
    + exact H0.
    + apply has_type_with_loc_weaken_resource. exact H1.
    + apply IHHenv.
Qed.

Lemma runtime_linear_env_shift_u : forall f G L K I sub V R,
  runtime_linear_env f G L K I sub V R -> forall a,
  runtime_linear_env f (a :: G) L K I (shift_u sub) V R.
Proof.
  intros f G L K I sub V R Henv. induction Henv; intros b; econstructor; eauto.
  apply has_type_with_loc_weaken_shared. exact H1.
Qed.

Lemma runtime_linear_env_up_l : forall f G L K I sub V R a,
  runtime_linear_env f G L K I sub V R ->
  runtime_linear_env f G (a :: L) (a :: K) (true :: I)
    (up_subst_l sub) (true :: V) R.
Proof.
  intros f G L K I sub V R a Henv.
  eapply RTEnvOn with
    (Vi := true :: mask_zero (length L)) (Ri := [])
    (Vt := false :: V) (Rt := R).
  - constructor. pose proof (runtime_linear_env_target_wf _ _ _ _ _ _ _ _ Henv) as Hw.
    unfold wf_mask in Hw. rewrite <- Hw. apply splitM_right.
  - apply split_right.
  - change (has_type_with_loc f G (a :: L)
      (mask_single (length (a :: L)) 0) [] (LVar 0) a).
    apply TyLocLVar. reflexivity.
  - apply runtime_linear_env_shift_l. exact Henv.
Qed.

Lemma runtime_shared_env_id : forall f G L,
  runtime_shared_env f G L G UVar.
Proof. unfold runtime_shared_env. intros. apply TyLocUVar, H. Qed.

Lemma runtime_linear_env_id : forall f G L I,
  wf_mask L I -> runtime_linear_env f G L L I LVar I [].
Proof.
  intros f G L. induction L as [| a L IH]; intros [| bit I] Hw;
    unfold wf_mask in Hw; simpl in Hw; try discriminate.
  - constructor.
  - assert (Htail : runtime_linear_env f G L L I LVar I [])
      by (apply IH; unfold wf_mask; lia).
    destruct bit.
    + eapply runtime_linear_env_ext; [apply runtime_linear_env_up_l, Htail | ].
      intros [| i]; reflexivity.
    + constructor. apply (runtime_linear_env_shift_l _ _ _ _ _ _ _ _ Htail a).
Qed.

(** ** Simultaneous substitution *)

Theorem has_type_with_loc_subst : forall f G L U R e a,
  has_type_with_loc f G L U R e a -> forall G' L' su sl V Q P,
  runtime_shared_env f G' L' G su ->
  runtime_linear_env f G' L' L U sl V Q ->
  Split P R Q ->
  has_type_with_loc f G' L' V P (subst su sl e) a.
Proof.
  intros f G L U R e a Htype. induction Htype;
    intros G' L' su sl Vout Qout P Hsu Hsl Hcombine; simpl.
  - pose proof (runtime_linear_env_single _ _ _ _ _ _ _ _ _ H Hsl) as Himage.
    apply split_right_inv in Hcombine. subst P. exact Himage.
  - pose proof (runtime_linear_env_zero _ _ _ _ _ _ _ Hsl) as [-> ->].
    apply split_right_inv in Hcombine. subst P. apply Hsu, H.
  - pose proof (runtime_linear_env_zero _ _ _ _ _ _ _ Hsl) as [-> ->].
    apply split_left_inv in Hcombine. subst P. apply TyLoc.
  - apply TyLocLam. eapply IHHtype.
    + apply runtime_shared_env_shift_l. exact Hsu.
    + apply runtime_linear_env_up_l. exact Hsl.
    + exact Hcombine.
  - destruct (runtime_linear_env_split _ _ _ _ _ _ _ _ Hsl _ _ H)
      as [V1 [V2 [Q1 [Q2 [HV [HQ [He1 He2]]]]]]].
    destruct (split_interchange _ _ _ _ _ _ _ Hcombine H0 HQ)
      as [P1 [P2 [HP [HP1 HP2]]]].
    eapply TyLocApp; [exact HV | exact HP | | ];
      [eapply IHHtype1 | eapply IHHtype2]; eassumption.
  - pose proof (runtime_linear_env_zero _ _ _ _ _ _ _ Hsl) as [-> ->].
    apply split_right_inv in Hcombine. subst P. apply TyLocUnit.
  - destruct (runtime_linear_env_split _ _ _ _ _ _ _ _ Hsl _ _ H)
      as [V1 [V2 [Q1 [Q2 [HV [HQ [He1 He2]]]]]]].
    destruct (split_interchange _ _ _ _ _ _ _ Hcombine H0 HQ)
      as [P1 [P2 [HP [HP1 HP2]]]].
    eapply TyLocLetUnit; [exact HV | exact HP | | ];
      [eapply IHHtype1 | eapply IHHtype2]; eassumption.
  - destruct (runtime_linear_env_split _ _ _ _ _ _ _ _ Hsl _ _ H)
      as [V1 [V2 [Q1 [Q2 [HV [HQ [He1 He2]]]]]]].
    destruct (split_interchange _ _ _ _ _ _ _ Hcombine H0 HQ)
      as [P1 [P2 [HP [HP1 HP2]]]].
    eapply TyLocPair; [exact HV | exact HP | | ];
      [eapply IHHtype1 | eapply IHHtype2]; eassumption.
  - destruct (runtime_linear_env_split _ _ _ _ _ _ _ _ Hsl _ _ H)
      as [V1 [V2 [Q1 [Q2 [HV [HQ [He1 He2]]]]]]].
    destruct (split_interchange _ _ _ _ _ _ _ Hcombine H0 HQ)
      as [P1 [P2 [HP [HP1 HP2]]]].
    eapply TyLocLetPair; [exact HV | exact HP | | ].
    + eapply IHHtype1; eassumption.
    + eapply IHHtype2.
      * apply runtime_shared_env_shift_l, runtime_shared_env_shift_l. exact Hsu.
      * apply runtime_linear_env_up_l, runtime_linear_env_up_l. exact He2.
      * exact HP2.
  - apply TyLocWith; [eapply IHHtype1 | eapply IHHtype2]; eassumption.
  - eapply TyLocFst. eapply IHHtype; eassumption.
  - eapply TyLocSnd. eapply IHHtype; eassumption.
  - pose proof (runtime_linear_env_zero _ _ _ _ _ _ _ Hsl) as [-> ->].
    apply split_right_inv in Hcombine. subst P.
    apply TyLocBang. eapply IHHtype.
    + exact Hsu.
    + apply runtime_linear_env_empty.
    + constructor.
  - destruct (runtime_linear_env_split _ _ _ _ _ _ _ _ Hsl _ _ H)
      as [V1 [V2 [Q1 [Q2 [HV [HQ [He1 He2]]]]]]].
    destruct (split_interchange _ _ _ _ _ _ _ Hcombine H0 HQ)
      as [P1 [P2 [HP [HP1 HP2]]]].
    eapply TyLocLetBang; [exact HV | exact HP | | ].
    + eapply IHHtype1; eassumption.
    + eapply IHHtype2.
      * apply runtime_shared_env_up_u. exact Hsu.
      * apply runtime_linear_env_shift_u. exact He2.
      * exact HP2.
  - pose proof (runtime_linear_env_zero _ _ _ _ _ _ _ Hsl) as [-> ->].
    apply split_right_inv in Hcombine. subst P. apply TyLocNat.
  - apply TyLocSucc. eapply IHHtype; eassumption.
  - destruct (runtime_linear_env_split _ _ _ _ _ _ _ _ Hsl _ _ H)
      as [Vc [Vr [Qc [Qr [HVfirst [HQfirst [Hec Her]]]]]]].
    destruct (split_interchange _ _ _ _ _ _ _ Hcombine H1 HQfirst)
      as [Pc [Pr [HPfirst [HPc HPr]]]].
    destruct (runtime_linear_env_split _ _ _ _ _ _ _ _ Her _ _ H0)
      as [Vs [Vz [Qs [Qz [HVrest [HQrest [Hes Hez]]]]]]].
    destruct (split_interchange _ _ _ _ _ _ _ HPr H2 HQrest)
      as [Ps [Pz [HPrest [HPs HPz]]]].
    eapply TyLocIter; [exact HVfirst | exact HVrest | exact HPfirst | exact HPrest | | | ];
      [eapply IHHtype1 | eapply IHHtype2 | eapply IHHtype3]; eassumption.
  - pose proof (runtime_linear_env_zero _ _ _ _ _ _ _ Hsl) as [-> ->].
    apply split_right_inv in Hcombine. subst P. apply TyLocBool.
  - destruct (runtime_linear_env_split _ _ _ _ _ _ _ _ Hsl _ _ H)
      as [Vc [Vb [Qc [Qb [HV [HQ [Hec Heb]]]]]]].
    destruct (split_interchange _ _ _ _ _ _ _ Hcombine H0 HQ)
      as [Pc [Pb [HP [HPc HPb]]]].
    eapply TyLocIf; [exact HV | exact HP | | | ];
      [eapply IHHtype1 | eapply IHHtype2 | eapply IHHtype3]; eassumption.
  - apply TyLocNew. eapply IHHtype; eassumption.
  - destruct (runtime_linear_env_split _ _ _ _ _ _ _ _ Hsl _ _ H)
      as [V1 [V2 [Q1 [Q2 [HV [HQ [He1 He2]]]]]]].
    destruct (split_interchange _ _ _ _ _ _ _ Hcombine H0 HQ)
      as [P1 [P2 [HP [HP1 HP2]]]].
    eapply TyLocSwap; [exact HV | exact HP | | ];
      [eapply IHHtype1 | eapply IHHtype2]; eassumption.
  - apply TyLocFree. eapply IHHtype; eassumption.
  - destruct (runtime_linear_env_restrict _ _ _ _ _ _ _ _ Hsl _ H)
      as [Vsmall [Qsmall [Hsmall [HVsmall HQsmall]]]].
    destruct H0 as [Rframe HR]. destruct HQsmall as [Qframe HQ].
    destruct (split_interchange _ _ _ _ _ _ _ Hcombine HR HQ)
      as [Psmall [Pframe [HPincl [HPsmall HPframe]]]].
    eapply TyLocWeak.
    + eapply IHHtype; eassumption.
    + exact HVsmall.
    + exists Pframe. exact HPincl.
Qed.

Corollary has_type_with_loc_subst_l : forall f G L U V W Rbody Rarg R e v a b,
  has_type_with_loc f G (a :: L) (true :: U) Rbody e b ->
  has_type_with_loc f G L V Rarg v a ->
  SplitM W V U -> Split R Rbody Rarg ->
  has_type_with_loc f G L W R (subst_l v e) b.
Proof.
  intros f G L U V W Rbody Rarg R e v a b He Hv Hlex Haddr.
  unfold subst_l. eapply has_type_with_loc_subst; [exact He | | | exact Haddr].
  - apply runtime_shared_env_id.
  - eapply RTEnvOn with (Vi := V) (Ri := Rarg) (Vt := U) (Rt := []).
    + exact Hlex.
    + apply split_left.
    + exact Hv.
    + apply runtime_linear_env_id.
      pose proof (has_type_with_loc_lexical_mask _ _ _ _ _ _ _ He) as Hw.
      unfold wf_mask in *. simpl in Hw. lia.
Qed.

Corollary has_type_with_loc_subst_u : forall f G L U R e v a b,
  has_type_with_loc f (a :: G) L U R e b ->
  has_type_with_loc f G L (mask_zero (length L)) [] v a ->
  has_type_with_loc f G L U R (subst_u v e) b.
Proof.
  intros f G L U R e v a b He Hv. unfold subst_u.
  eapply has_type_with_loc_subst; [exact He | | | apply split_left].
  - intros [| i] c Hi; simpl in *.
    + subst. exact Hv.
    + apply TyLocUVar, Hi.
  - apply runtime_linear_env_id. eapply has_type_with_loc_lexical_mask; exact He.
Qed.
