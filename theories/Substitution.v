(** * Capture-avoiding simultaneous substitution

    Shared and resource variables have independent substitutions. Crossing
    either kind of binder shifts free variables in both sets of images;
    only the bound zone receives a new identity image. In [LetPair], index
    zero belongs to the second component, as in the core syntax. *)

From Stdlib Require Import List Bool Arith Lia.
From DILLref Require Import Prelude Ty Syntax Index Scoping Mask Typing Renaming.
Import ListNotations.

Definition shift_l (s : nat -> term) (i : nat) : term := rename id_ren S (s i).
Definition shift_u (s : nat -> term) (i : nat) : term := rename S id_ren (s i).

Definition up_subst_l (s : nat -> term) (i : nat) : term :=
  match i with 0 => LVar 0 | S j => shift_l s j end.
Definition up_subst_u (s : nat -> term) (i : nat) : term :=
  match i with 0 => UVar 0 | S j => shift_u s j end.

Fixpoint subst (su sl : nat -> term) (e : term) : term :=
  match e with
  | LVar i => sl i
  | UVar i => su i
  | Loc a => Loc a
  | Lam a e => Lam a (subst (shift_l su) (up_subst_l sl) e)
  | App e1 e2 => App (subst su sl e1) (subst su sl e2)
  | Unit => Unit
  | LetUnit e1 e2 => LetUnit (subst su sl e1) (subst su sl e2)
  | Pair e1 e2 => Pair (subst su sl e1) (subst su sl e2)
  | LetPair e1 e2 => LetPair (subst su sl e1)
      (subst (shift_l (shift_l su)) (up_subst_l (up_subst_l sl)) e2)
  | With e1 e2 => With (subst su sl e1) (subst su sl e2)
  | Fst e => Fst (subst su sl e)
  | Snd e => Snd (subst su sl e)
  | Bang e => Bang (subst su sl e)
  | LetBang e1 e2 => LetBang (subst su sl e1) (subst (up_subst_u su) (shift_u sl) e2)
  | Nat n => Nat n
  | Succ e => Succ (subst su sl e)
  | Iter c s z => Iter (subst su sl c) (subst su sl s) (subst su sl z)
  | Bool b => Bool b
  | If c e1 e2 => If (subst su sl c) (subst su sl e1) (subst su sl e2)
  | New e => New (subst su sl e)
  | Swap e1 e2 => Swap (subst su sl e1) (subst su sl e2)
  | Free e => Free (subst su sl e)
  end.

(** Eliminate the innermost binder in one zone. *)
Definition subst_l (v e : term) : term :=
  subst UVar (fun i => match i with 0 => v | S j => LVar j end) e.
Definition subst_u (v e : term) : term :=
  subst (fun i => match i with 0 => v | S j => UVar j end) LVar e.

Lemma shift_l_ext : forall s t, (forall i, s i = t i) ->
  forall i, shift_l s i = shift_l t i.
Proof. unfold shift_l. intros. rewrite H. reflexivity. Qed.
Lemma shift_u_ext : forall s t, (forall i, s i = t i) ->
  forall i, shift_u s i = shift_u t i.
Proof. unfold shift_u. intros. rewrite H. reflexivity. Qed.
Lemma up_subst_l_ext : forall s t, (forall i, s i = t i) ->
  forall i, up_subst_l s i = up_subst_l t i.
Proof. intros s t H [| i]; simpl; auto using shift_l_ext. Qed.
Lemma up_subst_u_ext : forall s t, (forall i, s i = t i) ->
  forall i, up_subst_u s i = up_subst_u t i.
Proof. intros s t H [| i]; simpl; auto using shift_u_ext. Qed.

Lemma subst_ext : forall e su sl tu tl,
  (forall i, su i = tu i) -> (forall i, sl i = tl i) ->
  subst su sl e = subst tu tl e.
Proof.
  induction e; intros; simpl; f_equal;
    eauto 8 using shift_l_ext, shift_u_ext, up_subst_l_ext, up_subst_u_ext.
Qed.

(** Substituting variables is exactly renaming; no function extensionality
    is needed, since the two traversals agree pointwise on images. *)
Lemma subst_rename : forall e su sl ru rl,
  (forall i, su i = UVar (ru i)) -> (forall i, sl i = LVar (rl i)) ->
  subst su sl e = rename ru rl e.
Proof.
  induction e; intros; simpl; try solve [eauto]; f_equal; eauto.
  - apply IHe.
    + intros i. unfold shift_l. rewrite H. reflexivity.
    + intros [| i]; simpl; auto. unfold shift_l. rewrite H0. reflexivity.
  - apply IHe2.
    + intros i. unfold shift_l. rewrite H. reflexivity.
    + intros [| [| i]]; unfold up_subst_l, shift_l; simpl;
        rewrite ?H0; reflexivity.
  - apply IHe2.
    + intros [| i]; simpl; auto. unfold shift_u. rewrite H. reflexivity.
    + intros i. unfold shift_u. rewrite H0. reflexivity.
Qed.

Lemma subst_id : forall e, subst UVar LVar e = e.
Proof.
  intros. rewrite (subst_rename e UVar LVar id_ren id_ren);
    try reflexivity. apply rename_id.
Qed.

Definition subst_scoped (n g l : nat) (s : nat -> term) : Prop :=
  forall i, i < n -> scoped g l (s i).

Lemma shift_l_scoped : forall n g l s,
  subst_scoped n g l s -> subst_scoped n g (S l) (shift_l s).
Proof.
  unfold subst_scoped, shift_l. intros. eapply rename_scoped; eauto;
    unfold ren_scoped, id_ren; intros; lia.
Qed.
Lemma shift_u_scoped : forall n g l s,
  subst_scoped n g l s -> subst_scoped n (S g) l (shift_u s).
Proof.
  unfold subst_scoped, shift_u. intros. eapply rename_scoped; eauto;
    unfold ren_scoped, id_ren; intros; lia.
Qed.
Lemma up_subst_l_scoped : forall n g l s,
  subst_scoped n g l s -> subst_scoped (S n) g (S l) (up_subst_l s).
Proof.
  intros n g l s H [| i] Hi; simpl; [constructor; lia | ].
  apply (shift_l_scoped _ _ _ _ H). lia.
Qed.
Lemma up_subst_u_scoped : forall n g l s,
  subst_scoped n g l s -> subst_scoped (S n) (S g) l (up_subst_u s).
Proof.
  intros n g l s H [| i] Hi; simpl; [constructor; lia | ].
  apply (shift_u_scoped _ _ _ _ H). lia.
Qed.

#[local] Hint Constructors scoped : substitution.
#[local] Hint Resolve shift_l_scoped shift_u_scoped up_subst_l_scoped up_subst_u_scoped : substitution.

Lemma subst_preserves_scoping : forall g l e, scoped g l e ->
  forall g' l' su sl, subst_scoped g g' l' su -> subst_scoped l g' l' sl ->
  scoped g' l' (subst su sl e).
Proof.
  intros g l e H. induction H; intros; simpl; eauto 8 with substitution.
  all: unfold subst_scoped in *; eauto.
Qed.

(** Shared images have no resource demand, since they may be copied or
    omitted. A linear environment partitions its output mask among exactly
    the available source positions. Unavailable positions impose no typing
    obligation on their images. *)
Definition shared_env (f : flag) (G L K : list ty) (s : nat -> term) : Prop :=
  forall i a, In_opt a (nth_error K i) ->
  has_type f G L (mask_zero (length L)) (s i) a.

Inductive linear_env (f : flag) (G L : list ty) :
  list ty -> mask -> (nat -> term) -> mask -> Prop :=
  | EnvNil : forall s, linear_env f G L [] [] s (mask_zero (length L))
  | EnvOff : forall a K U s V,
      linear_env f G L K U (fun i => s (S i)) V ->
      linear_env f G L (a :: K) (false :: U) s V
  | EnvOn : forall a K U s V W R,
      SplitM V W R -> has_type f G L W (s 0) a ->
      linear_env f G L K U (fun i => s (S i)) R ->
      linear_env f G L (a :: K) (true :: U) s V.

Lemma linear_env_source_wf : forall f G L K U s V,
  linear_env f G L K U s V -> wf_mask K U.
Proof. intros f G L K U s V H. induction H; unfold wf_mask in *; simpl; auto. Qed.

Lemma linear_env_target_wf : forall f G L K U s V,
  linear_env f G L K U s V -> wf_mask L V.
Proof.
  intros f G L K U s V H. induction H; auto.
  - unfold wf_mask. apply mask_zero_length.
  - eapply splitM_wf_whole; eauto using typing_wf_mask.
Qed.

Lemma linear_env_ext : forall f G L K U s V,
  linear_env f G L K U s V -> forall t, (forall i, s i = t i) ->
  linear_env f G L K U t V.
Proof.
  intros f G L K U s V H. induction H; intros t Heq; econstructor; eauto.
  rewrite <- Heq. exact H0.
Qed.

Lemma linear_env_empty : forall f G L K s,
  linear_env f G L K (mask_zero (length K)) s (mask_zero (length L)).
Proof. intros f G L K. induction K; intros; simpl; constructor; auto. Qed.

Lemma linear_env_zero : forall f G L K s V,
  linear_env f G L K (mask_zero (length K)) s V -> V = mask_zero (length L).
Proof.
  intros f G L K. induction K; intros s V H; inversion H; subst; auto.
  eapply IHK; eassumption.
Qed.

Lemma linear_env_single : forall f G L K i a s V,
  In_opt a (nth_error K i) ->
  linear_env f G L K (mask_single (length K) i) s V ->
  has_type f G L V (s i) a.
Proof.
  intros f G L K. induction K as [| b K IH]; intros [| i] a s V Hnth He;
    simpl in Hnth; try contradiction; inversion He; subst.
  - match goal with Htail : linear_env _ _ _ K (mask_zero _) _ _ |- _ =>
      apply linear_env_zero in Htail; subst end.
    match goal with Hs : SplitM _ _ (mask_zero _) |- _ =>
      apply splitM_zero_right_inv in Hs; subst end. assumption.
  - eapply IH with (i := i) (s := fun j => s (S j)); eassumption.
Qed.

Lemma linear_env_split : forall f G L K I s V,
  linear_env f G L K I s V -> forall U F, SplitM I U F ->
  exists V1 V2, SplitM V V1 V2 /\
    linear_env f G L K U s V1 /\ linear_env f G L K F s V2.
Proof.
  intros f G L K I s V H. induction H; intros U' F Hs; inversion Hs; subst.
  - exists (mask_zero (length L)), (mask_zero (length L)).
    split; [apply splitM_zero | split; constructor].
  - match goal with Htail : SplitM _ _ _ |- _ =>
      destruct (IHlinear_env _ _ Htail) as [V1 [V2 [Hv [He1 He2]]]] end.
    exists V1, V2. split; [exact Hv | split; constructor; assumption].
  - match goal with Htail : SplitM _ _ _ |- _ =>
      destruct (IHlinear_env _ _ Htail) as [V1 [V2 [Hv [He1 He2]]]] end.
    destruct (splitM_unassoc _ _ _ _ _ H Hv) as [W1 [Hout Hin]].
    exists W1, V2. split; [exact Hout | split; econstructor; eassumption].
  - match goal with Htail : SplitM _ _ _ |- _ =>
      destruct (IHlinear_env _ _ Htail) as [V1 [V2 [Hv [He1 He2]]]] end.
    destruct (splitM_assoc _ _ _ _ _ (splitM_comm _ _ _ H) Hv) as [W2 [Hout Hin]].
    exists V1, W2. split; [exact Hout | split].
    + constructor. exact He1.
    + eapply EnvOn with (W := W) (R := V2); eauto using splitM_comm.
Qed.

Lemma linear_env_restrict : forall f G L K I s V,
  linear_env f G L K I s V -> forall U, mask_le U I ->
  exists W, linear_env f G L K U s W /\ mask_le W V.
Proof.
  intros f G L K I s V H. induction H; intros U' Hle; inversion Hle; subst.
  - exists (mask_zero (length L)). split; [constructor | apply mask_le_refl].
  - match goal with Htail : mask_le _ _ |- _ =>
      destruct (IHlinear_env _ Htail) as [R' [He Hr]] end.
    exists R'. split; [constructor | ]; assumption.
  - match goal with Htail : mask_le _ _ |- _ =>
      destruct (IHlinear_env _ Htail) as [R' [He Hr]] end.
    exists R'. split; [constructor; exact He | ].
    eapply mask_le_trans; [exact Hr | eapply splitM_le_r; exact H].
  - match goal with Htail : mask_le _ _ |- _ =>
      destruct (IHlinear_env _ Htail) as [R' [He Hr]] end.
    destruct (splitM_subright _ _ _ H _ Hr) as [V' [Hs Hv]].
    exists V'. split; [econstructor; eassumption | exact Hv].
Qed.

Lemma shared_env_shift_l : forall f G L K s a,
  shared_env f G L K s -> shared_env f G (a :: L) K (shift_l s).
Proof.
  unfold shared_env, shift_l. intros.
  change (has_type f G (a :: L) (false :: mask_zero (length L))
    (rename id_ren S (s i)) a0).
  apply typing_weaken_resource. eauto.
Qed.

Lemma shared_env_up_u : forall f G L K s a,
  shared_env f G L K s -> shared_env f (a :: G) L (a :: K) (up_subst_u s).
Proof.
  unfold shared_env. intros f G L K s a H [| i] b Hi; simpl in *.
  - subst. apply TyUVar. reflexivity.
  - unfold shift_u. apply typing_weaken_shared. eauto.
Qed.

Lemma linear_env_shift_l : forall f G L K U s V,
  linear_env f G L K U s V -> forall a,
  linear_env f G (a :: L) K U (shift_l s) (false :: V).
Proof.
  intros f G L K U s V H. induction H; intros b; simpl.
  - apply EnvNil.
  - constructor. apply IHlinear_env.
  - eapply EnvOn; [constructor; exact H | | apply IHlinear_env].
    apply typing_weaken_resource. exact H0.
Qed.

Lemma linear_env_shift_u : forall f G L K U s V,
  linear_env f G L K U s V -> forall a,
  linear_env f (a :: G) L K U (shift_u s) V.
Proof.
  intros f G L K U s V H. induction H; intros b; econstructor; eauto.
  apply typing_weaken_shared. exact H0.
Qed.

Lemma linear_env_up_l : forall f G L K U s V a,
  linear_env f G L K U s V ->
  linear_env f G (a :: L) (a :: K) (true :: U) (up_subst_l s) (true :: V).
Proof.
  intros. eapply EnvOn with (W := true :: mask_zero (length L)) (R := false :: V).
  - constructor. pose proof (linear_env_target_wf _ _ _ _ _ _ _ H) as Hw.
    unfold wf_mask in Hw. rewrite <- Hw. apply splitM_right.
  - change (has_type f G (a :: L) (mask_single (length (a :: L)) 0) (LVar 0) a).
    apply TyLVar. reflexivity.
  - apply linear_env_shift_l. exact H.
Qed.

Lemma typing_subst : forall f G L U e a,
  has_type f G L U e a -> forall G' L' su sl V,
  shared_env f G' L' G su -> linear_env f G' L' L U sl V ->
  has_type f G' L' V (subst su sl e) a.
Proof.
  intros f G L U e a H. induction H; intros G' L' su sl Vout Hsu Hsl; simpl.
  - eapply linear_env_single; eassumption.
  - apply linear_env_zero in Hsl. subst. apply Hsu, H.
  - apply TyLam. apply IHhas_type;
      auto using shared_env_shift_l, linear_env_up_l.
  - destruct (linear_env_split _ _ _ _ _ _ _ Hsl _ _ H) as [V1 [V2 [Hs [He1 He2]]]].
    eapply TyApp; eauto.
  - apply linear_env_zero in Hsl. subst. apply TyUnit.
  - destruct (linear_env_split _ _ _ _ _ _ _ Hsl _ _ H) as [V1 [V2 [Hs [He1 He2]]]].
    eapply TyLetUnit; eauto.
  - destruct (linear_env_split _ _ _ _ _ _ _ Hsl _ _ H) as [V1 [V2 [Hs [He1 He2]]]].
    eapply TyPair; eauto.
  - destruct (linear_env_split _ _ _ _ _ _ _ Hsl _ _ H) as [V1 [V2 [Hs [He1 He2]]]].
    eapply TyLetPair; eauto 8 using shared_env_shift_l, linear_env_up_l.
  - apply TyWith; eauto.
  - eapply TyFst; eauto.
  - eapply TySnd; eauto.
  - pose proof (linear_env_zero _ _ _ _ _ _ Hsl) as ->.
    apply TyBang. eauto using linear_env_empty.
  - destruct (linear_env_split _ _ _ _ _ _ _ Hsl _ _ H) as [V1 [V2 [Hs [He1 He2]]]].
    eapply TyLetBang; eauto using shared_env_up_u, linear_env_shift_u.
  - apply linear_env_zero in Hsl. subst. apply TyNat.
  - apply TySucc; eauto.
  - destruct (linear_env_split _ _ _ _ _ _ _ Hsl _ _ H) as [Vc [Vr [Hs [Hc Hr]]]].
    destruct (linear_env_split _ _ _ _ _ _ _ Hr _ _ H0) as [Vs [Vz [Hs' [HeS HeZ]]]].
    eapply TyIter; eauto.
  - apply linear_env_zero in Hsl. subst. apply TyBool.
  - destruct (linear_env_split _ _ _ _ _ _ _ Hsl _ _ H) as [Vc [Vb [Hs [Hc Hb]]]].
    eapply TyIf; eauto.
  - apply TyNew; eauto.
  - destruct (linear_env_split _ _ _ _ _ _ _ Hsl _ _ H) as [V1 [V2 [Hs [He1 He2]]]].
    eapply TySwap; eauto.
  - apply TyFree; eauto.
  - destruct (linear_env_restrict _ _ _ _ _ _ _ Hsl _ H0) as [W [He HW]].
    eapply TyWeak; eauto.
Qed.

Lemma shared_env_id : forall f G L, shared_env f G L G UVar.
Proof. unfold shared_env. intros. apply TyUVar, H. Qed.

Lemma linear_env_id : forall f G L U,
  wf_mask L U -> linear_env f G L L U LVar U.
Proof.
  intros f G L. induction L as [| a L IH]; intros [| b U] Hw;
    unfold wf_mask in Hw; simpl in Hw; try discriminate.
  - constructor.
  - assert (He : linear_env f G L L U LVar U) by (apply IH; unfold wf_mask; lia).
    destruct b.
    + eapply linear_env_ext; [apply linear_env_up_l, He | ].
      intros [| i]; reflexivity.
    + constructor. apply (linear_env_shift_l _ _ _ _ _ _ _ He a).
Qed.

(** Linear beta substitution accounts for the resources of the argument
    and of the body separately, in either mode. *)
Lemma typing_subst_l : forall f G L U V W e v a b,
  has_type f G (a :: L) (true :: U) e b ->
  has_type f G L V v a -> SplitM W V U ->
  has_type f G L W (subst_l v e) b.
Proof.
  intros f G L U V W e v a b He Hv Hs. unfold subst_l.
  eapply typing_subst; [exact He | apply shared_env_id | ].
  eapply EnvOn; [exact Hs | exact Hv | ].
  apply linear_env_id.
  pose proof (typing_wf_mask _ _ _ _ _ _ He) as Hw.
  unfold wf_mask in *. simpl in Hw. lia.
Qed.

(** Shared beta substitution requires a resource-free image even in affine
    mode. Its occurrences may duplicate effects when subsequently evaluated. *)
Lemma typing_subst_u : forall f G L U e v a b,
  has_type f (a :: G) L U e b ->
  has_type f G L (mask_zero (length L)) v a ->
  has_type f G L U (subst_u v e) b.
Proof.
  intros f G L U e v a b He Hv. unfold subst_u.
  eapply typing_subst; [exact He | | apply linear_env_id; eapply typing_wf_mask; exact He].
  intros [| i] c Hi; simpl in *.
  - subst. exact Hv.
  - apply TyUVar, Hi.
Qed.

Lemma linear_env_exchange : forall f G L U a b x y,
  wf_mask L U ->
  linear_env f G (b :: a :: L) (a :: b :: L) (x :: y :: U)
    (fun i => LVar (exchange_ren i)) (y :: x :: U).
Proof.
  intros f G L U a b x y Hw.
  pose proof (linear_env_id f G L U Hw) as He.
  pose proof (linear_env_shift_l _ _ _ _ _ _ _
    (linear_env_shift_l _ _ _ _ _ _ _ He a) b) as Htail.
  assert (Hz : SplitM U (mask_zero (length L)) U).
  { unfold wf_mask in Hw. rewrite <- Hw. apply splitM_right. }
  assert (Ha : has_type f G (b :: a :: L)
    (false :: true :: mask_zero (length L)) (LVar 1) a).
  { change (has_type f G (b :: a :: L)
      (mask_single (length (b :: a :: L)) 1) (LVar 1) a).
    apply TyLVar. reflexivity. }
  assert (Hb : has_type f G (b :: a :: L)
    (true :: false :: mask_zero (length L)) (LVar 0) b).
  { change (has_type f G (b :: a :: L)
      (mask_single (length (b :: a :: L)) 0) (LVar 0) b).
    apply TyLVar. reflexivity. }
  destruct x, y.
  - eapply EnvOn with (W := false :: true :: mask_zero (length L)) (R := true :: false :: U).
    + constructor; constructor; exact Hz.
    + exact Ha.
    + eapply EnvOn with (W := true :: false :: mask_zero (length L)) (R := false :: false :: U).
      * constructor; constructor; exact Hz.
      * exact Hb.
      * exact Htail.
  - eapply EnvOn with (W := false :: true :: mask_zero (length L)) (R := false :: false :: U).
    + constructor; constructor; exact Hz.
    + exact Ha.
    + constructor. exact Htail.
  - constructor.
    eapply EnvOn with (W := true :: false :: mask_zero (length L)) (R := false :: false :: U).
    + constructor; constructor; exact Hz.
    + exact Hb.
    + exact Htail.
  - constructor; constructor; exact Htail.
Qed.

Lemma typing_exchange_resource : forall f G L U e a b c x y,
  has_type f G (a :: b :: L) (x :: y :: U) e c ->
  has_type f G (b :: a :: L) (y :: x :: U) (rename id_ren exchange_ren e) c.
Proof.
  intros f G L U e a b c x y H.
  rewrite <- (subst_rename e UVar (fun i => LVar (exchange_ren i)) id_ren exchange_ren);
    try reflexivity.
  eapply typing_subst; [exact H | apply shared_env_id | ].
  apply linear_env_exchange.
  pose proof (typing_wf_mask _ _ _ _ _ _ H) as Hw.
  unfold wf_mask in *. simpl in Hw. lia.
Qed.
