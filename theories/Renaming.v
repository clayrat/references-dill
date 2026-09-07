(** * Renaming in two independent scopes

    Each zone has its own map of de Bruijn indices. Lifting fixes a newly
    bound index and shifts the images of the old indices. Store addresses
    are never renamed. *)

From Stdlib Require Import List Arith Lia.
From DILLref Require Import Ty Syntax Index Scoping Mask OPE Typing.
Import ListNotations.

Fixpoint rename (ru rl : nat -> nat) (e : term) : term :=
  match e with
  | LVar i => LVar (rl i)
  | UVar i => UVar (ru i)
  | Loc a => Loc a
  | Lam a e => Lam a (rename ru (up_ren rl) e)
  | App e1 e2 => App (rename ru rl e1) (rename ru rl e2)
  | Unit => Unit
  | LetUnit e1 e2 => LetUnit (rename ru rl e1) (rename ru rl e2)
  | Pair e1 e2 => Pair (rename ru rl e1) (rename ru rl e2)
  | LetPair e1 e2 =>
      LetPair (rename ru rl e1) (rename ru (up_ren (up_ren rl)) e2)
  | With e1 e2 => With (rename ru rl e1) (rename ru rl e2)
  | Fst e => Fst (rename ru rl e)
  | Snd e => Snd (rename ru rl e)
  | Bang e => Bang (rename ru rl e)
  | LetBang e1 e2 => LetBang (rename ru rl e1) (rename (up_ren ru) rl e2)
  | Nat n => Nat n
  | Succ e => Succ (rename ru rl e)
  | Iter c s z => Iter (rename ru rl c) (rename ru rl s) (rename ru rl z)
  | Bool b => Bool b
  | If c e1 e2 => If (rename ru rl c) (rename ru rl e1) (rename ru rl e2)
  | New e => New (rename ru rl e)
  | Swap e1 e2 => Swap (rename ru rl e1) (rename ru rl e2)
  | Free e => Free (rename ru rl e)
  end.

Lemma rename_ext : forall e ru rl su sl,
  (forall i, ru i = su i) -> (forall i, rl i = sl i) ->
  rename ru rl e = rename su sl e.
Proof.
  induction e; intros; simpl; f_equal; eauto using up_ren_ext.
Qed.

Lemma rename_id : forall e, rename id_ren id_ren e = e.
Proof.
  assert (H : forall e ru rl, (forall i, ru i = i) ->
    (forall i, rl i = i) -> rename ru rl e = e).
  { induction e; intros; simpl; f_equal; eauto using up_ren_id. }
  intros. apply H; reflexivity.
Qed.

Lemma rename_comp : forall e ru rl su sl,
  rename su sl (rename ru rl e) =
  rename (fun i => su (ru i)) (fun i => sl (rl i)) e.
Proof.
  induction e; intros; simpl; try (f_equal; auto; fail).
  - f_equal. rewrite IHe. apply rename_ext; intros [| i]; reflexivity.
  - f_equal; auto. rewrite IHe2. apply rename_ext; intros [| [| i]]; reflexivity.
  - f_equal; auto. rewrite IHe2. apply rename_ext; intros [| i]; reflexivity.
Qed.

Lemma rename_loc_free : forall e ru rl, loc_free (rename ru rl e) = loc_free e.
Proof.
  induction e; intros; simpl; rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; reflexivity.
Qed.

#[local] Hint Constructors scoped : renaming.
#[local] Hint Resolve up_ren_scoped : renaming.

Lemma rename_scoped : forall g l e, scoped g l e ->
  forall g' l' ru rl, ren_scoped g g' ru -> ren_scoped l l' rl ->
  scoped g' l' (rename ru rl e).
Proof.
  intros g l e H. induction H; intros; simpl; eauto 8 with renaming.
  all: constructor; unfold ren_scoped in *; eauto.
Qed.

(** Shared renamings can identify variables. Resource scope extension below
    uses an OPE, which cannot identify or permute positions. Newly inserted
    resource positions are unavailable; this is valid even in linear mode. *)
Lemma typing_rename : forall f G L U e a,
  has_type f G L U e a -> forall G' L' ru E,
  ren_context G G' ru -> ope L' E L ->
  has_type f G' L' (mask_comp E U) (rename ru (ope_index E) e) a.
Proof.
  intros f G L U e a H. induction H; intros G' L' ru E HG HE; simpl;
    try rewrite (ope_mask_zero _ _ _ HE).
  - rewrite (ope_mask_single _ _ _ _ _ HE H).
    apply TyLVar. eapply ope_index_nth; eassumption.
  - apply TyUVar. apply HG, H.
  - apply TyLam.
    change (has_type f G' (a :: L') (mask_comp (true :: E) (true :: U))
      (rename ru (ope_index (true :: E)) e) b).
    apply IHhas_type; [exact HG | constructor; exact HE].
  - eapply TyApp; eauto using ope_splitM, typing_wf_mask, splitM_wf_whole.
  - apply TyUnit.
  - eapply TyLetUnit; eauto using ope_splitM, typing_wf_mask, splitM_wf_whole.
  - eapply TyPair; eauto using ope_splitM, typing_wf_mask, splitM_wf_whole.
  - eapply TyLetPair.
    + eapply ope_splitM; eauto using typing_wf_mask, splitM_wf_whole.
    + eapply IHhas_type1; eassumption.
    + change (has_type f G' (b :: a :: L')
        (mask_comp (true :: true :: E) (true :: true :: U2))
        (rename ru (ope_index (true :: true :: E)) e2) c).
      apply IHhas_type2; [exact HG | constructor; constructor; exact HE].
  - apply TyWith; eauto.
  - eapply TyFst; eauto.
  - eapply TySnd; eauto.
  - apply TyBang. rewrite <- (ope_mask_zero _ _ _ HE). eauto.
  - eapply TyLetBang; eauto using ope_splitM, typing_wf_mask, splitM_wf_whole, up_ren_context.
  - apply TyNat.
  - apply TySucc; eauto.
  - eapply TyIter; eauto using ope_splitM, typing_wf_mask, splitM_wf_whole.
  - apply TyBool.
  - eapply TyIf; eauto using ope_splitM, typing_wf_mask, splitM_wf_whole.
  - apply TyNew; eauto.
  - eapply TySwap; eauto using ope_splitM, typing_wf_mask, splitM_wf_whole.
  - apply TyFree; eauto.
  - eapply TyWeak; eauto using ope_mask_le, typing_wf_mask.
Qed.

Lemma typing_rename_shared : forall f G L U e a G' ru,
  has_type f G L U e a -> ren_context G G' ru ->
  has_type f G' L U (rename ru id_ren e) a.
Proof.
  intros f G L U e a G' ru H Hr.
  pose proof (typing_rename _ _ _ _ _ _ H G' L ru (mask_id (length L)) Hr (ope_id L)) as Ht.
  rewrite (ope_comp_id_l _ _ _ (ope_select _ _ (typing_wf_mask _ _ _ _ _ _ H))) in Ht.
  erewrite rename_ext in Ht; [exact Ht | reflexivity | apply ope_index_id].
Qed.

Lemma typing_weaken_shared : forall f G L U e a b,
  has_type f G L U e a -> has_type f (b :: G) L U (rename S id_ren e) a.
Proof. intros. eapply typing_rename_shared; eauto using ren_context_shift. Qed.

Lemma typing_weaken_resource : forall f G L U e a b,
  has_type f G L U e a ->
  has_type f G (b :: L) (false :: U) (rename id_ren S e) a.
Proof.
  intros f G L U e a b H.
  pose proof (typing_rename _ _ _ _ _ _ H G (b :: L) id_ren
    (mask_wk (length L)) (ren_context_id G) (ope_wk b L)) as Ht.
  unfold mask_wk in Ht. simpl in Ht.
  rewrite (ope_comp_id_l _ _ _ (ope_select _ _ (typing_wf_mask _ _ _ _ _ _ H))) in Ht.
  erewrite rename_ext in Ht; [exact Ht | reflexivity | ].
  intros i. simpl. rewrite ope_index_id. reflexivity.
Qed.

(** Identify the two innermost shared hypotheses of the same type. *)
Lemma typing_contract_shared : forall f G L U e a b,
  has_type f (a :: a :: G) L U e b ->
  has_type f (a :: G) L U (rename contract_ren id_ren e) b.
Proof.
  intros. eapply typing_rename_shared; [exact H | ].
  intros [| [| i]] c Hi; exact Hi.
Qed.
