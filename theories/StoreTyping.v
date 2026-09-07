(** * Typing of terms, stores and configurations

    Terms with addresses are checked against a store signature. Cell typing
    and resource balance connect those judgments to a concrete store, and
    configuration typing additionally requires acyclicity. All judgments
    live in [Prop] and are erased by extraction. *)

From Stdlib Require Import List Bool Arith Lia.
From DILLref Require Import Prelude Ty Syntax Index Mask Scoping Typing NatMap NatMapMask Store.
Import ListNotations.

(** ** Terms with address resources

    [runtime_type f S G L U R e A] keeps lexical resource positions [U]
    separate from address resources [R], whose positions refer to entries
    of [S]. A [Loc] contains the entry's key, never its position. Bindings
    extend only lexical scopes; multiplicative rules divide both masks.

    Suspended bodies are checked too. Promotion has zero demand in both
    resource zones, even in affine mode. Additive alternatives share masks;
    they may mention the same address without duplicating ownership. *)

Inductive runtime_type :
    flag -> store_sig -> list ty -> list ty -> mask -> mask -> term -> ty -> Prop :=
  | RTLVar : forall f S G L i a,
      In_opt a (nth_error L i) ->
      runtime_type f S G L (mask_single (length L) i) (mask_zero (length S)) (LVar i) a
  | RTUVar : forall f S G L i a,
      In_opt a (nth_error G i) ->
      runtime_type f S G L (mask_zero (length L)) (mask_zero (length S)) (UVar i) a
  | RTLoc : forall f S G L i l a,
      In_opt (l, a) (nth_error S i) ->
      runtime_type f S G L (mask_zero (length L)) (mask_single (length S) i)
        (Loc l) (TRef a)
  | RTLam : forall f S G L U R a b e,
      runtime_type f S G (a :: L) (true :: U) R e b ->
      runtime_type f S G L U R (Lam a e) (TLolli a b)
  | RTApp : forall f S G L U U1 U2 R R1 R2 e1 e2 a b,
      SplitM U U1 U2 -> SplitM R R1 R2 ->
      runtime_type f S G L U1 R1 e1 (TLolli a b) -> runtime_type f S G L U2 R2 e2 a ->
      runtime_type f S G L U R (App e1 e2) b
  | RTUnit : forall f S G L,
      runtime_type f S G L (mask_zero (length L)) (mask_zero (length S)) Unit TUnit
  | RTLetUnit : forall f S G L U U1 U2 R R1 R2 e1 e2 a,
      SplitM U U1 U2 -> SplitM R R1 R2 ->
      runtime_type f S G L U1 R1 e1 TUnit -> runtime_type f S G L U2 R2 e2 a ->
      runtime_type f S G L U R (LetUnit e1 e2) a
  | RTPair : forall f S G L U U1 U2 R R1 R2 e1 e2 a b,
      SplitM U U1 U2 -> SplitM R R1 R2 ->
      runtime_type f S G L U1 R1 e1 a -> runtime_type f S G L U2 R2 e2 b ->
      runtime_type f S G L U R (Pair e1 e2) (TTensor a b)
  | RTLetPair : forall f S G L U U1 U2 R R1 R2 e1 e2 a b c,
      SplitM U U1 U2 -> SplitM R R1 R2 ->
      runtime_type f S G L U1 R1 e1 (TTensor a b) ->
      runtime_type f S G (b :: a :: L) (true :: true :: U2) R2 e2 c ->
      runtime_type f S G L U R (LetPair e1 e2) c
  | RTWith : forall f S G L U R e1 e2 a b,
      runtime_type f S G L U R e1 a -> runtime_type f S G L U R e2 b ->
      runtime_type f S G L U R (With e1 e2) (TWith a b)
  | RTFst : forall f S G L U R e a b,
      runtime_type f S G L U R e (TWith a b) -> runtime_type f S G L U R (Fst e) a
  | RTSnd : forall f S G L U R e a b,
      runtime_type f S G L U R e (TWith a b) -> runtime_type f S G L U R (Snd e) b
  | RTBang : forall f S G L e a,
      runtime_type f S G L (mask_zero (length L)) (mask_zero (length S)) e a ->
      runtime_type f S G L (mask_zero (length L)) (mask_zero (length S)) (Bang e) (TBang a)
  | RTLetBang : forall f S G L U U1 U2 R R1 R2 e1 e2 a b,
      SplitM U U1 U2 -> SplitM R R1 R2 ->
      runtime_type f S G L U1 R1 e1 (TBang a) ->
      runtime_type f S (a :: G) L U2 R2 e2 b ->
      runtime_type f S G L U R (LetBang e1 e2) b
  | RTNat : forall f S G L n,
      runtime_type f S G L (mask_zero (length L)) (mask_zero (length S)) (Nat n) TNat
  | RTSucc : forall f S G L U R e,
      runtime_type f S G L U R e TNat -> runtime_type f S G L U R (Succ e) TNat
  | RTIter : forall f S G L U Uc Ur Us Uz R Rc Rr Rs Rz count step seed a,
      SplitM U Uc Ur -> SplitM Ur Us Uz -> SplitM R Rc Rr -> SplitM Rr Rs Rz ->
      runtime_type f S G L Uc Rc count TNat ->
      runtime_type f S G L Us Rs step (TBang (TLolli a a)) ->
      runtime_type f S G L Uz Rz seed a ->
      runtime_type f S G L U R (Iter count step seed) a
  | RTBool : forall f S G L b,
      runtime_type f S G L (mask_zero (length L)) (mask_zero (length S)) (Bool b) TBool
  | RTIf : forall f S G L U Uc Ub R Rc Rb c e1 e2 a,
      SplitM U Uc Ub -> SplitM R Rc Rb -> runtime_type f S G L Uc Rc c TBool ->
      runtime_type f S G L Ub Rb e1 a -> runtime_type f S G L Ub Rb e2 a ->
      runtime_type f S G L U R (If c e1 e2) a
  | RTNew : forall f S G L U R e a,
      runtime_type f S G L U R e a -> runtime_type f S G L U R (New e) (TRef a)
  | RTSwap : forall f S G L U U1 U2 R R1 R2 e1 e2 a b,
      SplitM U U1 U2 -> SplitM R R1 R2 ->
      runtime_type f S G L U1 R1 e1 (TRef a) -> runtime_type f S G L U2 R2 e2 b ->
      runtime_type f S G L U R (Swap e1 e2) (TTensor a (TRef b))
  | RTFree : forall f S G L U R e,
      runtime_type f S G L U R e (TRef TUnit) -> runtime_type f S G L U R (Free e) TUnit
  | RTWeak : forall S G L U V R Q e a,
      runtime_type Affine S G L U R e a -> mask_le U V -> mask_le R Q ->
      runtime_type Affine S G L V Q e a.

Lemma runtime_type_masks : forall f S G L U R e a,
  runtime_type f S G L U R e a -> wf_mask L U /\ wf_mask S R.
Proof.
  intros f S G L U R e a H. induction H;
    unfold wf_mask in *; simpl in *;
    repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : SplitM _ _ _ |- _ =>
        apply splitM_length in H; destruct H
    | H : mask_le _ _ |- _ => apply mask_le_length in H
    end;
    rewrite ?mask_zero_length, ?mask_single_length in *; split; lia.
Qed.

#[local] Hint Constructors scoped : runtime_scoping.
Lemma runtime_type_scoped : forall f S G L U R e a,
  runtime_type f S G L U R e a -> scoped (length G) (length L) e.
Proof.
  intros f S G L U R e a H. induction H; simpl in *;
    eauto using lookup_bound with runtime_scoping.
Qed.

(** Source derivations embed with no address demand, at any signature. *)
Lemma source_runtime : forall f G L U e a, has_type f G L U e a ->
  forall S, runtime_type f S G L U (mask_zero (length S)) e a.
Proof.
  intros f G L U e a H. induction H; intros S;
    econstructor; eauto using splitM_zero, mask_le_refl.
Qed.

Lemma runtime_type_to_affine : forall f S G L U R e a,
  runtime_type f S G L U R e a -> runtime_type Affine S G L U R e a.
Proof. intros f S G L U R e a H. induction H; econstructor; eassumption. Qed.

Lemma runtime_nat_resources : forall S G L U R n a,
  runtime_type Linear S G L U R (Nat n) a ->
  U = mask_zero (length L) /\ R = mask_zero (length S).
Proof.
  intros S G L U R n a H. remember (Nat n) as e eqn:E in H.
  remember Linear as f eqn:Ef in H.
  induction H; inversion E; subst; try discriminate; auto.
Qed.

Lemma runtime_unit_resources : forall S G L U R a,
  runtime_type Linear S G L U R Unit a ->
  U = mask_zero (length L) /\ R = mask_zero (length S).
Proof.
  intros S G L U R a H. remember Unit as e eqn:E in H.
  remember Linear as f eqn:Ef in H.
  induction H; inversion E; subst; try discriminate; auto.
Qed.

(** Every occurrence, including in suspended code, needs its owner's right. *)
Lemma runtime_locations_available : forall f S G L U R e a,
  runtime_type f S G L U R e a ->
  forall l, In l (locations e) -> masked_key S R l.
Proof.
  intros f S G L U R e a H. induction H; intros k Hk; simpl in Hk;
    repeat rewrite in_app_iff in Hk; try contradiction;
    repeat match goal with H : _ \/ _ |- _ => destruct H end; try contradiction;
    try subst k;
    eauto 8 using masked_key_mono, splitM_le_l, splitM_le_r,
      mask_single_nth, lookup_bound.
  exists i, a. split; eauto using mask_single_nth, lookup_bound.
Qed.

Lemma runtime_zero_locations : forall f S G L U e a,
  runtime_type f S G L U (mask_zero (length S)) e a -> locations e = [].
Proof.
  intros f S G L U e a H.
  destruct (locations e) as [| l ls] eqn:E; [reflexivity | exfalso].
  assert (Hin : In l (locations e)) by (rewrite E; simpl; auto).
  destruct (runtime_locations_available _ _ _ _ _ _ _ _ H l Hin)
    as [i [b [_ Hi]]].
  exact (mask_zero_no_true (length S) i Hi).
Qed.

Lemma runtime_bang_no_locations : forall f S G L U R e a,
  runtime_type f S G L U R (Bang e) a -> locations e = [].
Proof.
  intros f S G L U R e a H. remember (Bang e) as t eqn:E in H.
  induction H; inversion E; subst; eauto using runtime_zero_locations.
Qed.

Lemma runtime_swap_no_self_reference : forall f S G L U R l v a,
  NoDup (natmap_domain S) -> runtime_type f S G L U R (Swap (Loc l) v) a ->
  ~ In l (locations v).
Proof.
  intros f S G L U R l v a Hnd H.
  remember (Swap (Loc l) v) as e eqn:E in H.
  induction H; inversion E; subst; eauto.
  intros Hin. eapply masked_key_disjoint; eauto;
    eapply runtime_locations_available; eauto; simpl; auto.
Qed.

(** ** Cell typing and resource balance

    The full signature supplies one exclusive right per address. The term
    and each stored value receive disjoint masks over that same signature.
    A residual mask permits unowned cells only in affine mode. Balance
    accounts for ownership but permits cycles; configurations additionally
    require [store_acyclic]. *)

(** [K] tracks the remaining cells and their content types; every value is
    checked against the full [S], with both lexical scopes empty. Matching
    list order is a representation convention, not an ordering of addresses. *)
Inductive cells_typed (f : flag) (S : store_sig) : store_sig -> store -> mask -> Prop :=
  | CellsNil : cells_typed f S [] [] (mask_zero (length S))
  | CellsCons : forall l a v K s R Rc Rt,
      value v -> runtime_type f S [] [] [] Rc v a ->
      SplitM R Rc Rt -> cells_typed f S K s Rt ->
      cells_typed f S ((l, a) :: K) ((l, v) :: s) R.

Inductive store_balance (f : flag) (s : store) (e : term) (a : ty) : Prop :=
  | StoreBalance : forall S Rterm Rrest Rcells Rfree,
      NoDup (natmap_domain S) ->
      cells_typed f S S s Rcells -> runtime_type f S [] [] [] Rterm e a ->
      SplitM (mask_id (length S)) Rterm Rrest -> SplitM Rrest Rcells Rfree ->
      (f = Linear -> Rfree = mask_zero (length S)) ->
      store_balance f s e a.

Lemma cells_typed_domain : forall f S K s R,
  cells_typed f S K s R -> natmap_domain K = natmap_domain s.
Proof. intros f S K s R H. induction H; simpl; congruence. Qed.

Lemma cells_typed_mask : forall f S K s R,
  cells_typed f S K s R -> wf_mask S R.
Proof.
  intros f S K s R H. induction H.
  - apply mask_zero_length.
  - eapply splitM_wf_whole; eauto. eapply runtime_type_masks; eassumption.
Qed.

Lemma cells_locations_available : forall f S K s R,
  cells_typed f S K s R ->
  forall x l, store_edge s x l -> masked_key S R l.
Proof.
  intros f S K s R H. induction H; intros x k [w [Hin Hloc]]; simpl in Hin.
  - contradiction.
  - destruct Hin as [E | Hin].
    + injection E as -> ->. eapply masked_key_mono;
        [eapply splitM_le_l; eassumption | ].
      eapply runtime_locations_available; eassumption.
    + eapply masked_key_mono; [eapply splitM_le_r; eassumption | ].
      apply IHcells_typed with (x := x). exists w. auto.
Qed.

Lemma balance_unique_addresses : forall f s e a,
  store_balance f s e a -> NoDup (natmap_domain s).
Proof.
  intros f s e a H. destruct H as [S Rt Rr Rc Rf Hnd Hcells Hterm Hsplit Hrest Hmode].
  rewrite <- (cells_typed_domain _ _ _ _ _ Hcells). assumption.
Qed.

(** Static absence of dangling addresses, including inside stored closures.
    Dynamic safety also needs preservation through each operational step. *)
Lemma balance_allocated : forall f s e a l,
  store_balance f s e a ->
  In l (locations e) \/ (exists x, store_edge s x l) -> In l (natmap_domain s).
Proof.
  intros f s e a l H Hloc.
  destruct H as [S Rt Rr Rc Rf Hnd Hcells Hterm Hsplit Hrest Hmode].
  rewrite <- (cells_typed_domain _ _ _ _ _ Hcells).
  destruct Hloc as [Hloc | [x Hloc]]; eapply masked_key_domain.
  - eapply runtime_locations_available; eassumption.
  - eapply cells_locations_available; eassumption.
Qed.

(** An address mentioned by the running term cannot also be owned by any
    stored value. This includes references hidden under suspensions. *)
Lemma balance_root_no_incoming : forall f s e a l,
  store_balance f s e a -> In l (locations e) -> forall x, ~ store_edge s x l.
Proof.
  intros f s e a l H Hloc x Hedge.
  destruct H as [S Rt Rr Rc Rf Hnd Hcells Hterm Hsplit Hrest Hmode].
  eapply masked_key_disjoint; [exact Hnd | exact Hsplit | | ].
  - eapply runtime_locations_available; eassumption.
  - eapply masked_key_mono; [eapply splitM_le_l; exact Hrest | ].
    eapply cells_locations_available; eassumption.
Qed.

(** ** Typed configurations *)

Definition configuration_typed (f : flag) (s : store) (e : term) (a : ty) : Prop :=
  store_balance f s e a /\ store_acyclic s.

(** Graph preservation for a primitive swap at the root. Typing supplies
    both graph side conditions, in either mode. Full step preservation also
    needs runtime substitution, signature transport for the strong update,
    and an evaluation-context theorem. *)
Lemma balanced_swap_acyclic : forall f s l v a,
  configuration_typed f s (Swap (Loc l) v) a ->
  store_acyclic (natmap_replace l v s).
Proof.
  intros f s l v a [Hbalance Hacy].
  apply store_acyclic_replace; [exact Hacy | | ].
  - eapply balance_root_no_incoming; [exact Hbalance | simpl; auto].
  - destruct Hbalance as [S Rt Rr Rc Rf Hnd Hcells Hterm Hsplit Hrest Hmode].
    eapply runtime_swap_no_self_reference; eassumption.
Qed.

Lemma source_configuration : forall f e a,
  has_type f [] [] [] e a -> configuration_typed f [] e a.
Proof.
  intros f e a H. split; [ | apply store_acyclic_empty].
  eapply StoreBalance with (S := []) (Rfree := []);
    try constructor; try reflexivity.
  apply source_runtime with (S := []) in H. exact H.
Qed.

(** TODO: runtime substitution and signature transport, store balance and
    acyclicity preservation for every operational rule, and root reachability
    of all cells in balanced acyclic linear configurations. *)
