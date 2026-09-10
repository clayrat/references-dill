(** * Typing of terms, stores and configurations

    Lexical resource variables use a fixed de Bruijn scope and an availability
    mask. Locations instead carry stable natural-number keys, so their owned
    resources are represented directly by a [store_sig] fragment and divided
    with [Split]. Cell typing and global balance connect those fragments to a
    concrete store. Configuration typing additionally requires acyclicity. *)

From Stdlib Require Import List Bool Arith Lia.
From DILLref Require Import Prelude Ty Syntax Index Mask Split Scoping Typing NatMap Graph Store.
Import ListNotations.

(** ** Terms with owned locations

    [has_type_with_loc f G L U R e A] assigns [R] directly to [e]. Unlike the
    lexical scope [L], removing a location never changes the syntax of another
    location, so no positional address mask is needed. Multiplicative rules
    split [R]; additive alternatives share it. Promotion owns no locations. *)

Inductive has_type_with_loc :
    flag -> list ty -> list ty -> mask -> store_sig -> term -> ty -> Prop :=
  | TyLocLVar : forall f G L i a,
      In_opt a (nth_error L i) ->
      has_type_with_loc f G L (mask_single (length L) i) [] (LVar i) a
  | TyLocUVar : forall f G L i a,
      In_opt a (nth_error G i) ->
      has_type_with_loc f G L (mask_zero (length L)) [] (UVar i) a
  | TyLoc : forall f G L l a,
      has_type_with_loc f G L (mask_zero (length L)) [(l, a)]
        (Loc l) (TRef a)
  | TyLocLam : forall f G L U R a b e,
      has_type_with_loc f G (a :: L) (true :: U) R e b ->
      has_type_with_loc f G L U R (Lam a e) (TLolli a b)
  | TyLocApp : forall f G L U U1 U2 R R1 R2 e1 e2 a b,
      SplitM U U1 U2 -> Split R R1 R2 ->
      has_type_with_loc f G L U1 R1 e1 (TLolli a b) ->
      has_type_with_loc f G L U2 R2 e2 a ->
      has_type_with_loc f G L U R (App e1 e2) b
  | TyLocUnit : forall f G L,
      has_type_with_loc f G L (mask_zero (length L)) [] Unit TUnit
  | TyLocLetUnit : forall f G L U U1 U2 R R1 R2 e1 e2 a,
      SplitM U U1 U2 -> Split R R1 R2 ->
      has_type_with_loc f G L U1 R1 e1 TUnit ->
      has_type_with_loc f G L U2 R2 e2 a ->
      has_type_with_loc f G L U R (LetUnit e1 e2) a
  | TyLocPair : forall f G L U U1 U2 R R1 R2 e1 e2 a b,
      SplitM U U1 U2 -> Split R R1 R2 ->
      has_type_with_loc f G L U1 R1 e1 a ->
      has_type_with_loc f G L U2 R2 e2 b ->
      has_type_with_loc f G L U R (Pair e1 e2) (TTensor a b)
  | TyLocLetPair : forall f G L U U1 U2 R R1 R2 e1 e2 a b c,
      SplitM U U1 U2 -> Split R R1 R2 ->
      has_type_with_loc f G L U1 R1 e1 (TTensor a b) ->
      has_type_with_loc f G (b :: a :: L) (true :: true :: U2) R2 e2 c ->
      has_type_with_loc f G L U R (LetPair e1 e2) c
  | TyLocWith : forall f G L U R e1 e2 a b,
      has_type_with_loc f G L U R e1 a ->
      has_type_with_loc f G L U R e2 b ->
      has_type_with_loc f G L U R (With e1 e2) (TWith a b)
  | TyLocFst : forall f G L U R e a b,
      has_type_with_loc f G L U R e (TWith a b) ->
      has_type_with_loc f G L U R (Fst e) a
  | TyLocSnd : forall f G L U R e a b,
      has_type_with_loc f G L U R e (TWith a b) ->
      has_type_with_loc f G L U R (Snd e) b
  | TyLocBang : forall f G L e a,
      has_type_with_loc f G L (mask_zero (length L)) [] e a ->
      has_type_with_loc f G L (mask_zero (length L)) [] (Bang e) (TBang a)
  | TyLocLetBang : forall f G L U U1 U2 R R1 R2 e1 e2 a b,
      SplitM U U1 U2 -> Split R R1 R2 ->
      has_type_with_loc f G L U1 R1 e1 (TBang a) ->
      has_type_with_loc f (a :: G) L U2 R2 e2 b ->
      has_type_with_loc f G L U R (LetBang e1 e2) b
  | TyLocNat : forall f G L n,
      has_type_with_loc f G L (mask_zero (length L)) [] (Nat n) TNat
  | TyLocSucc : forall f G L U R e,
      has_type_with_loc f G L U R e TNat ->
      has_type_with_loc f G L U R (Succ e) TNat
  | TyLocIter : forall f G L U Uc Ur Us Uz R Rc Rr Rs Rz count step seed a,
      SplitM U Uc Ur -> SplitM Ur Us Uz ->
      Split R Rc Rr -> Split Rr Rs Rz ->
      has_type_with_loc f G L Uc Rc count TNat ->
      has_type_with_loc f G L Us Rs step (TBang (TLolli a a)) ->
      has_type_with_loc f G L Uz Rz seed a ->
      has_type_with_loc f G L U R (Iter count step seed) a
  | TyLocBool : forall f G L b,
      has_type_with_loc f G L (mask_zero (length L)) [] (Bool b) TBool
  | TyLocIf : forall f G L U Uc Ub R Rc Rb c e1 e2 a,
      SplitM U Uc Ub -> Split R Rc Rb ->
      has_type_with_loc f G L Uc Rc c TBool ->
      has_type_with_loc f G L Ub Rb e1 a ->
      has_type_with_loc f G L Ub Rb e2 a ->
      has_type_with_loc f G L U R (If c e1 e2) a
  | TyLocNew : forall f G L U R e a,
      has_type_with_loc f G L U R e a ->
      has_type_with_loc f G L U R (New e) (TRef a)
  | TyLocSwap : forall f G L U U1 U2 R R1 R2 e1 e2 a b,
      SplitM U U1 U2 -> Split R R1 R2 ->
      has_type_with_loc f G L U1 R1 e1 (TRef a) ->
      has_type_with_loc f G L U2 R2 e2 b ->
      has_type_with_loc f G L U R (Swap e1 e2) (TTensor a (TRef b))
  | TyLocFree : forall f G L U R e,
      has_type_with_loc f G L U R e (TRef TUnit) ->
      has_type_with_loc f G L U R (Free e) TUnit
  | TyLocWeak : forall G L U V R Q e a,
      has_type_with_loc Affine G L U R e a ->
      mask_le U V -> split_incl R Q ->
      has_type_with_loc Affine G L V Q e a.

Lemma has_type_with_loc_mask : forall f G L U R e a,
  has_type_with_loc f G L U R e a -> wf_mask L U.
Proof.
  intros f G L U R e a H. induction H; unfold wf_mask in *; simpl in *;
    repeat match goal with
    | Hs : SplitM _ _ _ |- _ => apply splitM_length in Hs; destruct Hs
    | Hle : mask_le _ _ |- _ => apply mask_le_length in Hle
    end;
    rewrite ?mask_zero_length, ?mask_single_length in *; lia.
Qed.

#[local] Hint Constructors scoped : runtime_scoping.
Lemma has_type_with_loc_scoped : forall f G L U R e a,
  has_type_with_loc f G L U R e a -> scoped (length G) (length L) e.
Proof.
  intros f G L U R e a H. induction H; simpl in *;
    eauto using lookup_bound, In_opt_Is_some with runtime_scoping.
Qed.

(** Source derivations own no locations. *)
Lemma source_runtime : forall f G L U e a,
  has_type f G L U e a -> has_type_with_loc f G L U [] e a.
Proof.
  intros f G L U e a H. induction H;
    econstructor; eauto using splitM_zero, mask_le_refl, split_left,
      split_incl_refl.
Qed.

Lemma has_type_with_loc_to_affine : forall f G L U R e a,
  has_type_with_loc f G L U R e a ->
  has_type_with_loc Affine G L U R e a.
Proof. intros f G L U R e a H. induction H; econstructor; eassumption. Qed.

Lemma runtime_nat_resources : forall G L U R n a,
  has_type_with_loc Linear G L U R (Nat n) a ->
  U = mask_zero (length L) /\ R = [].
Proof.
  intros G L U R n a H. remember (Nat n) as e eqn:E in H.
  remember Linear as f eqn:Ef in H.
  induction H; inversion E; subst; try discriminate; auto.
Qed.

Lemma runtime_unit_resources : forall G L U R a,
  has_type_with_loc Linear G L U R Unit a ->
  U = mask_zero (length L) /\ R = [].
Proof.
  intros G L U R a H. remember Unit as e eqn:E in H.
  remember Linear as f eqn:Ef in H.
  induction H; inversion E; subst; try discriminate; auto.
Qed.

Lemma split_domain_left : forall (R R1 R2 : store_sig) l,
  Split R R1 R2 -> In l (natmap_domain R1) -> In l (natmap_domain R).
Proof.
  intros R R1 R2 l Hsplit Hin. apply split_map with (f := fst) in Hsplit.
  eapply split_in; [exact Hsplit | left; exact Hin].
Qed.

Lemma split_domain_right : forall (R R1 R2 : store_sig) l,
  Split R R1 R2 -> In l (natmap_domain R2) -> In l (natmap_domain R).
Proof.
  intros R R1 R2 l Hsplit Hin. apply split_map with (f := fst) in Hsplit.
  eapply split_in; [exact Hsplit | right; exact Hin].
Qed.

Lemma split_domain_inv : forall (R R1 R2 : store_sig) l,
  Split R R1 R2 -> In l (natmap_domain R) ->
  In l (natmap_domain R1) \/ In l (natmap_domain R2).
Proof.
  intros R R1 R2 l Hsplit Hin. apply split_map with (f := fst) in Hsplit.
  eapply split_in; eassumption.
Qed.

Lemma split_incl_domain : forall (R Q : store_sig) l,
  split_incl R Q -> In l (natmap_domain R) -> In l (natmap_domain Q).
Proof.
  intros R Q l [F Hsplit] Hin.
  eapply split_domain_left; eassumption.
Qed.

(** Every occurrence, including in suspended code, is present in the owner's
    location context. *)
Lemma runtime_locations_owned : forall f G L U R e a,
  has_type_with_loc f G L U R e a ->
  forall l, In l (locations e) -> In l (natmap_domain R).
Proof.
  intros f G L U R e a H. induction H; intros k Hk; simpl in Hk;
    repeat rewrite in_app_iff in Hk;
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
    try contradiction; try subst k;
    eauto 8 using split_domain_left, split_domain_right, split_incl_domain.
  simpl. auto.
Qed.

(** Linear typing is exact: every location resource assigned to a term has a
    corresponding syntactic occurrence. Additive alternatives may repeat an
    occurrence, but cannot discard it. *)
Lemma linear_runtime_locations_complete : forall G L U R e a,
  has_type_with_loc Linear G L U R e a ->
  forall l, In l (natmap_domain R) -> In l (locations e).
Proof.
  intros G L U R e a H. remember Linear as f eqn:Hlinear in H.
  induction H; intros k Hk; simpl in *; repeat rewrite in_app_iff;
    try contradiction; try discriminate; try solve [eauto 2].
  all: try first
    [ match goal with
      | Hsplit : Split ?whole ?left_context ?right_context,
          IHleft : _ -> forall l,
            In l (natmap_domain ?left_context) -> In l (locations ?left_term),
          IHright : _ -> forall l,
            In l (natmap_domain ?right_context) -> In l (locations ?right_term),
          Hin : In ?key (natmap_domain ?whole)
          |- In ?key (locations ?left_term) \/ In ?key (locations ?right_term) =>
          destruct (split_domain_inv whole left_context right_context key
            Hsplit Hin) as [Hleft | Hright];
          [ left; eapply IHleft; eassumption
          | right; eapply IHright; eassumption ]
      end
    | match goal with
      | Houter : Split ?whole ?count_context ?rest_context,
          Hinner : Split ?rest_context ?step_context ?seed_context,
          IHcount : _ -> forall l,
            In l (natmap_domain ?count_context) -> In l (locations ?count),
          IHstep : _ -> forall l,
            In l (natmap_domain ?step_context) -> In l (locations ?step),
          IHseed : _ -> forall l,
            In l (natmap_domain ?seed_context) -> In l (locations ?seed),
          Hin : In ?key (natmap_domain ?whole)
          |- In ?key (locations ?count) \/ In ?key (locations ?step) \/
             In ?key (locations ?seed) =>
          destruct (split_domain_inv whole count_context rest_context key
            Houter Hin) as [Hcount | Hrest];
          [ left; eapply IHcount; eassumption
          | right; destruct (split_domain_inv rest_context step_context
              seed_context key Hinner Hrest) as [Hstep | Hseed];
            [ left; eapply IHstep; eassumption
            | right; eapply IHseed; eassumption ] ]
      end
    | match goal with
      | Hsplit : Split ?whole ?condition_context ?branch_context,
          IHcondition : _ -> forall l,
            In l (natmap_domain ?condition_context) ->
            In l (locations ?condition),
          IHbranch : _ -> forall l,
            In l (natmap_domain ?branch_context) -> In l (locations ?branch),
          Hin : In ?key (natmap_domain ?whole)
          |- In ?key (locations ?condition) \/ In ?key (locations ?branch) \/ _ =>
          destruct (split_domain_inv whole condition_context branch_context
            key Hsplit Hin) as [Hcondition | Hbranch];
          [ left; eapply IHcondition; eassumption
          | right; left; eapply IHbranch; eassumption ]
      end
    | match goal with
      | IHleft : _ -> forall l,
            In l (natmap_domain ?context) -> In l (locations ?left_term),
          Hin : In ?key (natmap_domain ?context)
          |- In ?key (locations ?left_term) \/ _ =>
          left; eapply IHleft; eassumption
      end ].
Qed.

Lemma runtime_no_locations : forall f G L U e a,
  has_type_with_loc f G L U [] e a -> locations e = [].
Proof.
  intros f G L U e a H.
  destruct (locations e) as [| l ls] eqn:E; [reflexivity | exfalso].
  assert (Hin : In l (locations e)) by (rewrite E; simpl; auto).
  pose proof (runtime_locations_owned _ _ _ _ _ _ _ H l Hin). contradiction.
Qed.

Lemma runtime_bang_no_locations : forall f G L U R e a,
  has_type_with_loc f G L U R (Bang e) a -> locations e = [].
Proof.
  intros f G L U R e a H. remember (Bang e) as t eqn:E in H.
  induction H; inversion E; subst; eauto using runtime_no_locations.
Qed.

Lemma runtime_swap_no_self_reference : forall f G L U R l v a,
  NoDup (natmap_domain R) ->
  has_type_with_loc f G L U R (Swap (Loc l) v) a ->
  ~ In l (locations v).
Proof.
  intros f G L U R l v a Hnd H.
  remember (Swap (Loc l) v) as e eqn:E in H.
  induction H; inversion E; subst; eauto.
  - intros Hin.
    assert (Hl : In l (natmap_domain R1)).
    { eapply runtime_locations_owned; [exact H1 | simpl; auto]. }
    assert (Hv : In l (natmap_domain R2)).
    { eapply runtime_locations_owned; eassumption. }
    eapply split_disjoint with
      (l := natmap_domain R) (ls := natmap_domain R1)
      (rs := natmap_domain R2) (x := l); eauto.
    apply split_map with (f := fst) in H0. exact H0.
  - apply IHhas_type_with_loc.
    + destruct H1 as [F H1]. eapply split_nodup_left.
      * apply split_map with (f := fst) in H1. exact H1.
      * exact Hnd.
    + reflexivity.
Qed.

(** ** Signature partitions *)

Lemma split_store_sig_update : forall l a (S S1 S2 : store_sig),
  Split S S1 S2 ->
  Split (store_sig_update l a S)
    (store_sig_update l a S1) (store_sig_update l a S2).
Proof.
  intros l a S S1 S2 Hsplit.
  unfold store_sig_update, natmap_replace. apply split_map. exact Hsplit.
Qed.

Lemma split_domain_disjoint : forall (S S1 S2 : store_sig) l,
  Split S S1 S2 -> NoDup (natmap_domain S) ->
  In l (natmap_domain S1) -> ~ In l (natmap_domain S2).
Proof.
  intros S S1 S2 l Hsplit Hnd Hin.
  apply split_map with (f := fst) in Hsplit.
  eapply split_disjoint; eassumption.
Qed.

Lemma store_sig_update_single : forall l a b,
  store_sig_update l b [(l, a)] = [(l, b)].
Proof.
  intros. unfold store_sig_update, natmap_replace. cbn [map fst snd].
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma store_sig_update_absent : forall l a S,
  ~ In l (natmap_domain S) -> store_sig_update l a S = S.
Proof. intros. apply natmap_replace_absent. exact H. Qed.

Lemma split_store_sig_remove : forall l (S S1 S2 : store_sig),
  Split S S1 S2 ->
  Split (store_sig_remove l S)
    (store_sig_remove l S1) (store_sig_remove l S2).
Proof.
  intros l S S1 S2 Hsplit. unfold store_sig_remove.
  repeat rewrite natmap_remove_filter. apply split_filter. exact Hsplit.
Qed.

Lemma store_sig_remove_absent : forall l S,
  ~ In l (natmap_domain S) -> store_sig_remove l S = S.
Proof. intros. apply natmap_remove_absent. exact H. Qed.

Lemma store_sig_remove_single : forall l a,
  store_sig_remove l [(l, a)] = [].
Proof.
  intros. unfold store_sig_remove. cbn [natmap_remove].
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(** ** Cell typing and resource balance *)

Inductive cells_typed (f : flag) : store_sig -> store -> store_sig -> Prop :=
  | CellsNil : cells_typed f [] [] []
  | CellsCons : forall l a v K s R Rc Rt,
      value v -> has_type_with_loc f [] [] [] Rc v a ->
      Split R Rc Rt -> cells_typed f K s Rt ->
      cells_typed f ((l, a) :: K) ((l, v) :: s) R.

Inductive store_balance (f : flag) (s : store) (e : term) (a : ty) : Prop :=
  | StoreBalance : forall S Rterm Rrest Rcells Rfree,
      NoDup (natmap_domain S) ->
      cells_typed f S s Rcells ->
      has_type_with_loc f [] [] [] Rterm e a ->
      Split S Rterm Rrest -> Split Rrest Rcells Rfree ->
      (f = Linear -> Rfree = []) ->
      store_balance f s e a.

Lemma cells_typed_domain : forall f K s R,
  cells_typed f K s R -> natmap_domain K = natmap_domain s.
Proof. intros f K s R H. induction H; simpl; congruence. Qed.

Lemma cells_locations_owned : forall f K s R,
  cells_typed f K s R ->
  forall x l, store_edge s x l -> In l (natmap_domain R).
Proof.
  intros f K s R H. induction H; intros x k [w [Hin Hloc]]; simpl in Hin.
  - contradiction.
  - destruct Hin as [E | Hin].
    + injection E as -> ->. eapply split_domain_left; [exact H1 | ].
      eapply runtime_locations_owned; eassumption.
    + eapply split_domain_right; [exact H1 | ].
      apply IHcells_typed with (x := x). exists w. auto.
Qed.

Lemma linear_cells_locations_complete : forall K s R,
  cells_typed Linear K s R ->
  forall l, In l (natmap_domain R) -> exists owner, store_edge s owner l.
Proof.
  intros K s R Hcells. induction Hcells; intros k Hk.
  - contradiction.
  - destruct (split_domain_inv R Rc Rt k H1 Hk) as [Hcurrent | Htail].
    + exists l, v. split; [left; reflexivity | ].
      eapply linear_runtime_locations_complete; eassumption.
    + destruct (IHHcells k Htail) as [owner [w [Hin Hloc]]].
      exists owner, w. split; [right; exact Hin | exact Hloc].
Qed.

Lemma balance_unique_addresses : forall f s e a,
  store_balance f s e a -> NoDup (natmap_domain s).
Proof.
  intros f s e a [S Rt Rr Rc Rf Hnd Hcells Hterm Hsplit Hrest Hmode].
  rewrite <- (cells_typed_domain _ _ _ _ Hcells). exact Hnd.
Qed.

Lemma balance_allocated : forall f s e a l,
  store_balance f s e a ->
  In l (locations e) \/ (exists x, store_edge s x l) ->
  In l (natmap_domain s).
Proof.
  intros f s e a l
    [S Rt Rr Rc Rf Hnd Hcells Hterm Hsplit Hrest Hmode] Hloc.
  rewrite <- (cells_typed_domain _ _ _ _ Hcells).
  apply split_map with (f := fst) in Hsplit.
  apply split_map with (f := fst) in Hrest.
  eapply split_in; [exact Hsplit | ]. destruct Hloc as [Hloc | [x Hloc]].
  - left. eapply runtime_locations_owned; eassumption.
  - right. eapply split_in; [exact Hrest | left].
    eapply cells_locations_owned; eassumption.
Qed.

Lemma balance_root_no_incoming : forall f s e a l,
  store_balance f s e a -> In l (locations e) ->
  forall x, ~ store_edge s x l.
Proof.
  intros f s e a l
    [S Rt Rr Rc Rf Hnd Hcells Hterm Hsplit Hrest Hmode] Hloc x Hedge.
  apply split_map with (f := fst) in Hsplit.
  apply split_map with (f := fst) in Hrest.
  eapply split_disjoint with
    (l := natmap_domain S) (ls := natmap_domain Rt)
    (rs := natmap_domain Rr) (x := l); eauto.
  - eapply runtime_locations_owned; eassumption.
  - eapply split_in; [exact Hrest | left].
    eapply cells_locations_owned; eassumption.
Qed.

(** Exact linear balance assigns every allocated cell either to the running
    term or to a cell content. *)
Lemma linear_balance_root_or_owned : forall s e a l,
  store_balance Linear s e a -> In l (natmap_domain s) ->
  In l (locations e) \/ exists owner, store_edge s owner l.
Proof.
  intros s e a l
    [S Rt Rr Rc Rf Hnd Hcells Hterm Hsplit Hrest Hmode] Hin.
  specialize (Hmode eq_refl). subst Rf.
  apply split_left_inv in Hrest. subst Rc.
  rewrite <- (cells_typed_domain _ _ _ _ Hcells) in Hin.
  destruct (split_domain_inv S Rt Rr l Hsplit Hin) as
    [Hterm_owned | Hcells_owned].
  - left. eapply linear_runtime_locations_complete; eassumption.
  - right. eapply linear_cells_locations_complete; eassumption.
Qed.

(** ** Typed configurations *)

Definition configuration_typed (f : flag) (s : store) (e : term) (a : ty) : Prop :=
  store_balance f s e a /\ store_acyclic s.

Lemma source_configuration : forall f e a,
  has_type f [] [] [] e a -> configuration_typed f [] e a.
Proof.
  intros f e a H. split; [ | apply store_acyclic_empty].
  eapply StoreBalance with (S := []) (Rfree := []);
    try constructor; try reflexivity.
  apply source_runtime. exact H.
Qed.

Definition root_reachable (s : store) (e : term) (l : nat) : Prop :=
  graph_root_reachable (store_edge s) (fun root => In root (locations e)) l.

(** Every allocated cell of a linear typed configuration is owned along a
    finite path starting in the running term. *)
Theorem linear_configuration_root_reachable : forall s e a l,
  configuration_typed Linear s e a -> In l (natmap_domain s) ->
  root_reachable s e l.
Proof.
  intros s e a l [Hbalance Hacy] Hin.
  unfold root_reachable.
  eapply finite_acyclic_root_reachable with
    (vertices := natmap_domain s).
  - intros owner target [v [Hentry Hlocation]].
    apply (in_map fst) in Hentry. exact Hentry.
  - exact Hacy.
  - intros target Htarget.
    eapply linear_balance_root_or_owned; eassumption.
  - exact Hin.
Qed.
