(** * Inversion principles for typing terms with locations

    Syntax-directed generation, canonical forms and typed cell lookup are
    shared by preservation and progress.  They depend only on static typing
    and store structure, not on the operational relation. *)

From Stdlib Require Import List Bool Arith.
From DILLref Require Import Prelude Ty Syntax Mask Split NatMap Store StoreTyping.
Import ListNotations.
Local Opaque split_incl.

Definition has_type_with_loc_head (f : flag) (G L : list ty)
    (U : mask) (R : store_sig) (e : term) (a : ty) : Prop :=
  match e with
  | LVar i => In_opt a (nth_error L i) /\
      U = mask_single (length L) i /\ R = []
  | UVar i => In_opt a (nth_error G i) /\
      U = mask_zero (length L) /\ R = []
  | Loc l => exists b, a = TRef b /\
      U = mask_zero (length L) /\ R = [(l, b)]
  | Lam b body => exists c, a = TLolli b c /\
      has_type_with_loc f G (b :: L) (true :: U) R body c
  | App e1 e2 => exists U1 U2 R1 R2 b,
      SplitM U U1 U2 /\ Split R R1 R2 /\
      has_type_with_loc f G L U1 R1 e1 (TLolli b a) /\
      has_type_with_loc f G L U2 R2 e2 b
  | Unit => a = TUnit /\ U = mask_zero (length L) /\ R = []
  | LetUnit e1 e2 => exists U1 U2 R1 R2,
      SplitM U U1 U2 /\ Split R R1 R2 /\
      has_type_with_loc f G L U1 R1 e1 TUnit /\
      has_type_with_loc f G L U2 R2 e2 a
  | Pair e1 e2 => exists U1 U2 R1 R2 b c,
      a = TTensor b c /\ SplitM U U1 U2 /\ Split R R1 R2 /\
      has_type_with_loc f G L U1 R1 e1 b /\
      has_type_with_loc f G L U2 R2 e2 c
  | LetPair e1 body => exists U1 U2 R1 R2 b c,
      SplitM U U1 U2 /\ Split R R1 R2 /\
      has_type_with_loc f G L U1 R1 e1 (TTensor b c) /\
      has_type_with_loc f G (c :: b :: L) (true :: true :: U2) R2 body a
  | With e1 e2 => exists b c, a = TWith b c /\
      has_type_with_loc f G L U R e1 b /\
      has_type_with_loc f G L U R e2 c
  | Fst e1 => exists b, has_type_with_loc f G L U R e1 (TWith a b)
  | Snd e1 => exists b, has_type_with_loc f G L U R e1 (TWith b a)
  | Bang body => exists b, a = TBang b /\
      U = mask_zero (length L) /\ R = [] /\
      has_type_with_loc f G L (mask_zero (length L)) [] body b
  | LetBang e1 body => exists U1 U2 R1 R2 b,
      SplitM U U1 U2 /\ Split R R1 R2 /\
      has_type_with_loc f G L U1 R1 e1 (TBang b) /\
      has_type_with_loc f (b :: G) L U2 R2 body a
  | Nat _ => a = TNat /\ U = mask_zero (length L) /\ R = []
  | Succ e1 => a = TNat /\ has_type_with_loc f G L U R e1 TNat
  | Iter count step_term seed => exists Uc Ur Us Uz Rc Rr Rs Rz,
      SplitM U Uc Ur /\ SplitM Ur Us Uz /\
      Split R Rc Rr /\ Split Rr Rs Rz /\
      has_type_with_loc f G L Uc Rc count TNat /\
      has_type_with_loc f G L Us Rs step_term (TBang (TLolli a a)) /\
      has_type_with_loc f G L Uz Rz seed a
  | Bool _ => a = TBool /\ U = mask_zero (length L) /\ R = []
  | If c e1 e2 => exists Uc Ub Rc Rb,
      SplitM U Uc Ub /\ Split R Rc Rb /\
      has_type_with_loc f G L Uc Rc c TBool /\
      has_type_with_loc f G L Ub Rb e1 a /\
      has_type_with_loc f G L Ub Rb e2 a
  | New e1 => exists b, a = TRef b /\ has_type_with_loc f G L U R e1 b
  | Swap e1 e2 => exists U1 U2 R1 R2 b c,
      a = TTensor b (TRef c) /\ SplitM U U1 U2 /\ Split R R1 R2 /\
      has_type_with_loc f G L U1 R1 e1 (TRef b) /\
      has_type_with_loc f G L U2 R2 e2 c
  | Free e1 => a = TUnit /\
      has_type_with_loc f G L U R e1 (TRef TUnit)
  end.

Lemma has_type_with_loc_generation : forall f G L U R e a,
  has_type_with_loc f G L U R e a ->
  exists V Q,
    (f = Linear -> V = U /\ Q = R) /\
    mask_le V U /\ split_incl Q R /\
    has_type_with_loc_head f G L V Q e a.
Proof.
  intros f G L U R e a H. induction H.
  all: try solve [eexists; eexists; split; [intros; split; reflexivity | ];
    repeat split; try apply mask_le_refl; try apply split_incl_refl;
    simpl; repeat eexists; eauto].
  destruct IHhas_type_with_loc as [V0 [Q0 [_ [HV [HQ Hhead]]]]].
  exists V0, Q0. split; [discriminate | ]. repeat split; eauto using
    mask_le_trans, split_incl_trans.
Qed.

(** In an empty resource scope the smaller mask exposed by generation is
    necessarily empty, so clients only need to track the location fragment. *)
Lemma has_type_with_loc_generation_closed : forall f G R e a,
  has_type_with_loc f G [] [] R e a ->
  exists Q,
    (f = Linear -> Q = R) /\ split_incl Q R /\
    has_type_with_loc_head f G [] [] Q e a.
Proof.
  intros f G R e a Htype.
  destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
    as [V [Q [Hlinear [HV [HQ Hhead]]]]].
  assert (V = []) as ->.
  { apply mask_le_length in HV. destruct V; [reflexivity | discriminate]. }
  exists Q. repeat split; try assumption.
  intros Hf. specialize (Hlinear Hf). tauto.
Qed.

(** ** Canonical forms *)

Inductive canonical_value : ty -> term -> Prop :=
  | CanonicalLoc : forall l a, canonical_value (TRef a) (Loc l)
  | CanonicalLam : forall a body b,
      canonical_value (TLolli a b) (Lam a body)
  | CanonicalUnit : canonical_value TUnit Unit
  | CanonicalPair : forall v1 v2 a b,
      value v1 -> value v2 ->
      canonical_value (TTensor a b) (Pair v1 v2)
  | CanonicalWith : forall e1 e2 a b,
      canonical_value (TWith a b) (With e1 e2)
  | CanonicalBang : forall body a,
      canonical_value (TBang a) (Bang body)
  | CanonicalNat : forall n, canonical_value TNat (Nat n)
  | CanonicalBool : forall b, canonical_value TBool (Bool b).

Lemma typed_value_canonical : forall f R v a,
  value v -> has_type_with_loc f [] [] [] R v a -> canonical_value a v.
Proof.
  intros f R v a Hvalue Htype.
  destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
    as [V [Q [_ [_ [_ Hhead]]]]].
  destruct Hvalue; cbn [has_type_with_loc_head] in Hhead.
  - destruct Hhead as [b [Heq _]]. inversion Heq. constructor.
  - destruct Hhead as [b [Heq _]]. inversion Heq. constructor.
  - destruct Hhead as [Heq _]. subst. constructor.
  - destruct Hhead as [U1 [U2 [R1 [R2 [b [c
      [Heq [_ [_ [_ _]]]]]]]]]].
    subst. constructor; assumption.
  - destruct Hhead as [b [c [Heq [_ _]]]]. subst. constructor.
  - destruct Hhead as [b [Heq _]]. subst. constructor.
  - destruct Hhead as [Heq _]. subst. constructor.
  - destruct Hhead as [Heq _]. subst. constructor.
Qed.

(** Convenient type-specific projections of [typed_value_canonical]. *)
Lemma canonical_ref : forall f R v a,
  value v -> has_type_with_loc f [] [] [] R v (TRef a) ->
  exists l, v = Loc l.
Proof.
  intros. pose proof (typed_value_canonical _ _ _ _ H H0) as Hcanonical.
  inversion Hcanonical; subst. eauto.
Qed.

Lemma canonical_lolli : forall f R v a b,
  value v -> has_type_with_loc f [] [] [] R v (TLolli a b) ->
  exists body, v = Lam a body.
Proof.
  intros. pose proof (typed_value_canonical _ _ _ _ H H0) as Hcanonical.
  inversion Hcanonical; subst. eauto.
Qed.

Lemma canonical_unit : forall f R v,
  value v -> has_type_with_loc f [] [] [] R v TUnit -> v = Unit.
Proof.
  intros. pose proof (typed_value_canonical _ _ _ _ H H0) as Hcanonical.
  inversion Hcanonical. reflexivity.
Qed.

Lemma canonical_tensor : forall f R v a b,
  value v -> has_type_with_loc f [] [] [] R v (TTensor a b) ->
  exists v1 v2, v = Pair v1 v2 /\ value v1 /\ value v2.
Proof.
  intros. pose proof (typed_value_canonical _ _ _ _ H H0) as Hcanonical.
  inversion Hcanonical; subst. eauto.
Qed.

Lemma canonical_with : forall f R v a b,
  value v -> has_type_with_loc f [] [] [] R v (TWith a b) ->
  exists e1 e2, v = With e1 e2.
Proof.
  intros. pose proof (typed_value_canonical _ _ _ _ H H0) as Hcanonical.
  inversion Hcanonical; subst. eauto.
Qed.

Lemma canonical_bang : forall f R v a,
  value v -> has_type_with_loc f [] [] [] R v (TBang a) ->
  exists body, v = Bang body.
Proof.
  intros. pose proof (typed_value_canonical _ _ _ _ H H0) as Hcanonical.
  inversion Hcanonical; subst. eauto.
Qed.

Lemma canonical_nat : forall f R v,
  value v -> has_type_with_loc f [] [] [] R v TNat ->
  exists n, v = Nat n.
Proof.
  intros. pose proof (typed_value_canonical _ _ _ _ H H0) as Hcanonical.
  inversion Hcanonical; subst. eauto.
Qed.

Lemma canonical_bool : forall f R v,
  value v -> has_type_with_loc f [] [] [] R v TBool ->
  exists b, v = Bool b.
Proof.
  intros. pose proof (typed_value_canonical _ _ _ _ H H0) as Hcanonical.
  inversion Hcanonical; subst. eauto.
Qed.

(** ** Locations and typed cells *)

Lemma typed_location_member : forall f G L U R l a,
  has_type_with_loc f G L U R (Loc l) (TRef a) -> In (l, a) R.
Proof.
  intros f G L U R l a Htype.
  destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
    as [V [Q [_ [_ [HQ Hhead]]]]].
  cbn [has_type_with_loc_head] in Hhead.
  destruct Hhead as [b [Heq [_ ->]]]. inversion Heq; subst b.
  destruct HQ as [F Hsplit].
  apply (proj2 (split_in _ _ _ Hsplit (l, a))). simpl. auto.
Qed.

Lemma cells_typed_member : forall f S s C l a,
  cells_typed f S s C -> In (l, a) S ->
  exists v Rc,
    In (l, v) s /\ value v /\ has_type_with_loc f [] [] [] Rc v a.
Proof.
  intros f S s C l a Hcells. induction Hcells; intros Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + injection Heq as -> ->. exists v, Rc. split; [simpl; auto | ].
      split; assumption.
    + destruct (IHHcells Hin) as [w [Rw [Hmember [Hvalue Htype]]]].
      exists w, Rw. split; [simpl; auto | ]. split; assumption.
Qed.

Lemma cells_typed_lookup : forall f S s C l a,
  NoDup (natmap_domain S) -> cells_typed f S s C -> In (l, a) S ->
  exists v Rc,
    In_opt v (natmap_lookup l s) /\
    value v /\ has_type_with_loc f [] [] [] Rc v a.
Proof.
  intros f S s C l a Hnd Hcells Hin.
  destruct (cells_typed_member _ _ _ _ _ _ Hcells Hin)
    as [v [Rc [Hmember [Hvalue Htype]]]].
  assert (Hnd_store : NoDup (natmap_domain s)).
  { rewrite <- (cells_typed_domain _ _ _ _ Hcells). exact Hnd. }
  assert (Hdomain : In l (natmap_domain s)).
  { apply (in_map fst) in Hmember. exact Hmember. }
  apply natmap_lookup_complete in Hdomain.
  apply Is_some_exists in Hdomain. destruct Hdomain as [w Hlookup].
  pose proof (natmap_lookup_member_unique _ _ _ _
      Hnd_store Hmember Hlookup) as ->.
  exists w, Rc. repeat split; assumption.
Qed.

Lemma cells_typed_nth : forall f K s C i l a,
  cells_typed f K s C -> In_opt (l, a) (nth_error K i) ->
  exists v, In_opt (l, v) (nth_error s i).
Proof.
  intros f K s C i l a Hcells. revert i l a.
  induction Hcells; intros [| i] k b Hnth; simpl in Hnth; try contradiction.
  - injection Hnth as -> ->. exists v. reflexivity.
  - eapply IHHcells; eassumption.
Qed.

Lemma cells_typed_replace : forall f K s C i l a old v b V,
  NoDup (natmap_domain K) -> cells_typed f K s C ->
  In_opt (l, a) (nth_error K i) ->
  In_opt (l, old) (nth_error s i) ->
  value v -> has_type_with_loc f [] [] [] V v b ->
  exists W Other,
    value old /\ has_type_with_loc f [] [] [] W old a /\
    Split C W Other /\
    forall C', Split C' V Other ->
      cells_typed f (store_sig_update l b K) (store_update l v s) C'.
Proof.
  intros f K s C i l a old v b V Hnd Hcells.
  revert i l a old Hnd. induction Hcells;
    intros [| i] k b0 old Hnd Hsig Hstore Hv Hvt;
    simpl in Hsig, Hstore; try contradiction;
    inversion Hnd as [| ? ? Habs Hndtail]; subst.
  - inversion Hsig; subst. inversion Hstore; subst.
    exists Rc, Rt. split; [exact H | ]. split; [exact H0 | ].
    split; [exact H1 | ]. intros C' HC'.
    assert (Hstore_absent : ~ In l (natmap_domain s)).
    { rewrite <- (cells_typed_domain _ _ _ _ Hcells). exact Habs. }
    unfold store_sig_update, store_update.
    unfold natmap_replace. cbn [map fst snd].
    rewrite Nat.eqb_refl.
    change (cells_typed f
      ((l, b) :: natmap_replace l b K)
      ((l, v) :: natmap_replace l v s) C').
    rewrite (natmap_replace_absent l b K Habs),
      (natmap_replace_absent l v s Hstore_absent).
    econstructor; eassumption.
  - assert (Hne : l <> k).
    { intros ->. apply Habs. apply In_opt_eq_Some, nth_error_In,
        (in_map fst) in Hsig. exact Hsig. }
    destruct (IHHcells _ _ _ _ Hndtail Hsig Hstore Hv Hvt)
      as [W [OtherTail [Hold [Htyped [HC Hrebuild]]]]].
    destruct (split_assoc _ _ _ _ _ (split_comm _ _ _ H1) HC)
      as [Other [HCwhole HOther]].
    exists W, Other. split; [exact Hold | ]. split; [exact Htyped | ].
    split; [exact HCwhole | ]. intros C' HC'.
      destruct (split_interchange _ _ _ _ _ _ _ HC'
          (split_left V) HOther)
        as [Tail' [Head [Htop [Htail Hhead]]]].
      apply split_right_inv in Hhead. subst Head.
      assert (E : Nat.eqb k l = false) by (apply Nat.eqb_neq; congruence).
      assert (Hsig_update :
        store_sig_update k b ((l, a) :: K) =
          (l, a) :: store_sig_update k b K).
      { unfold store_sig_update, natmap_replace.
        cbn [map fst snd]. rewrite E. reflexivity. }
      assert (Hstore_update :
        store_update k v ((l, v0) :: s) =
          (l, v0) :: store_update k v s).
      { unfold store_update, natmap_replace.
        cbn [map fst snd]. rewrite E. reflexivity. }
      rewrite Hsig_update, Hstore_update.
      econstructor.
      * exact H.
      * exact H0.
      * apply split_comm. exact Htop.
      * apply Hrebuild. exact Htail.
Qed.

Lemma cells_typed_remove : forall f K s C i l,
  NoDup (natmap_domain K) -> cells_typed f K s C ->
  In_opt (l, TUnit) (nth_error K i) ->
  In_opt (l, Unit) (nth_error s i) ->
  exists W Other,
    has_type_with_loc f [] [] [] W Unit TUnit /\ Split C W Other /\
    cells_typed f (store_sig_remove l K) (store_remove l s) Other.
Proof.
  intros f K s C i l Hnd Hcells. revert i l Hnd.
  induction Hcells; intros [| i] k Hnd Hsig Hstore;
    simpl in Hsig, Hstore; try contradiction;
    inversion Hnd as [| ? ? Habs Hndtail]; subst.
  - inversion Hsig; subst. inversion Hstore; subst.
    exists Rc, Rt. split; [exact H0 | ]. split; [exact H1 | ].
    assert (Hstore_absent : ~ In l (natmap_domain s)).
    { rewrite <- (cells_typed_domain _ _ _ _ Hcells). exact Habs. }
    unfold store_sig_remove, store_remove.
    change (cells_typed f
      (natmap_remove l (natmap_insert l TUnit K))
      (natmap_remove l (natmap_insert l Unit s)) Rt).
    rewrite (@natmap_remove_insert ty l TUnit K Habs),
      (@natmap_remove_insert term l Unit s Hstore_absent).
    exact Hcells.
  - assert (Hne : l <> k).
    { intros ->. apply Habs. apply In_opt_eq_Some, nth_error_In,
        (in_map fst) in Hsig. exact Hsig. }
    destruct (IHHcells _ _ Hndtail Hsig Hstore)
      as [W [OtherTail [Hunit [HC Htail]]]].
    destruct (split_assoc _ _ _ _ _ (split_comm _ _ _ H1) HC)
      as [Other [HCwhole HOther]].
    exists W, Other. split; [exact Hunit | ]. split; [exact HCwhole | ].
    assert (E : Nat.eqb k l = false) by (apply Nat.eqb_neq; congruence).
    assert (Hsig_remove :
      store_sig_remove k ((l, a) :: K) =
        (l, a) :: store_sig_remove k K).
    { unfold store_sig_remove. cbn [natmap_remove fst snd].
      rewrite E. reflexivity. }
    assert (Hstore_remove :
      store_remove k ((l, v) :: s) =
        (l, v) :: store_remove k s).
    { unfold store_remove. cbn [natmap_remove fst snd].
      rewrite E. reflexivity. }
    rewrite Hsig_remove, Hstore_remove.
    econstructor; eauto. apply split_comm. exact HOther.
Qed.
