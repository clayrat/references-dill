(** * Declarative source typing with a fixed resource scope

    [has_type f G L U e A] assigns [A] to [e]. [G] is shared, [L] retains
    every resource position, and [U] selects the hypotheses of this judgment.
    Multiplicative premises partition [U]; additive premises share it.

    The rules describe exact use in linear mode. [TyWeak] adds general affine
    weakening at any node of a derivation, including under local binders.
    Promotion always checks its body with a zero mask. There is no [Loc] rule:
    [StoreTyping.v] extends the source judgment with address resources. *)

From Stdlib Require Import List Bool Arith Lia.
From DILLref Require Import Prelude Ty Syntax Index Scoping Mask.
Import ListNotations.

Inductive has_type : flag -> list ty -> list ty -> mask -> term -> ty -> Prop :=
  | TyLVar : forall f G L i a,
      In_opt a (nth_error L i) ->
      has_type f G L (mask_single (length L) i) (LVar i) a
  | TyUVar : forall f G L i a,
      In_opt a (nth_error G i) ->
      has_type f G L (mask_zero (length L)) (UVar i) a
  | TyLam : forall f G L U a b e,
      has_type f G (a :: L) (true :: U) e b ->
      has_type f G L U (Lam a e) (TLolli a b)
  | TyApp : forall f G L U U1 U2 e1 e2 a b,
      SplitM U U1 U2 ->
      has_type f G L U1 e1 (TLolli a b) -> has_type f G L U2 e2 a ->
      has_type f G L U (App e1 e2) b
  | TyUnit : forall f G L, has_type f G L (mask_zero (length L)) Unit TUnit
  | TyLetUnit : forall f G L U U1 U2 e1 e2 a,
      SplitM U U1 U2 ->
      has_type f G L U1 e1 TUnit -> has_type f G L U2 e2 a ->
      has_type f G L U (LetUnit e1 e2) a
  | TyPair : forall f G L U U1 U2 e1 e2 a b,
      SplitM U U1 U2 ->
      has_type f G L U1 e1 a -> has_type f G L U2 e2 b ->
      has_type f G L U (Pair e1 e2) (TTensor a b)
  | TyLetPair : forall f G L U U1 U2 e1 e2 a b c,
      SplitM U U1 U2 ->
      has_type f G L U1 e1 (TTensor a b) ->
      has_type f G (b :: a :: L) (true :: true :: U2) e2 c ->
      has_type f G L U (LetPair e1 e2) c
  | TyWith : forall f G L U e1 e2 a b,
      has_type f G L U e1 a -> has_type f G L U e2 b ->
      has_type f G L U (With e1 e2) (TWith a b)
  | TyFst : forall f G L U e a b,
      has_type f G L U e (TWith a b) -> has_type f G L U (Fst e) a
  | TySnd : forall f G L U e a b,
      has_type f G L U e (TWith a b) -> has_type f G L U (Snd e) b
  | TyBang : forall f G L e a,
      has_type f G L (mask_zero (length L)) e a ->
      has_type f G L (mask_zero (length L)) (Bang e) (TBang a)
  | TyLetBang : forall f G L U U1 U2 e1 e2 a b,
      SplitM U U1 U2 ->
      has_type f G L U1 e1 (TBang a) -> has_type f (a :: G) L U2 e2 b ->
      has_type f G L U (LetBang e1 e2) b
  | TyNat : forall f G L n, has_type f G L (mask_zero (length L)) (Nat n) TNat
  | TySucc : forall f G L U e,
      has_type f G L U e TNat -> has_type f G L U (Succ e) TNat
  | TyIter : forall f G L U Uc R Us Uz count step seed a,
      SplitM U Uc R -> SplitM R Us Uz ->
      has_type f G L Uc count TNat ->
      has_type f G L Us step (TBang (TLolli a a)) ->
      has_type f G L Uz seed a ->
      has_type f G L U (Iter count step seed) a
  | TyBool : forall f G L b, has_type f G L (mask_zero (length L)) (Bool b) TBool
  | TyIf : forall f G L U Uc Ub c e1 e2 a,
      SplitM U Uc Ub -> has_type f G L Uc c TBool ->
      has_type f G L Ub e1 a -> has_type f G L Ub e2 a ->
      has_type f G L U (If c e1 e2) a
  | TyNew : forall f G L U e a,
      has_type f G L U e a -> has_type f G L U (New e) (TRef a)
  | TySwap : forall f G L U U1 U2 e1 e2 a b,
      SplitM U U1 U2 ->
      has_type f G L U1 e1 (TRef a) -> has_type f G L U2 e2 b ->
      has_type f G L U (Swap e1 e2) (TTensor a (TRef b))
  | TyFree : forall f G L U e,
      has_type f G L U e (TRef TUnit) -> has_type f G L U (Free e) TUnit
  | TyWeak : forall G L U V e a,
      has_type Affine G L U e a -> mask_le U V ->
      has_type Affine G L V e a.

(** Every derivation supplies its mask's well-formedness; callers need not
    carry an unrelated assumption to rule out truncated masks. *)
Lemma typing_wf_mask : forall f G L U e a,
  has_type f G L U e a -> wf_mask L U.
Proof.
  intros f G L U e a H. induction H;
    unfold wf_mask in *; simpl in *;
    try apply mask_zero_length; try apply mask_single_length; try lia.
  all: repeat match goal with
    | Hs : SplitM _ _ _ |- _ =>
        let Hl := fresh "Hl" in
        pose proof (splitM_length _ _ _ Hs) as Hl; clear Hs; destruct Hl
    | Hle : mask_le _ _ |- _ =>
        let Hl := fresh "Hl" in
        pose proof (mask_le_length _ _ Hle) as Hl; clear Hle
    end; lia.
Qed.

#[local] Hint Constructors scoped : scope_typing.

Lemma typing_scoped : forall f G L U e a,
  has_type f G L U e a -> scoped (length G) (length L) e.
Proof.
  intros f G L U e a H. induction H; simpl in *;
    eauto using lookup_bound with scope_typing.
Qed.

Lemma typing_loc_free : forall f G L U e a,
  has_type f G L U e a -> loc_free e = true.
Proof.
  intros f G L U e a H. induction H; simpl;
    rewrite ?IHhas_type, ?IHhas_type1, ?IHhas_type2, ?IHhas_type3; reflexivity.
Qed.

Lemma typing_no_loc : forall f G L U l a, ~ has_type f G L U (Loc l) a.
Proof. intros f G L U l a H. apply typing_loc_free in H. discriminate. Qed.

(** Any linear derivation is also valid in affine mode. This does not add
    contraction or relax the empty-resource premise of promotion. *)
Lemma typing_to_affine : forall f G L U e a,
  has_type f G L U e a -> has_type Affine G L U e a.
Proof. intros f G L U e a H. induction H; econstructor; eassumption. Qed.

(** These inversions pass through affine weakening. In particular, adding
    unused hypotheses cannot make a consumed variable disappear under [!]. *)
Lemma typing_lvar_available : forall f G L U i a,
  has_type f G L U (LVar i) a -> In_opt true (nth_error U i).
Proof.
  intros f G L U i a H. remember (LVar i) as e eqn:E in H.
  induction H; inversion E; subst;
    eauto using mask_single_nth, lookup_bound, mask_le_nth.
Qed.

Lemma typing_bang_body : forall f G L U e a,
  has_type f G L U (Bang e) (TBang a) ->
  has_type f G L (mask_zero (length L)) e a.
Proof.
  intros f G L U e a H.
  remember (Bang e) as t eqn:Et in H.
  remember (TBang a) as b eqn:Eb in H.
  induction H; inversion Et; subst; try inversion Eb; subst; eauto.
Qed.

Lemma typing_bang_lvar_absurd : forall f G L U i a,
  ~ has_type f G L U (Bang (LVar i)) (TBang a).
Proof.
  intros f G L U i a H. apply typing_bang_body, typing_lvar_available in H.
  exact (mask_zero_no_true (length L) i H).
Qed.

(** ** Generation and uniqueness

    [typing_head] exposes the last syntax-directed rule. [typing_generation]
    first removes any outer affine weakening, retaining the smaller mask and
    its inclusion in the original one. It is a proposition, not a checker. *)
Definition typing_head (f : flag) (G L : list ty) (U : mask) (e : term) (a : ty) : Prop :=
  match e with
  | LVar i => In_opt a (nth_error L i) /\ U = mask_single (length L) i
  | UVar i => In_opt a (nth_error G i) /\ U = mask_zero (length L)
  | Loc _ => False
  | Lam b e => exists c, a = TLolli b c /\ has_type f G (b :: L) (true :: U) e c
  | App e1 e2 => exists U1 U2 b, SplitM U U1 U2 /\
      has_type f G L U1 e1 (TLolli b a) /\ has_type f G L U2 e2 b
  | Unit => a = TUnit /\ U = mask_zero (length L)
  | LetUnit e1 e2 => exists U1 U2, SplitM U U1 U2 /\
      has_type f G L U1 e1 TUnit /\ has_type f G L U2 e2 a
  | Pair e1 e2 => exists U1 U2 b c, a = TTensor b c /\ SplitM U U1 U2 /\
      has_type f G L U1 e1 b /\ has_type f G L U2 e2 c
  | LetPair e1 e2 => exists U1 U2 b c, SplitM U U1 U2 /\
      has_type f G L U1 e1 (TTensor b c) /\
      has_type f G (c :: b :: L) (true :: true :: U2) e2 a
  | With e1 e2 => exists b c, a = TWith b c /\
      has_type f G L U e1 b /\ has_type f G L U e2 c
  | Fst e => exists b, has_type f G L U e (TWith a b)
  | Snd e => exists b, has_type f G L U e (TWith b a)
  | Bang e => exists b, a = TBang b /\ U = mask_zero (length L) /\
      has_type f G L (mask_zero (length L)) e b
  | LetBang e1 e2 => exists U1 U2 b, SplitM U U1 U2 /\
      has_type f G L U1 e1 (TBang b) /\ has_type f (b :: G) L U2 e2 a
  | Nat _ => a = TNat /\ U = mask_zero (length L)
  | Succ e => a = TNat /\ has_type f G L U e TNat
  | Iter count step seed => exists Uc R Us Uz,
      SplitM U Uc R /\ SplitM R Us Uz /\
      has_type f G L Uc count TNat /\
      has_type f G L Us step (TBang (TLolli a a)) /\ has_type f G L Uz seed a
  | Bool _ => a = TBool /\ U = mask_zero (length L)
  | If c e1 e2 => exists Uc Ub, SplitM U Uc Ub /\
      has_type f G L Uc c TBool /\ has_type f G L Ub e1 a /\ has_type f G L Ub e2 a
  | New e => exists b, a = TRef b /\ has_type f G L U e b
  | Swap e1 e2 => exists U1 U2 b c, a = TTensor b (TRef c) /\ SplitM U U1 U2 /\
      has_type f G L U1 e1 (TRef b) /\ has_type f G L U2 e2 c
  | Free e => a = TUnit /\ has_type f G L U e (TRef TUnit)
  end.

Lemma typing_generation : forall f G L U e a, has_type f G L U e a ->
  exists V, (f = Linear -> V = U) /\ mask_le V U /\ typing_head f G L V e a.
Proof.
  intros f G L U e a H. induction H.
  all: try solve [eexists; split; [reflexivity | split; [apply mask_le_refl | ]];
    simpl; repeat eexists; eauto].
  destruct IHhas_type as [W [_ [Hle Hhead]]].
  exists W. split; [discriminate | split; [eapply mask_le_trans; eassumption | exact Hhead]].
Qed.

(** Masks and mode may differ: they constrain use, not the result type. *)
Lemma typing_unique : forall e G L f U a f' V b,
  has_type f G L U e a -> has_type f' G L V e b -> a = b.
Proof.
  induction e; intros G L f U res1 f' V res2 Ha Hb;
    apply typing_generation in Ha; apply typing_generation in Hb;
    destruct Ha as [Ua [_ [_ Ha]]]; destruct Hb as [Ub [_ [_ Hb]]];
    cbn [typing_head] in Ha, Hb;
    repeat match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H : In_opt _ _ |- _ => apply In_opt_eq_Some in H
    end; try contradiction; subst; try congruence.
  all: repeat match goal with
    | IH : forall G L f U a f' V b, has_type f G L U ?e a ->
        has_type f' G L V ?e b -> a = b,
      H1 : has_type ?f ?G ?L ?U ?e ?a,
      H2 : has_type ?f' ?G ?L ?V ?e ?b |- _ =>
        tryif constr_eq a b then fail else idtac;
        let E := fresh "Etype" in
        pose proof (IH G L f U a f' V b H1 H2) as E;
        clear H1; inversion E; subst; try clear E
    end; eauto; congruence.
Qed.
