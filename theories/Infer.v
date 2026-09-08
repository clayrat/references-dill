(** * Type inference with leftover resource masks

    [infer f G L I e] infers the type of a source term and returns the
    positions of [L] that remain available. The full resource scope never
    changes while a term is checked: multiplicative premises receive the
    previous premise's leftovers, whereas additive alternatives start with
    the same mask.

    Local resource binders are removed from the returned mask. Linear mode
    requires each such binder to have been consumed; affine mode permits an
    unused local binder. Promotion succeeds only when checking its body leaves
    the entire input mask unchanged. Runtime locations have no source type.

    Types are synthesized from the term alone; no expected type is supplied
    and no checking mode is needed. Every binder carries its type ([Lam a e]),
    the eliminators of [⊗], [&], [!] and [ref] read the component types off
    the eliminated term, and there is no polymorphism or subtyping, so a term
    has at most one type ([typing_unique]) and a single structural pass
    computes it. The only type comparisons are equality tests between two
    synthesized types: at application, [let () =], [Succ], the iterator, the
    branches of [if] and [free]. A bidirectional algorithm with a separate
    checking mode becomes necessary only when binder annotations are dropped
    or the language gains polymorphism or subtyping; see Pierce, Types and
    Programming Languages, MIT Press 2002, §9.3 (uniqueness of types) and
    §10.2 (the synthesizing typechecker of the simply typed calculus), and
    Dunfield and Krishnaswami, Bidirectional Typing, ACM Computing Surveys
    54(5), 2021, §1, https://doi.org/10.1145/3450952, on the trade-off between
    annotations and a checking mode. What the resource discipline adds to the
    traversal is its second output, the leftover mask. *)

From Stdlib Require Import List Bool Arith Lia.
From DILLref Require Import Prelude Ty Syntax Mask Typing.
Import ListNotations.

(** Combine the resources guaranteed to remain after either additive
    alternative. Linear alternatives must consume exactly the same positions;
    affine alternatives conservatively retain only their common leftovers. *)
Definition merge_leftovers (f : flag) (O1 O2 : mask) : option mask :=
  match f with
  | Linear => if mask_eqb O1 O2 then Some O1 else None
  | Affine => Some (mask_meet O1 O2)
  end.

(** Remove one local resource position when leaving its scope. *)
Definition finish_binder (f : flag) (O : mask) : option mask :=
  match f, O with
  | Linear, false :: O' => Some O'
  | Linear, _ => None
  | Affine, _ :: O' => Some O'
  | Affine, [] => None
  end.

(** ** Result composition

    Premises are chained through [bind] and [guard] from [Prelude]. The
    projections below extract the components of a checked type and unfold
    under [cbn], so proofs see the underlying case analysis. *)

Definition as_lolli (t : ty) : option (ty * ty) :=
  match t with TLolli a b => Some (a, b) | _ => None end.
Definition as_tensor (t : ty) : option (ty * ty) :=
  match t with TTensor a b => Some (a, b) | _ => None end.
Definition as_with (t : ty) : option (ty * ty) :=
  match t with TWith a b => Some (a, b) | _ => None end.
Definition as_bang (t : ty) : option ty :=
  match t with TBang a => Some a | _ => None end.
Definition as_ref (t : ty) : option ty :=
  match t with TRef a => Some a | _ => None end.
Arguments as_lolli t /.
Arguments as_tensor t /.
Arguments as_with t /.
Arguments as_bang t /.
Arguments as_ref t /.

(** The step function of the iterator must be a boxed endofunction. *)
Definition as_step (t : ty) : option ty :=
  bind (as_bang t) (fun t' =>
  bind (as_lolli t') (fun '(a, b) => guard (ty_eqb a b) (Some a))).
Arguments as_step t /.

(** ** The inference function

    The recursive worker assumes that [I] has the same length as [L]. Every
    recursive call preserves that invariant by construction. *)
Fixpoint infer_raw
    (f : flag) (G L : list ty) (I : mask) (e : term)
    {struct e} : option (ty * mask) :=
  match e with
  | LVar i =>
      bind (nth_error L i) (fun a =>
      bind (mask_consume i I) (fun out => Some (a, out)))
  | UVar i => bind (nth_error G i) (fun a => Some (a, I))
  | Loc _ => None
  | Lam a body =>
      bind (infer_raw f G (a :: L) (true :: I) body) (fun '(b, out) =>
      bind (finish_binder f out) (fun out' => Some (TLolli a b, out')))
  | App e1 e2 =>
      bind (infer_raw f G L I e1) (fun '(t, O1) =>
      bind (as_lolli t) (fun '(a, b) =>
      bind (infer_raw f G L O1 e2) (fun '(a', O2) =>
      guard (ty_eqb a a') (Some (b, O2)))))
  | Unit => Some (TUnit, I)
  | LetUnit e1 e2 =>
      bind (infer_raw f G L I e1) (fun '(a, O1) =>
      guard (ty_eqb a TUnit) (infer_raw f G L O1 e2))
  | Pair e1 e2 =>
      bind (infer_raw f G L I e1) (fun '(a, O1) =>
      bind (infer_raw f G L O1 e2) (fun '(b, O2) => Some (TTensor a b, O2)))
  | LetPair e1 body =>
      bind (infer_raw f G L I e1) (fun '(t, O1) =>
      bind (as_tensor t) (fun '(a, b) =>
      bind (infer_raw f G (b :: a :: L) (true :: true :: O1) body) (fun '(c, O2) =>
      bind (finish_binder f O2) (fun O3 =>
      bind (finish_binder f O3) (fun O4 => Some (c, O4))))))
  | With e1 e2 =>
      bind (infer_raw f G L I e1) (fun '(a, O1) =>
      bind (infer_raw f G L I e2) (fun '(b, O2) =>
      bind (merge_leftovers f O1 O2) (fun out => Some (TWith a b, out))))
  | Fst e1 =>
      bind (infer_raw f G L I e1) (fun '(t, out) =>
      bind (as_with t) (fun '(a, _) => Some (a, out)))
  | Snd e1 =>
      bind (infer_raw f G L I e1) (fun '(t, out) =>
      bind (as_with t) (fun '(_, b) => Some (b, out)))
  | Bang body =>
      bind (infer_raw f G L I body) (fun '(a, out) =>
      guard (mask_eqb out I) (Some (TBang a, I)))
  | LetBang e1 body =>
      bind (infer_raw f G L I e1) (fun '(t, O1) =>
      bind (as_bang t) (fun a => infer_raw f (a :: G) L O1 body))
  | Nat _ => Some (TNat, I)
  | Succ e1 =>
      bind (infer_raw f G L I e1) (fun '(a, out) =>
      guard (ty_eqb a TNat) (Some (TNat, out)))
  | Iter count step seed =>
      bind (infer_raw f G L I count) (fun '(a_count, O_count) =>
      guard (ty_eqb a_count TNat) (
      bind (infer_raw f G L O_count step) (fun '(t, O_step) =>
      bind (as_step t) (fun a =>
      bind (infer_raw f G L O_step seed) (fun '(a_seed, O_seed) =>
      guard (ty_eqb a a_seed) (Some (a, O_seed)))))))
  | Bool _ => Some (TBool, I)
  | If condition e1 e2 =>
      bind (infer_raw f G L I condition) (fun '(a_condition, O_condition) =>
      guard (ty_eqb a_condition TBool) (
      bind (infer_raw f G L O_condition e1) (fun '(a, O1) =>
      bind (infer_raw f G L O_condition e2) (fun '(b, O2) =>
      guard (ty_eqb a b) (
      bind (merge_leftovers f O1 O2) (fun out => Some (a, out)))))))
  | New e1 =>
      bind (infer_raw f G L I e1) (fun '(a, out) => Some (TRef a, out))
  | Swap e1 e2 =>
      bind (infer_raw f G L I e1) (fun '(t, O1) =>
      bind (as_ref t) (fun a =>
      bind (infer_raw f G L O1 e2) (fun '(b, O2) =>
      Some (TTensor a (TRef b), O2))))
  | Free e1 =>
      bind (infer_raw f G L I e1) (fun '(a, out) =>
      guard (ty_eqb a (TRef TUnit)) (Some (TUnit, out)))
  end.

(** Malformed availability masks are rejected before recursion. Out-of-scope
    variables and runtime locations are rejected by [infer_raw]. *)
Definition infer
    (f : flag) (G L : list ty) (I : mask) (e : term)
    : option (ty * mask) :=
  if Nat.eqb (length I) (length L)
  then infer_raw f G L I e
  else None.

(** ** Structural properties of the executable helpers

    Case analysis on a successful infer exposes the results of every
    premise and substitutes the equalities the checker tested. *)

Lemma merge_leftovers_le : forall f I O1 O2 O,
  mask_le O1 I -> mask_le O2 I ->
  In_opt O (merge_leftovers f O1 O2) -> mask_le O I.
Proof.
  intros f I O1 O2 O H1 H2 Hmerge. apply In_opt_Some in Hmerge.
  destruct f; simpl in Hmerge.
  - destruct (mask_eqb O1 O2) eqn:E; try discriminate.
    inversion Hmerge; subst. exact H1.
  - inversion Hmerge; subst.
    eapply mask_le_trans; [apply mask_meet_le_l | exact H1].
    rewrite (mask_le_length _ _ H1), (mask_le_length _ _ H2). reflexivity.
Qed.

Lemma finish_binder_le : forall f I O tail,
  In_opt tail (finish_binder f O) -> mask_le O (true :: I) -> mask_le tail I.
Proof.
  intros f I [| b O] tail Hfinish Hle. apply In_opt_Some in Hfinish.
  - destruct f; discriminate.
  - destruct f, b; simpl in Hfinish; try discriminate;
      inversion Hfinish; subst; eapply mask_le_tail, Hle.
Qed.

(** The local position either belongs to the demand already or can be added
    by affine weakening. Linear mode records the exact first alternative. *)
Lemma finish_binder_split : forall f I used O tail,
  In_opt tail (finish_binder f O) -> SplitM (true :: I) used O ->
  exists used_tail, SplitM I used_tail tail /\
    mask_le used (true :: used_tail) /\
    (f = Linear -> used = true :: used_tail).
Proof.
  intros f I used [| b O] tail Hfinish Hsplit. apply In_opt_Some in Hfinish.
  - destruct f; discriminate.
  - destruct f, b; simpl in Hfinish; try discriminate; inversion Hfinish; subst;
      inversion Hsplit; subst.
    + eexists. repeat split; try eassumption; try apply mask_le_refl.
    + eexists. repeat split; try eassumption; try constructor;
        try apply mask_le_refl; discriminate.
    + eexists. repeat split; try eassumption; try apply mask_le_refl;
        discriminate.
Qed.

#[local] Ltac break_infer H :=
  apply In_opt_Some in H; cbn in H;
  repeat first
    [ lazymatch type of H with
      | context [infer_raw ?f ?G ?L ?I ?e] =>
          let E := fresh "Einfer" in
          let a := fresh "inferred_type" in
          let O := fresh "leftovers" in
          destruct (infer_raw f G L I e) as [[a O] |] eqn:E
      end
    | lazymatch type of H with
      | context [nth_error ?xs ?i] =>
          let E := fresh "Elookup" in
          let x := fresh "found" in destruct (nth_error xs i) as [x |] eqn:E
      end
    | lazymatch type of H with
      | context [mask_consume ?i ?I] =>
          let E := fresh "Econsume" in
          let O := fresh "consumed" in destruct (mask_consume i I) as [O |] eqn:E
      end
    | lazymatch type of H with
      | context [finish_binder ?f ?I] =>
          let E := fresh "Efinish" in
          let O := fresh "finished" in destruct (finish_binder f I) as [O |] eqn:E
      end
    | lazymatch type of H with
      | context [merge_leftovers ?f ?O1 ?O2] =>
          let E := fresh "Emerge" in
          let O := fresh "merged" in
          destruct (merge_leftovers f O1 O2) as [O |] eqn:E
      end
    | lazymatch type of H with
      | context [ty_eqb ?a ?b] =>
          let E := fresh "Etype" in destruct (ty_eqb a b) eqn:E
      end
    | lazymatch type of H with
      | context [mask_eqb ?I ?O] =>
          let E := fresh "Emask" in destruct (mask_eqb I O) eqn:E
      end
    | match type of H with
      | context [match ?a with _ => _ end] =>
          let T := type of a in unify T ty; destruct a
      end; cbn in H ];
  try discriminate; inversion H; subst; clear H;
  repeat match goal with
  | E : ty_eqb _ _ = true |- _ => apply ty_eqb_eq in E; subst
  | E : mask_eqb _ _ = true |- _ => apply mask_eqb_eq in E; subst
  | E : _ = Some _ |- _ => apply Some_In_opt in E
  end.

Lemma infer_raw_le : forall e f G L I a O,
  In_opt (a, O) (infer_raw f G L I e) -> mask_le O I.
Proof.
  induction e; intros f G L I a O Hinfer; break_infer Hinfer.
  all: try apply mask_le_refl.
  all: try solve [eapply mask_consume_le; eassumption].
  all: try match goal with
  | E : In_opt (_, _) (infer_raw _ _ _ _ ?e) |- _ =>
      eapply IHe in E; eassumption
  end.
  all: try match goal with
  | E1 : In_opt (_, ?O1) (infer_raw _ _ _ _ ?e1),
    E2 : In_opt (_, _) (infer_raw _ _ _ ?O1 ?e2) |- _ =>
      eapply mask_le_trans; [eapply IHe2, E2 | eapply IHe1, E1]
  end.
  all: try match goal with
  | Ebody : In_opt (_, ?Obody) (infer_raw _ _ _ _ ?body),
    Efinish : In_opt ?Otail (finish_binder _ ?Obody) |- _ =>
      eapply finish_binder_le; [exact Efinish | eapply IHe, Ebody]
  end.
  all: try match goal with
  | Ebody : In_opt (_, ?O2) (infer_raw _ _ _ _ ?body),
    Efinish1 : In_opt ?O3 (finish_binder _ ?O2),
    Efinish2 : In_opt ?O4 (finish_binder _ ?O3),
    Efirst : In_opt (_, ?O1) (infer_raw _ _ _ _ ?first) |- _ =>
      eapply mask_le_trans;
      [eapply finish_binder_le; [exact Efinish2 |
        eapply finish_binder_le; [exact Efinish1 | eapply IHe2, Ebody]] |
       eapply IHe1, Efirst]
  end.
  all: try match goal with
  | E1 : In_opt (_, ?O1) (infer_raw _ _ _ ?I ?e1),
    E2 : In_opt (_, ?O2) (infer_raw _ _ _ ?I ?e2),
    Em : In_opt ?O (merge_leftovers _ ?O1 ?O2) |- _ =>
      eapply merge_leftovers_le; [eapply IHe1, E1 | eapply IHe2, E2 | exact Em]
  end.
  all: try match goal with
  | E1 : In_opt (_, ?O1) (infer_raw _ _ _ ?I ?e1),
    E2 : In_opt (_, ?O2) (infer_raw _ _ _ ?O1 ?e2),
    E3 : In_opt (_, ?O3) (infer_raw _ _ _ ?O2 ?e3) |- _ =>
      eapply mask_le_trans; [eapply IHe3, E3 | ];
      eapply mask_le_trans; [eapply IHe2, E2 | eapply IHe1, E1]
  end.
  eapply mask_le_trans.
  - eapply merge_leftovers_le.
    + eapply IHe2, Einfer0.
    + eapply IHe3, Einfer1.
    + exact Emerge.
  - eapply IHe1, Einfer.
Qed.

Lemma infer_raw_length : forall e f G L I a O,
  In_opt (a, O) (infer_raw f G L I e) -> length O = length I.
Proof.
  intros. eapply mask_le_length, infer_raw_le, H.
Qed.

Lemma infer_raw_split : forall e f G L I a O,
  In_opt (a, O) (infer_raw f G L I e) ->
  exists U, SplitM I U O.
Proof.
  intros e f G L I a O H.
  exists (mask_diff I O). apply splitM_comm, splitM_diff.
  eapply infer_raw_le, H.
Qed.

(** Either the exact demand (linear mode) or a smaller demand extended by
    affine weakening. *)
Lemma typing_widen : forall f G L U V e a,
  has_type f G L U e a -> mask_le U V -> (f = Linear -> U = V) ->
  has_type f G L V e a.
Proof.
  intros [] G L U V e a H Hle Hexact.
  - rewrite (Hexact eq_refl) in H. exact H.
  - eapply TyWeak; eassumption.
Qed.

Lemma finish_binder_typing : forall f G L I used O tail e a,
  In_opt tail (finish_binder f O) -> SplitM (true :: I) used O ->
  has_type f G L used e a ->
  exists used_tail, SplitM I used_tail tail /\
    has_type f G L (true :: used_tail) e a.
Proof.
  intros f G L I used O tail e a Hfinish Hsplit Htyped.
  destruct (finish_binder_split _ _ _ _ _ Hfinish Hsplit)
    as [used_tail [Htail [Hle Hexact]]].
  exists used_tail. split; [exact Htail | ].
  eapply typing_widen; eassumption.
Qed.

Lemma finish_binder_typing2 : forall f G L I used O O' tail e a,
  In_opt O' (finish_binder f O) -> In_opt tail (finish_binder f O') ->
  SplitM (true :: true :: I) used O -> has_type f G L used e a ->
  exists used_tail, SplitM I used_tail tail /\
    has_type f G L (true :: true :: used_tail) e a.
Proof.
  intros f G L I used O O' tail e a Hfinish Hfinish' Hsplit Htyped.
  destruct (finish_binder_split _ _ _ _ _ Hfinish Hsplit)
    as [used' [Hsplit' [Hle Hexact]]].
  destruct (finish_binder_split _ _ _ _ _ Hfinish' Hsplit')
    as [used_tail [Htail [Hle' Hexact']]].
  exists used_tail. split; [exact Htail | ].
  eapply typing_widen; [exact Htyped | | ].
  - eapply mask_le_trans; [exact Hle | constructor; exact Hle'].
  - intros Hf. rewrite (Hexact Hf), (Hexact' Hf). reflexivity.
Qed.

(** Merged alternatives share one demand at which both branches can be
    retyped: the common demand in linear mode, the join in affine mode. *)
Lemma merge_leftovers_sound : forall f G L I U1 O1 U2 O2 O,
  SplitM I U1 O1 -> SplitM I U2 O2 -> In_opt O (merge_leftovers f O1 O2) ->
  exists U, SplitM I U O /\
    (forall e a, has_type f G L U1 e a -> has_type f G L U e a) /\
    (forall e a, has_type f G L U2 e a -> has_type f G L U e a).
Proof.
  intros [] G L I U1 O1 U2 O2 O H1 H2 Hmerge. apply In_opt_Some in Hmerge.
  simpl in Hmerge.
  - destruct (mask_eqb O1 O2) eqn:E; try discriminate.
    inversion Hmerge; subst. apply mask_eqb_eq in E. subst O2.
    pose proof (splitM_left_unique _ _ _ _ H1 H2). subst U2.
    exists U1. auto.
  - inversion Hmerge; subst.
    destruct (splitM_length _ _ _ H1) as [L1 _].
    destruct (splitM_length _ _ _ H2) as [L2 _].
    exists (mask_join U1 U2). split; [eapply splitM_join_remainders; eassumption | ].
    split; intros e a Ht; eapply TyWeak; [exact Ht | | exact Ht | ].
    + apply mask_le_join_l. congruence.
    + apply mask_le_join_r. congruence.
Qed.

Lemma infer_raw_length_scope : forall e f G L I a O,
  In_opt (a, O) (infer_raw f G L I e) -> length I = length L -> length O = length L.
Proof. intros. rewrite (infer_raw_length _ _ _ _ _ _ _ H). assumption. Qed.

(** Consuming a fixed position is stable when the same total demand is placed
    in a different availability frame. *)
Lemma mask_consume_frame : forall i I O C J P,
  In_opt O (mask_consume i I) ->
  SplitM I C O -> SplitM J C P ->
  In_opt P (mask_consume i J).
Proof.
  intros i I O C J P Hconsume HI HJ.
  pose proof (mask_consume_split _ _ _ Hconsume) as Hsingle.
  pose proof (splitM_left_unique _ _ _ _ Hsingle HI) as HC. subst C.
  pose proof (mask_consume_available _ _ _ Hconsume) as Havailable.
  apply In_opt_Some in Havailable.
  assert (Hbound : i < length I).
  { apply nth_error_Some. congruence. }
  pose proof (splitM_length _ _ _ HJ) as [Hsingle_length _].
  rewrite mask_single_length in Hsingle_length.
  assert (Hlength : length J = length I) by lia.
  eapply mask_consume_of_split.
  - eapply mask_le_nth; [eapply splitM_le_l, HJ | ].
    apply mask_single_nth. lia.
  - rewrite Hlength. exact HJ.
Qed.

(** Leaving a local resource scope is stable under framing of the outer
    resources. The local position itself is reconstructed in the new frame. *)
Lemma finish_binder_frame : forall f I body_out O body_used used J P,
  In_opt O (finish_binder f body_out) ->
  SplitM (true :: I) body_used body_out ->
  SplitM I used O -> SplitM J used P ->
  exists framed_out,
    SplitM (true :: J) body_used framed_out /\
    In_opt P (finish_binder f framed_out).
Proof.
  intros f I [| b body_out] O body_used used J P
    Hfinish Hbody Houter Hframe; apply In_opt_Some in Hfinish;
    destruct f; try discriminate.
  - destruct b; simpl in Hfinish; try discriminate.
    inversion Hfinish; subst. inversion Hbody; subst.
    match goal with
    | Htail : SplitM I _ O |- _ =>
        pose proof (splitM_left_unique _ _ _ _ Htail Houter) as ->
    end.
    exists (false :: P). split; [constructor; exact Hframe | reflexivity].
  - destruct b; simpl in Hfinish; inversion Hfinish; subst; inversion Hbody; subst.
    + match goal with
      | Htail : SplitM I _ O |- _ =>
          pose proof (splitM_left_unique _ _ _ _ Htail Houter) as ->
      end.
      exists (true :: P). split; [constructor; exact Hframe | reflexivity].
    + match goal with
      | Htail : SplitM I _ O |- _ =>
          pose proof (splitM_left_unique _ _ _ _ Htail Houter) as ->
      end.
      exists (false :: P). split; [constructor; exact Hframe | reflexivity].
Qed.

Lemma unchanged_frame : forall I C J P,
  SplitM I C I -> SplitM J C P -> J = P.
Proof.
  intros I C J P HI HJ.
  pose proof (splitM_left_unique _ _ _ _ HI (splitM_right I)) as ->.
  eapply splitM_zero_left_inv, HJ.
Qed.

(** ** Soundness

    The syntax-directed cases have three shapes: no resource demand, one
    premise passed through a rule, and two premises in sequence whose
    demands combine into one division of the input. *)

Lemma sound_unchanged : forall f G L I e a,
  length I = length L -> has_type f G L (mask_zero (length L)) e a ->
  exists U, SplitM I U I /\ has_type f G L U e a.
Proof.
  intros f G L I e a Hlen H. exists (mask_zero (length L)).
  split; [rewrite <- Hlen; apply splitM_right | exact H].
Qed.

Lemma sound_map : forall f G L I O e a e' b,
  (forall U, has_type f G L U e a -> has_type f G L U e' b) ->
  (exists U, SplitM I U O /\ has_type f G L U e a) ->
  exists U, SplitM I U O /\ has_type f G L U e' b.
Proof. intros f G L I O e a e' b rule [U [Hs Ht]]. exists U. auto. Qed.

Lemma infer_raw_sound_seq {e1 e2 f G G2 L I a1 O1 a2 O2} :
  (forall f G L I a O, length I = length L ->
    In_opt (a, O) (infer_raw f G L I e1) ->
    exists U, SplitM I U O /\ has_type f G L U e1 a) ->
  (forall f G L I a O, length I = length L ->
    In_opt (a, O) (infer_raw f G L I e2) ->
    exists U, SplitM I U O /\ has_type f G L U e2 a) ->
  length I = length L ->
  In_opt (a1, O1) (infer_raw f G L I e1) ->
  In_opt (a2, O2) (infer_raw f G2 L O1 e2) ->
  exists U U1 U2, SplitM I U O2 /\ SplitM U U1 U2 /\
    has_type f G L U1 e1 a1 /\ has_type f G2 L U2 e2 a2.
Proof.
  intros IH1 IH2 Hlen E1 E2.
  destruct (IH1 _ _ _ _ _ _ Hlen E1) as [U1 [H1 T1]].
  destruct (IH2 _ _ _ _ _ _ (infer_raw_length_scope _ _ _ _ _ _ _ E1 Hlen) E2)
    as [U2 [H2 T2]].
  destruct (splitM_unassoc _ _ _ _ _ H1 H2) as [U [Hw Hp]].
  exists U, U1, U2. auto.
Qed.

(** The two-premise shape with the rule that combines the premises. *)
Lemma sound_seq {e1 e2 f G G2 L I a1 O1 a2 O2} (e : term) (b : ty) :
  (forall f G L I a O, length I = length L ->
    In_opt (a, O) (infer_raw f G L I e1) ->
    exists U, SplitM I U O /\ has_type f G L U e1 a) ->
  (forall f G L I a O, length I = length L ->
    In_opt (a, O) (infer_raw f G L I e2) ->
    exists U, SplitM I U O /\ has_type f G L U e2 a) ->
  length I = length L ->
  In_opt (a1, O1) (infer_raw f G L I e1) ->
  In_opt (a2, O2) (infer_raw f G2 L O1 e2) ->
  (forall U U1 U2, SplitM U U1 U2 ->
    has_type f G L U1 e1 a1 -> has_type f G2 L U2 e2 a2 ->
    has_type f G L U e b) ->
  exists U, SplitM I U O2 /\ has_type f G L U e b.
Proof.
  intros IH1 IH2 Hlen E1 E2 rule.
  destruct (infer_raw_sound_seq IH1 IH2 Hlen E1 E2) as [U [U1 [U2 [Hw [Hp [T1 T2]]]]]].
  exists U. eauto.
Qed.

Lemma infer_raw_sound : forall e f G L I a O,
  length I = length L ->
  In_opt (a, O) (infer_raw f G L I e) ->
  exists U, SplitM I U O /\ has_type f G L U e a.
Proof.
  induction e; intros f G L I a O Hlen Hinfer; break_infer Hinfer.
  - exists (mask_single (length L) n). split.
    + rewrite <- Hlen. eapply mask_consume_split, Econsume.
    + apply TyLVar, Elookup.
  - apply sound_unchanged; [exact Hlen | apply TyUVar, Elookup].
  - destruct (IHe f G (t :: L) (true :: I) _ _ (f_equal S Hlen) Einfer)
      as [U [Hs Ht]].
    destruct (finish_binder_typing _ _ _ _ _ _ _ _ _ Efinish Hs Ht)
      as [U' [Hs' Ht']].
    exists U'. split; [exact Hs' | apply TyLam; exact Ht'].
  - eapply (sound_seq _ _ IHe1 IHe2 Hlen Einfer Einfer0).
    intros. eapply TyApp; eassumption.
  - apply sound_unchanged; [exact Hlen | apply TyUnit].
  - eapply (sound_seq _ _ IHe1 IHe2 Hlen Einfer Einfer0).
    intros. eapply TyLetUnit; eassumption.
  - eapply (sound_seq _ _ IHe1 IHe2 Hlen Einfer Einfer0).
    intros. eapply TyPair; eassumption.
  - destruct (IHe1 _ _ _ _ _ _ Hlen Einfer) as [U1 [H1 T1]].
    destruct (IHe2 f G (inferred_type2 :: inferred_type1 :: L)
      (true :: true :: leftovers) _ _
      (f_equal S (f_equal S (infer_raw_length_scope _ _ _ _ _ _ _ Einfer Hlen)))
      Einfer0) as [Ub [Hb Tb]].
    destruct (finish_binder_typing2 _ _ _ _ _ _ _ _ _ _ Efinish Efinish0 Hb Tb)
      as [U2 [H2 T2]].
    destruct (splitM_unassoc _ _ _ _ _ H1 H2) as [U [Hw Hp]].
    exists U. split; [exact Hw | eapply TyLetPair; eassumption].
  - destruct (IHe1 _ _ _ _ _ _ Hlen Einfer) as [U1 [H1 T1]].
    destruct (IHe2 _ _ _ _ _ _ Hlen Einfer0) as [U2 [H2 T2]].
    destruct (merge_leftovers_sound f G L _ _ _ _ _ _ H1 H2 Emerge)
      as [U [Hw [W1 W2]]].
    exists U. split; [exact Hw | apply TyWith; [apply W1, T1 | apply W2, T2]].
  - eapply sound_map; [intros ? ?; eapply TyFst; eassumption | eapply IHe; eassumption].
  - eapply sound_map; [intros ? ?; eapply TySnd; eassumption | eapply IHe; eassumption].
  - destruct (IHe _ _ _ _ _ _ Hlen Einfer) as [U [Hs Ht]].
    pose proof (splitM_left_unique _ _ _ _ Hs (splitM_right _)) as ->.
    apply sound_unchanged; [exact Hlen | apply TyBang; rewrite <- Hlen; exact Ht].
  - eapply (sound_seq _ _ IHe1 IHe2 Hlen Einfer Einfer0).
    intros. eapply TyLetBang; eassumption.
  - apply sound_unchanged; [exact Hlen | apply TyNat].
  - eapply sound_map; [intros ? ?; apply TySucc; eassumption | eapply IHe; eassumption].
  - destruct (IHe1 _ _ _ _ _ _ Hlen Einfer) as [Uc [Hc Tc]].
    destruct (infer_raw_sound_seq IHe2 IHe3
      (infer_raw_length_scope _ _ _ _ _ _ _ Einfer Hlen) Einfer0 Einfer1)
      as [R [Us [Uz [HR [Hp [Ts Tz]]]]]].
    destruct (splitM_unassoc _ _ _ _ _ Hc HR) as [U [Hw Hp']].
    exists U. split; [exact Hw | eapply TyIter; eassumption].
  - apply sound_unchanged; [exact Hlen | apply TyBool].
  - destruct (IHe1 _ _ _ _ _ _ Hlen Einfer) as [Uc [Hc Tc]].
    pose proof (infer_raw_length_scope _ _ _ _ _ _ _ Einfer Hlen) as Hlen_c.
    destruct (IHe2 _ _ _ _ _ _ Hlen_c Einfer0) as [U1 [H1 T1]].
    destruct (IHe3 _ _ _ _ _ _ Hlen_c Einfer1) as [U2 [H2 T2]].
    destruct (merge_leftovers_sound f G L _ _ _ _ _ _ H1 H2 Emerge)
      as [Ub [Hb [W1 W2]]].
    destruct (splitM_unassoc _ _ _ _ _ Hc Hb) as [U [Hw Hp]].
    exists U. split; [exact Hw | ].
    eapply TyIf; [exact Hp | exact Tc | apply W1, T1 | apply W2, T2].
  - eapply sound_map; [intros ? ?; apply TyNew; eassumption | eapply IHe; eassumption].
  - eapply (sound_seq _ _ IHe1 IHe2 Hlen Einfer Einfer0).
    intros. eapply TySwap; eassumption.
  - eapply sound_map; [intros ? ?; apply TyFree; eassumption | eapply IHe; eassumption].
Qed.

Theorem infer_sound : forall f G L I e a O,
  In_opt (a, O) (infer f G L I e) ->
  exists U, SplitM I U O /\ has_type f G L U e a.
Proof.
  intros f G L I e a O Hinfer. apply In_opt_Some in Hinfer. unfold infer in Hinfer.
  destruct (Nat.eqb (length I) (length L)) eqn:E; try discriminate.
  apply Nat.eqb_eq in E. eapply infer_raw_sound; [exact E | apply Some_In_opt, Hinfer].
Qed.

(** ** Framing

    A construct without demand leaves the frame unchanged; a single premise
    is framed by the induction hypothesis directly; two premises in sequence
    are framed one after the other. *)

Lemma infer_raw_frame_seq {e1 e2 f G G2 L I a1 O1 a2 O2 C J P} :
  (forall f G L I a O, In_opt (a, O) (infer_raw f G L I e1) ->
    forall C J P, SplitM I C O -> SplitM J C P ->
    In_opt (a, P) (infer_raw f G L J e1)) ->
  (forall f G L I a O, In_opt (a, O) (infer_raw f G L I e2) ->
    forall C J P, SplitM I C O -> SplitM J C P ->
    In_opt (a, P) (infer_raw f G L J e2)) ->
  In_opt (a1, O1) (infer_raw f G L I e1) ->
  In_opt (a2, O2) (infer_raw f G2 L O1 e2) ->
  SplitM I C O2 -> SplitM J C P ->
  exists P1, In_opt (a1, P1) (infer_raw f G L J e1) /\
    In_opt (a2, P) (infer_raw f G2 L P1 e2).
Proof.
  intros IH1 IH2 E1 E2 HI HJ.
  destruct (infer_raw_split _ _ _ _ _ _ _ E1) as [C1 H1].
  destruct (infer_raw_split _ _ _ _ _ _ _ E2) as [C2 H2].
  destruct (splitM_frame_sequence _ _ _ _ _ _ _ _ H1 H2 HI HJ) as [P1 [H1' H2']].
  exists P1. eauto.
Qed.

Lemma infer_raw_frame : forall e f G L I a O,
  In_opt (a, O) (infer_raw f G L I e) ->
  forall C J P, SplitM I C O -> SplitM J C P ->
  In_opt (a, P) (infer_raw f G L J e).
Proof.
  induction e; intros f G L I a O Hinfer C J P HI HJ; break_infer Hinfer.
  - apply Some_In_opt. cbn. rewrite (In_opt_Some Elookup),
      (In_opt_Some (mask_consume_frame _ _ _ _ _ _ Econsume HI HJ)). reflexivity.
  - pose proof (unchanged_frame _ _ _ _ HI HJ). subst P. apply Some_In_opt. cbn. rewrite (In_opt_Some Elookup). reflexivity.
  - destruct (infer_raw_split _ _ _ _ _ _ _ Einfer) as [Cb Hb].
    destruct (finish_binder_frame _ _ _ _ _ _ _ _ Efinish Hb HI HJ)
      as [Pb [Hb' Hfinish']].
    apply Some_In_opt. cbn. rewrite (In_opt_Some (IHe _ _ _ _ _ _ Einfer _ _ _ Hb Hb')), (In_opt_Some Hfinish'). reflexivity.
  - destruct (infer_raw_frame_seq IHe1 IHe2 Einfer Einfer0 HI HJ) as [P1 [E1 E2]].
    apply Some_In_opt. cbn. rewrite (In_opt_Some E1), (In_opt_Some E2), ty_eqb_refl. reflexivity.
  - pose proof (unchanged_frame _ _ _ _ HI HJ). subst P. apply Some_In_opt. reflexivity.
  - destruct (infer_raw_frame_seq IHe1 IHe2 Einfer Einfer0 HI HJ) as [P1 [E1 E2]].
    apply Some_In_opt. cbn. rewrite (In_opt_Some E1), (In_opt_Some E2). reflexivity.
  - destruct (infer_raw_frame_seq IHe1 IHe2 Einfer Einfer0 HI HJ) as [P1 [E1 E2]].
    apply Some_In_opt. cbn. rewrite (In_opt_Some E1), (In_opt_Some E2). reflexivity.
  - destruct (infer_raw_split _ _ _ _ _ _ _ Einfer) as [C1 H1].
    destruct (infer_raw_split _ _ _ _ _ _ _ Einfer0) as [Cb Hb].
    destruct (finish_binder_split _ _ _ _ _ Efinish Hb) as [Cr [Hr _]].
    destruct (finish_binder_split _ _ _ _ _ Efinish0 Hr) as [C2 [H2 _]].
    destruct (splitM_frame_sequence _ _ _ _ _ _ _ _ H1 H2 HI HJ)
      as [P1 [H1' H2']].
    destruct (finish_binder_frame _ _ _ _ _ _ _ _ Efinish0 Hr H2 H2')
      as [Pr [Hr' Hfinish2']].
    destruct (finish_binder_frame _ _ _ _ _ _ _ _ Efinish Hb Hr Hr')
      as [Pb [Hb' Hfinish1']].
    apply Some_In_opt. cbn. rewrite (In_opt_Some (IHe1 _ _ _ _ _ _ Einfer _ _ _ H1 H1')),
      (In_opt_Some (IHe2 _ _ _ _ _ _ Einfer0 _ _ _ Hb Hb')), (In_opt_Some Hfinish1'), (In_opt_Some Hfinish2').
    reflexivity.
  - destruct (infer_raw_split _ _ _ _ _ _ _ Einfer) as [C1 H1].
    destruct (infer_raw_split _ _ _ _ _ _ _ Einfer0) as [C2 H2].
    apply In_opt_Some in Emerge. destruct f; simpl in Emerge.
    + destruct (mask_eqb leftovers leftovers0) eqn:Emask; try discriminate.
      inversion Emerge; subst. apply mask_eqb_eq in Emask. subst leftovers0.
      pose proof (splitM_left_unique _ _ _ _ H1 HI) as ->.
      pose proof (splitM_left_unique _ _ _ _ H2 HI) as ->.
      apply Some_In_opt. cbn. rewrite (In_opt_Some (IHe1 _ _ _ _ _ _ Einfer _ _ _ HI HJ)),
        (In_opt_Some (IHe2 _ _ _ _ _ _ Einfer0 _ _ _ HI HJ)), mask_eqb_refl.
      reflexivity.
    + inversion Emerge; subst.
      destruct (splitM_frame_meet _ _ _ _ _ _ _ _ H1 H2 HI HJ)
        as [P1 [P2 [H1' [H2' Hmeet]]]].
      apply Some_In_opt. cbn. rewrite (In_opt_Some (IHe1 _ _ _ _ _ _ Einfer _ _ _ H1 H1')),
        (In_opt_Some (IHe2 _ _ _ _ _ _ Einfer0 _ _ _ H2 H2')), Hmeet.
      reflexivity.
  - apply Some_In_opt. cbn. rewrite (In_opt_Some (IHe _ _ _ _ _ _ Einfer _ _ _ HI HJ)). reflexivity.
  - apply Some_In_opt. cbn. rewrite (In_opt_Some (IHe _ _ _ _ _ _ Einfer _ _ _ HI HJ)). reflexivity.
  - pose proof (unchanged_frame _ _ _ _ HI HJ). subst P.
    apply Some_In_opt. cbn. rewrite (In_opt_Some (IHe _ _ _ _ _ _ Einfer _ _ _ HI HJ)), mask_eqb_refl. reflexivity.
  - destruct (infer_raw_frame_seq IHe1 IHe2 Einfer Einfer0 HI HJ) as [P1 [E1 E2]].
    apply Some_In_opt. cbn. rewrite (In_opt_Some E1), (In_opt_Some E2). reflexivity.
  - pose proof (unchanged_frame _ _ _ _ HI HJ). subst P. apply Some_In_opt. reflexivity.
  - apply Some_In_opt. cbn. rewrite (In_opt_Some (IHe _ _ _ _ _ _ Einfer _ _ _ HI HJ)), ty_eqb_refl. reflexivity.
  - destruct (infer_raw_split _ _ _ _ _ _ _ Einfer) as [Cc Hc].
    destruct (infer_raw_split _ _ _ _ _ _ _ Einfer0) as [Cs Hs].
    destruct (infer_raw_split _ _ _ _ _ _ _ Einfer1) as [Cz Hz].
    destruct (splitM_unassoc _ _ _ _ _ Hs Hz) as [Csz [Hsz _]].
    destruct (splitM_frame_sequence _ _ _ _ _ _ _ _ Hc Hsz HI HJ)
      as [Pc [Hc' Hsz']].
    destruct (infer_raw_frame_seq IHe2 IHe3 Einfer0 Einfer1 Hsz Hsz')
      as [Ps [Es Ez]].
    apply Some_In_opt. cbn. rewrite (In_opt_Some (IHe1 _ _ _ _ _ _ Einfer _ _ _ Hc Hc')), ty_eqb_refl, (In_opt_Some Es),
      ty_eqb_refl, (In_opt_Some Ez), ty_eqb_refl.
    reflexivity.
  - pose proof (unchanged_frame _ _ _ _ HI HJ). subst P. apply Some_In_opt. reflexivity.
  - destruct (infer_raw_split _ _ _ _ _ _ _ Einfer) as [Cc Hc].
    destruct (infer_raw_split _ _ _ _ _ _ _ Einfer0) as [C1 H1].
    destruct (infer_raw_split _ _ _ _ _ _ _ Einfer1) as [C2 H2].
    apply In_opt_Some in Emerge. destruct f; simpl in Emerge.
    + destruct (mask_eqb leftovers0 leftovers1) eqn:Emask; try discriminate.
      inversion Emerge; subst. apply mask_eqb_eq in Emask. subst leftovers1.
      pose proof (splitM_left_unique _ _ _ _ H1 H2) as ->.
      destruct (splitM_frame_sequence _ _ _ _ _ _ _ _ Hc H1 HI HJ)
        as [Pc [Hc' Hb']].
      apply Some_In_opt. cbn. rewrite (In_opt_Some (IHe1 _ _ _ _ _ _ Einfer _ _ _ Hc Hc')), ty_eqb_refl,
        (In_opt_Some (IHe2 _ _ _ _ _ _ Einfer0 _ _ _ H1 Hb')),
        (In_opt_Some (IHe3 _ _ _ _ _ _ Einfer1 _ _ _ H1 Hb')), ty_eqb_refl, mask_eqb_refl.
      reflexivity.
    + inversion Emerge; subst.
      pose proof (splitM_join_remainders _ _ _ _ _ H1 H2) as Hb.
      destruct (splitM_frame_sequence _ _ _ _ _ _ _ _ Hc Hb HI HJ)
        as [Pc [Hc' Hb']].
      destruct (splitM_frame_meet _ _ _ _ _ _ _ _ H1 H2 Hb Hb')
        as [P1 [P2 [H1' [H2' Hmeet]]]].
      apply Some_In_opt. cbn. rewrite (In_opt_Some (IHe1 _ _ _ _ _ _ Einfer _ _ _ Hc Hc')), ty_eqb_refl,
        (In_opt_Some (IHe2 _ _ _ _ _ _ Einfer0 _ _ _ H1 H1')),
        (In_opt_Some (IHe3 _ _ _ _ _ _ Einfer1 _ _ _ H2 H2')), ty_eqb_refl, Hmeet.
      reflexivity.
  - apply Some_In_opt. cbn. rewrite (In_opt_Some (IHe _ _ _ _ _ _ Einfer _ _ _ HI HJ)). reflexivity.
  - destruct (infer_raw_frame_seq IHe1 IHe2 Einfer Einfer0 HI HJ) as [P1 [E1 E2]].
    apply Some_In_opt. cbn. rewrite (In_opt_Some E1), (In_opt_Some E2). reflexivity.
  - apply Some_In_opt. cbn. rewrite (In_opt_Some (IHe _ _ _ _ _ _ Einfer _ _ _ HI HJ)), ty_eqb_refl. reflexivity.
Qed.

Theorem infer_frame : forall f G L I e a O C J P,
  In_opt (a, O) (infer f G L I e) ->
  SplitM I C O -> SplitM J C P ->
  In_opt (a, P) (infer f G L J e).
Proof.
  intros f G L I e a O C J P Hinfer HI HJ. apply In_opt_Some in Hinfer.
  unfold infer in *. destruct (Nat.eqb (length I) (length L)) eqn:EI;
    try discriminate.
  apply Nat.eqb_eq in EI.
  pose proof (splitM_length _ _ _ HI) as [HC_I _].
  pose proof (splitM_length _ _ _ HJ) as [HC_J _].
  assert (EJ : Nat.eqb (length J) (length L) = true).
  { apply Nat.eqb_eq. lia. }
  rewrite EJ.
  eapply infer_raw_frame; [apply Some_In_opt, Hinfer | exact HI | exact HJ].
Qed.

(** ** Completeness *)

Definition leftover_ok (f : flag) (expected actual : mask) : Prop :=
  match f with
  | Linear => actual = expected
  | Affine => mask_le expected actual
  end.

Lemma leftover_ok_refl : forall f O, leftover_ok f O O.
Proof. intros []; simpl; [reflexivity | apply mask_le_refl]. Qed.

Lemma leftover_ok_trans : forall f O1 O2 O3,
  leftover_ok f O1 O2 -> leftover_ok f O2 O3 -> leftover_ok f O1 O3.
Proof.
  intros [] O1 O2 O3 H12 H23; simpl in *.
  - congruence.
  - eapply mask_le_trans; eassumption.
Qed.

(** If an earlier affine premise leaves more resources than the declarative
    split requires, those resources pass through the next premise. *)
Lemma splitM_continue : forall f I U F O,
  SplitM I U F -> leftover_ok f I O ->
  exists P, SplitM O U P /\ leftover_ok f F P.
Proof.
  intros [] I U F O Hsplit Hok; simpl in *.
  - subst O. exists F. split; [exact Hsplit | reflexivity].
  - destruct (splitM_extend _ _ _ Hsplit _ Hok) as [P [Hs Hp]].
    exists P. split; assumption.
Qed.

Lemma finish_binder_complete : forall f F O,
  leftover_ok f (false :: F) O ->
  exists tail, In_opt tail (finish_binder f O) /\ leftover_ok f F tail.
Proof.
  intros [] F O Hok; simpl in Hok.
  - subst O. exists F. split; reflexivity.
  - destruct O as [| b O]; inversion Hok; subst.
    exists O. split; [destruct b; reflexivity | assumption].
Qed.

Lemma merge_leftovers_complete : forall f F O1 O2,
  leftover_ok f F O1 -> leftover_ok f F O2 ->
  exists O, In_opt O (merge_leftovers f O1 O2) /\ leftover_ok f F O.
Proof.
  intros [] F O1 O2 H1 H2; simpl in *.
  - subst O1 O2. exists F. split.
    + simpl. rewrite mask_eqb_refl. reflexivity.
    + reflexivity.
  - exists (mask_meet O1 O2). split; [reflexivity | ].
    eapply mask_meet_greatest; eassumption.
Qed.

(** The same three shapes as for soundness: a construct without demand
    returns its input, one premise is passed through a computation, and two
    premises run in sequence after reassociating the declarative division. *)

Lemma complete_unchanged : forall f G L I F e a n,
  SplitM I (mask_zero n) F -> In_opt (a, I) (infer_raw f G L I e) ->
  exists O, In_opt (a, O) (infer_raw f G L I e) /\ leftover_ok f F O.
Proof.
  intros f G L I F e a n HI E. pose proof (splitM_zero_left_inv _ _ _ HI) as <-.
  exists I. split; [exact E | apply leftover_ok_refl].
Qed.

Lemma complete_map : forall f G L I F e a e' b,
  (forall O, In_opt (a, O) (infer_raw f G L I e) -> In_opt (b, O) (infer_raw f G L I e')) ->
  (exists O, In_opt (a, O) (infer_raw f G L I e) /\ leftover_ok f F O) ->
  exists O, In_opt (b, O) (infer_raw f G L I e') /\ leftover_ok f F O.
Proof. intros f G L I F e a e' b rule [O [E Hok]]. exists O. auto. Qed.

Lemma infer_raw_complete_seq {f G G2 L e1 e2 U U1 U2 a1 a2 I F} :
  (forall I F, SplitM I U1 F ->
    exists O, In_opt (a1, O) (infer_raw f G L I e1) /\ leftover_ok f F O) ->
  (forall I F, SplitM I U2 F ->
    exists O, In_opt (a2, O) (infer_raw f G2 L I e2) /\ leftover_ok f F O) ->
  SplitM U U1 U2 -> SplitM I U F ->
  exists O1 O2, In_opt (a1, O1) (infer_raw f G L I e1) /\
    In_opt (a2, O2) (infer_raw f G2 L O1 e2) /\ leftover_ok f F O2.
Proof.
  intros IH1 IH2 H HI.
  destruct (splitM_assoc _ _ _ _ _ HI H) as [R [H1 HR]].
  destruct (IH1 _ _ H1) as [O1 [E1 Hok1]].
  destruct (splitM_continue _ _ _ _ _ HR Hok1) as [F2 [H2 HokF]].
  destruct (IH2 _ _ H2) as [O2 [E2 Hok2]].
  exists O1, O2. repeat split; try assumption.
  eapply leftover_ok_trans; eassumption.
Qed.

Lemma complete_seq {f G G2 L e1 e2 U U1 U2 a1 a2 I F} (e : term) (b : ty) :
  (forall I F, SplitM I U1 F ->
    exists O, In_opt (a1, O) (infer_raw f G L I e1) /\ leftover_ok f F O) ->
  (forall I F, SplitM I U2 F ->
    exists O, In_opt (a2, O) (infer_raw f G2 L I e2) /\ leftover_ok f F O) ->
  SplitM U U1 U2 -> SplitM I U F ->
  (forall I O1 O2, In_opt (a1, O1) (infer_raw f G L I e1) ->
    In_opt (a2, O2) (infer_raw f G2 L O1 e2) -> In_opt (b, O2) (infer_raw f G L I e)) ->
  exists O, In_opt (b, O) (infer_raw f G L I e) /\ leftover_ok f F O.
Proof.
  intros IH1 IH2 H HI rule.
  destruct (infer_raw_complete_seq IH1 IH2 H HI) as [O1 [O2 [E1 [E2 Hok]]]].
  exists O2. eauto.
Qed.

Lemma infer_raw_complete : forall f G L U e a,
  has_type f G L U e a ->
  forall I F, SplitM I U F ->
  exists O, In_opt (a, O) (infer_raw f G L I e) /\ leftover_ok f F O.
Proof.
  intros f G L U e a Htyped. induction Htyped; intros I F HI.
  - apply In_opt_Some in H.
    assert (Hbound : i < length L).
    { apply nth_error_Some. congruence. }
    pose proof (splitM_length _ _ _ HI) as [HU _].
    rewrite mask_single_length in HU.
    assert (Hconsume : In_opt F (mask_consume i I)).
    { eapply mask_consume_of_split; [ | rewrite <- HU; exact HI].
      eapply mask_le_nth; [eapply splitM_le_l, HI | ].
      apply mask_single_nth. exact Hbound. }
    exists F. split; [ | apply leftover_ok_refl].
    apply Some_In_opt. cbn. rewrite H, (In_opt_Some Hconsume). reflexivity.
  - apply In_opt_Some in H.
    eapply complete_unchanged; [exact HI | apply Some_In_opt; cbn; rewrite H; reflexivity].
  - destruct (IHHtyped (true :: I) (false :: F) ltac:(constructor; exact HI))
      as [Ob [Ebody Hok]].
    destruct (finish_binder_complete _ _ _ Hok) as [O [Efinish Hok']].
    exists O. split; [ | exact Hok'].
    apply Some_In_opt. cbn. rewrite (In_opt_Some Ebody), (In_opt_Some Efinish). reflexivity.
  - eapply (complete_seq _ _ IHHtyped1 IHHtyped2 H HI).
    intros ? ? ? E1 E2. apply Some_In_opt. cbn.
    rewrite (In_opt_Some E1), (In_opt_Some E2), ty_eqb_refl. reflexivity.
  - eapply complete_unchanged; [exact HI | apply Some_In_opt; reflexivity].
  - eapply (complete_seq _ _ IHHtyped1 IHHtyped2 H HI).
    intros ? ? ? E1 E2. apply Some_In_opt. cbn.
    rewrite (In_opt_Some E1), ty_eqb_refl, (In_opt_Some E2). reflexivity.
  - eapply (complete_seq _ _ IHHtyped1 IHHtyped2 H HI).
    intros ? ? ? E1 E2. apply Some_In_opt. cbn.
    rewrite (In_opt_Some E1), (In_opt_Some E2). reflexivity.
  - destruct (splitM_assoc _ _ _ _ _ HI H) as [R [H1 HR]].
    destruct (IHHtyped1 _ _ H1) as [O1 [E1 Hok1]].
    destruct (splitM_continue _ _ _ _ _ HR Hok1) as [F2 [H2 HokF]].
    destruct (IHHtyped2 (true :: true :: O1) (false :: false :: F2)
      ltac:(constructor; constructor; exact H2)) as [Ob [Ebody Hokbody]].
    destruct (finish_binder_complete _ _ _ Hokbody) as [O3 [Efinish1 Hok3]].
    destruct (finish_binder_complete _ _ _ Hok3) as [O4 [Efinish2 Hok4]].
    exists O4. split.
    + apply Some_In_opt. cbn.
      rewrite (In_opt_Some E1), (In_opt_Some Ebody), (In_opt_Some Efinish1),
        (In_opt_Some Efinish2). reflexivity.
    + eapply leftover_ok_trans; eassumption.
  - destruct (IHHtyped1 _ _ HI) as [O1 [E1 Hok1]].
    destruct (IHHtyped2 _ _ HI) as [O2 [E2 Hok2]].
    destruct (merge_leftovers_complete _ _ _ _ Hok1 Hok2) as [O [Emerge Hok]].
    exists O. split; [ | exact Hok].
    apply Some_In_opt. cbn.
    rewrite (In_opt_Some E1), (In_opt_Some E2), (In_opt_Some Emerge). reflexivity.
  - eapply complete_map; [ | apply IHHtyped, HI].
    intros ? E. apply Some_In_opt. cbn. rewrite (In_opt_Some E). reflexivity.
  - eapply complete_map; [ | apply IHHtyped, HI].
    intros ? E. apply Some_In_opt. cbn. rewrite (In_opt_Some E). reflexivity.
  - pose proof (splitM_zero_left_inv _ _ _ HI) as <-.
    destruct (IHHtyped I I HI) as [O [Ebody Hok]].
    assert (EO : O = I).
    { destruct f; simpl in Hok.
      - exact Hok.
      - apply mask_le_antisym; [eapply infer_raw_le, Ebody | exact Hok]. }
    subst O. eapply complete_unchanged; [exact HI | ].
    apply Some_In_opt. cbn. rewrite (In_opt_Some Ebody), mask_eqb_refl. reflexivity.
  - eapply (complete_seq _ _ IHHtyped1 IHHtyped2 H HI).
    intros ? ? ? E1 E2. apply Some_In_opt. cbn.
    rewrite (In_opt_Some E1), (In_opt_Some E2). reflexivity.
  - eapply complete_unchanged; [exact HI | apply Some_In_opt; reflexivity].
  - eapply complete_map; [ | apply IHHtyped, HI].
    intros ? E. apply Some_In_opt. cbn. rewrite (In_opt_Some E), ty_eqb_refl. reflexivity.
  - destruct (splitM_assoc _ _ _ _ _ HI H) as [R1 [Hc HR]].
    destruct (IHHtyped1 _ _ Hc) as [Oc [Ec Hokc]].
    destruct (splitM_continue _ _ _ _ _ HR Hokc) as [F1 [HR' HokF1]].
    destruct (infer_raw_complete_seq IHHtyped2 IHHtyped3 H0 HR')
      as [Os [Oz [Es [Ez Hok]]]].
    exists Oz. split.
    + apply Some_In_opt. cbn.
      rewrite (In_opt_Some Ec), ty_eqb_refl, (In_opt_Some Es), ty_eqb_refl,
        (In_opt_Some Ez), ty_eqb_refl. reflexivity.
    + eapply leftover_ok_trans; eassumption.
  - eapply complete_unchanged; [exact HI | apply Some_In_opt; reflexivity].
  - destruct (splitM_assoc _ _ _ _ _ HI H) as [R [Hc Hb]].
    destruct (IHHtyped1 _ _ Hc) as [Oc [Ec Hokc]].
    destruct (splitM_continue _ _ _ _ _ Hb Hokc) as [Fb [Hb' HokF]].
    destruct (IHHtyped2 _ _ Hb') as [O1 [E1 Hok1]].
    destruct (IHHtyped3 _ _ Hb') as [O2 [E2 Hok2]].
    destruct (merge_leftovers_complete _ _ _ _ Hok1 Hok2) as [O [Emerge Hok]].
    exists O. split.
    + apply Some_In_opt. cbn.
      rewrite (In_opt_Some Ec), ty_eqb_refl, (In_opt_Some E1), (In_opt_Some E2),
        ty_eqb_refl, (In_opt_Some Emerge). reflexivity.
    + eapply leftover_ok_trans; [exact HokF | exact Hok].
  - eapply complete_map; [ | apply IHHtyped, HI].
    intros ? E. apply Some_In_opt. cbn. rewrite (In_opt_Some E). reflexivity.
  - eapply (complete_seq _ _ IHHtyped1 IHHtyped2 H HI).
    intros ? ? ? E1 E2. apply Some_In_opt. cbn.
    rewrite (In_opt_Some E1), (In_opt_Some E2). reflexivity.
  - eapply complete_map; [ | apply IHHtyped, HI].
    intros ? E. apply Some_In_opt. cbn. rewrite (In_opt_Some E), ty_eqb_refl. reflexivity.
  - match goal with
    | Hle : mask_le _ _ |- _ =>
        destruct (splitM_shrink_left _ _ _ HI _ Hle) as [F' [HI' HFF']]
    end.
    destruct (IHHtyped _ _ HI') as [O [E Hok]].
    exists O. split; [exact E | ].
    simpl in *. eapply mask_le_trans; eassumption.
Qed.

Theorem infer_complete : forall f G L U e a I F,
  has_type f G L U e a -> SplitM I U F ->
  exists O, In_opt (a, O) (infer f G L I e) /\
    leftover_ok f F O /\ mask_le O I.
Proof.
  intros f G L U e a I F Htyped Hsplit.
  destruct (infer_raw_complete _ _ _ _ _ _ Htyped _ _ Hsplit)
    as [O [Einfer Hok]].
  exists O. repeat split.
  - unfold infer.
    pose proof (typing_wf_mask _ _ _ _ _ _ Htyped) as HU.
    unfold wf_mask in HU.
    pose proof (splitM_length _ _ _ Hsplit) as [HUI _].
    assert (Elen : Nat.eqb (length I) (length L) = true).
    { apply Nat.eqb_eq. lia. }
    rewrite Elen. exact Einfer.
  - exact Hok.
  - eapply infer_raw_le, Einfer.
Qed.

(** ** Open terms and closed programs

    The leftover mask is meaningful to a caller that continues checking. An
    open term taken on its own must consume every available resource in
    linear mode; affine mode may leave resources unused. *)

Definition check_open (f : flag) (G L : list ty) (I : mask) (e : term)
    : option ty :=
  match infer f G L I e with
  | Some (a, leftovers) =>
      match f with
      | Linear =>
          if mask_eqb leftovers (mask_zero (length L)) then Some a else None
      | Affine => Some a
      end
  | None => None
  end.

Definition check_program (f : flag) (e : term) : option ty :=
  check_open f [] [] [] e.

(** In linear mode the available mask is exactly the demand; in affine mode
    it bounds the demand. *)
Lemma check_open_sound : forall f G L I e a,
  In_opt a (check_open f G L I e) ->
  exists U, mask_le U I /\ (f = Linear -> U = I) /\ has_type f G L U e a.
Proof.
  intros f G L I e a H. apply In_opt_Some in H. unfold check_open in H.
  destruct (infer f G L I e) as [[b O] |] eqn:E; try discriminate.
  destruct (infer_sound _ _ _ _ _ _ _ (Some_In_opt E)) as [U [Hsplit Htyped]].
  destruct f.
  - destruct (mask_eqb O (mask_zero (length L))) eqn:Ez; try discriminate.
    inversion H; subst. apply mask_eqb_eq in Ez. subst O.
    exists U. split; [eapply splitM_le_l, Hsplit | split; [ | exact Htyped]].
    intros _. symmetry. eapply splitM_zero_right_inv, Hsplit.
  - inversion H; subst.
    exists U. split; [eapply splitM_le_l, Hsplit | split; [discriminate | exact Htyped]].
Qed.

Lemma check_open_complete : forall f G L U e a,
  has_type f G L U e a -> In_opt a (check_open f G L U e).
Proof.
  intros f G L U e a H. apply Some_In_opt. unfold check_open.
  pose proof (typing_wf_mask _ _ _ _ _ _ H) as Hw. unfold wf_mask in Hw.
  assert (Hsplit : SplitM U U (mask_zero (length L))).
  { rewrite <- Hw. apply splitM_left. }
  destruct (infer_complete _ _ _ _ _ _ _ _ H Hsplit) as [O [E [Hok _]]].
  rewrite (In_opt_Some E). destruct f; simpl in Hok.
  - subst O. rewrite mask_eqb_refl. reflexivity.
  - reflexivity.
Qed.

Theorem check_program_sound : forall f e a,
  In_opt a (check_program f e) -> has_type f [] [] [] e a.
Proof.
  intros f e a H. destruct (check_open_sound _ _ _ _ _ _ H) as [U [Hle [_ Htyped]]].
  inversion Hle; subst. exact Htyped.
Qed.

Theorem check_program_complete : forall f e a,
  has_type f [] [] [] e a -> In_opt a (check_program f e).
Proof. intros. apply check_open_complete. assumption. Qed.
