(** * Multi-step safety of typed configurations

    Preservation and progress compose over the reflexive-transitive closure of
    small-step evaluation. Consequently, the fuelled evaluator may return a
    value or time out, but it cannot report a typed execution as stuck.
    Store-event lifetimes exclude repeated deallocation without intervening
    allocation, and exact linear ownership excludes leaks from terminating
    closed programs of type [nat]. *)

From Stdlib Require Import List Arith Bool.
From DILLref Require Import Ty Syntax Typing NatMap Graph Store Semantics StoreTyping.
From DILLref Require Import StoreTypingInversion.
From DILLref Require Import Preservation Progress.
Import ListNotations.

Theorem reaches_configuration_preservation : forall f c c' a,
  reaches c c' ->
  configuration_typed f (fst c) (snd c) a ->
  configuration_typed f (fst c') (snd c') a.
Proof.
  intros f c c' a Hreach. induction Hreach; intros Htyped.
  - exact Htyped.
  - apply IHHreach. destruct c1 as [s1 e1], c2 as [s2 e2].
    cbn [fst snd] in *. eapply configuration_preservation; eassumption.
Qed.

Theorem configuration_no_dangling : forall f s e a l,
  configuration_typed f s e a ->
  In l (locations e) \/ (exists owner, store_edge s owner l) ->
  In l (natmap_domain s).
Proof.
  intros f s e a l [Hbalance _] Hlocation.
  eapply balance_allocated; eassumption.
Qed.

Corollary runFuel_configuration_preservation : forall fuel f c a,
  configuration_typed f (fst c) (snd c) a ->
  configuration_typed f
    (fst (run_result_config (runFuel fuel c)))
    (snd (run_result_config (runFuel fuel c))) a.
Proof.
  intros fuel f c a Htyped.
  eapply reaches_configuration_preservation.
  - apply runFuel_reachable.
  - exact Htyped.
Qed.

Corollary reachable_configuration_not_stuck : forall f c c' a,
  reaches c c' ->
  configuration_typed f (fst c) (snd c) a ->
  step c' <> SStuck.
Proof.
  intros f c [s' e'] a Hreach Htyped. cbn [fst snd] in *.
  apply (typed_configuration_not_stuck f s' e' a).
  exact (reaches_configuration_preservation
    f c (s', e') a Hreach Htyped).
Qed.

Theorem runFuel_typed_not_stuck : forall fuel f c c' a,
  configuration_typed f (fst c) (snd c) a ->
  runFuel fuel c <> RStuck c'.
Proof.
  intros fuel f c c' a Htyped Hrun.
  pose proof (runFuel_reachable fuel c) as Hreach.
  rewrite Hrun in Hreach. cbn [run_result_config] in Hreach.
  apply (reachable_configuration_not_stuck f c c' a Hreach Htyped).
  eapply runFuel_stuck_final. exact Hrun.
Qed.

(** ** Store-event lifetimes

    The live-address indices make address reuse explicit. An allocation starts
    a new lifetime only when its numeric address is absent; a free ends the
    current lifetime; swap preserves it. *)
Inductive event_lifetime : list nat -> list store_event -> list nat -> Prop :=
  | LifetimeRefl : forall live,
      event_lifetime live [] live
  | LifetimeAlloc : forall live l events final,
      ~ In l live ->
      event_lifetime (l :: live) events final ->
      event_lifetime live (EventAlloc l :: events) final
  | LifetimeSwap : forall live l events final,
      In l live ->
      event_lifetime live events final ->
      event_lifetime live (EventSwap l :: events) final
  | LifetimeFree : forall live l events final,
      In l live ->
      event_lifetime
        (filter (fun k => negb (Nat.eqb l k)) live) events final ->
      event_lifetime live (EventFree l :: events) final.

Theorem event_trace_lifetime : forall c events c',
  event_trace c events c' ->
  event_lifetime (natmap_domain (fst c)) events
    (natmap_domain (fst c')).
Proof.
  intros c events c' Htrace. induction Htrace.
  - constructor.
  - destruct c1 as [s1 e1], c2 as [s2 e2], c3 as [s3 e3].
    cbn [fst] in *. pose proof (silent_step_store_unchanged _ _ _ _ H) as E.
    subst s2. exact IHHtrace.
  - destruct c1 as [s1 e1], c2 as [s2 e2], c3 as [s3 e3].
    cbn [fst] in *.
    pose proof (labelled_step_store_transition _ _ _ _ _ H) as Hdomain.
    destruct event; cbn [event_store_transition] in Hdomain;
      destruct Hdomain as [Hlive Hdomain].
    + eapply LifetimeAlloc; [exact Hlive | ].
      rewrite <- Hdomain. exact IHHtrace.
    + eapply LifetimeSwap; [exact Hlive | ].
      rewrite <- Hdomain. exact IHHtrace.
    + eapply LifetimeFree; [exact Hlive | ].
      rewrite <- Hdomain. exact IHHtrace.
Qed.

Lemma event_lifetime_app_inv : forall before first second after,
  event_lifetime before (first ++ second) after ->
  exists middle,
    event_lifetime before first middle /\
    event_lifetime middle second after.
Proof.
  intros before first. revert before.
  induction first as [| event first IH]; intros before second after Hlife.
  - exists before. split; [constructor | exact Hlife].
  - destruct event; inversion Hlife; subst.
    + match goal with
      | Htail : event_lifetime _ (first ++ second) after |- _ =>
          destruct (IH _ _ _ Htail) as [middle [Hfirst Hsecond]]
      end.
      exists middle. split; [econstructor; eassumption | exact Hsecond].
    + match goal with
      | Htail : event_lifetime _ (first ++ second) after |- _ =>
          destruct (IH _ _ _ Htail) as [middle [Hfirst Hsecond]]
      end.
      exists middle. split; [econstructor; eassumption | exact Hsecond].
    + match goal with
      | Htail : event_lifetime _ (first ++ second) after |- _ =>
          destruct (IH _ _ _ Htail) as [middle [Hfirst Hsecond]]
      end.
      exists middle. split; [econstructor; eassumption | exact Hsecond].
Qed.

Lemma event_lifetime_free_inv : forall live l events final,
  event_lifetime live (EventFree l :: events) final ->
  In l live /\
  event_lifetime
    (filter (fun k => negb (Nat.eqb l k)) live) events final.
Proof. intros live l events final Hlife. inversion Hlife; subst; auto. Qed.

Lemma event_lifetime_no_alloc_preserves_absence :
  forall before events after l,
  event_lifetime before events after ->
  ~ In (EventAlloc l) events ->
  ~ In l before ->
  ~ In l after.
Proof.
  intros before events after l Hlife. induction Hlife;
    intros Hno_alloc Habsent.
  - exact Habsent.
  - apply IHHlife.
    + intros Hin. apply Hno_alloc. right. exact Hin.
    + intros [E | Hin].
      * subst. apply Hno_alloc. left. reflexivity.
      * apply Habsent. exact Hin.
  - apply IHHlife.
    + intros Hin. apply Hno_alloc. right. exact Hin.
    + exact Habsent.
  - apply IHHlife.
    + intros Hin. apply Hno_alloc. right. exact Hin.
    + intros Hin. apply filter_In in Hin. apply Habsent. tauto.
Qed.

(** Two frees of the same numeric address must belong to different lifetimes:
    the trace contains a fresh allocation of that address between them. *)
Definition free_events_separated (events : list store_event) : Prop :=
  forall l prefix between suffix,
    events = prefix ++ EventFree l :: between ++ EventFree l :: suffix ->
    In (EventAlloc l) between.

Lemma event_lifetime_free_events_separated : forall before events after,
  event_lifetime before events after -> free_events_separated events.
Proof.
  intros before events after Hlife.
  intros l prefix between suffix Eevents.
  subst events.
  destruct (event_lifetime_app_inv _ _ _ _ Hlife)
    as [before_first [_ Hfirst]].
  destruct (event_lifetime_free_inv _ _ _ _ Hfirst)
    as [_ Hafter_first].
  destruct (event_lifetime_app_inv _ _ _ _ Hafter_first)
    as [before_second [Hbetween Hsecond]].
  destruct (event_lifetime_free_inv _ _ _ _ Hsecond)
    as [Hsecond_live _].
  destruct (in_dec store_event_eq_dec (EventAlloc l) between) as [Hin | Hnot].
  - exact Hin.
  - exfalso.
    assert (Habsent : ~ In l before_second).
    { eapply event_lifetime_no_alloc_preserves_absence; eauto.
      rewrite filter_In. intros [_ Hkeep].
      rewrite Nat.eqb_refl in Hkeep. discriminate. }
    exact (Habsent Hsecond_live).
Qed.

Theorem no_double_free : forall c events c',
  event_trace c events c' -> free_events_separated events.
Proof.
  intros c events c' Htrace.
  eapply event_lifetime_free_events_separated.
  apply event_trace_lifetime. exact Htrace.
Qed.

Corollary runFuelTrace_no_double_free : forall fuel c,
  free_events_separated (trace_result_events (runFuelTrace fuel c)).
Proof.
  intros fuel c. eapply no_double_free.
  apply runFuelTrace_event_trace.
Qed.

(** Typed preservation and no-dangling turn the domain effect of a free into
    absence from both the residual term and every remaining cell. *)
Theorem free_removes_location_ownership : forall f s e s' e' a l,
  configuration_typed f s e a ->
  labelled_step (EventFree l) (s, e) (s', e') ->
  ~ In l (natmap_domain s') /\
  ~ In l (locations e') /\
  (forall owner, ~ store_edge s' owner l).
Proof.
  intros f s e s' e' a l Htyped Hfree.
  assert (Htyped' : configuration_typed f s' e' a).
  { eapply configuration_preservation.
    - apply labelled_step_sound with (event := EventFree l). exact Hfree.
    - exact Htyped. }
  pose proof (labelled_step_store_transition _ _ _ _ _ Hfree)
    as [_ Hdomain].
  assert (Habsent : ~ In l (natmap_domain s')).
  { rewrite Hdomain, filter_In. intros [_ Hkeep].
    rewrite Nat.eqb_refl in Hkeep. discriminate. }
  split; [exact Habsent | split].
  - intros Hlocation. apply Habsent.
    eapply configuration_no_dangling; [exact Htyped' | left; exact Hlocation].
  - intros owner Hedge. apply Habsent.
    eapply configuration_no_dangling; [exact Htyped' | right].
    exists owner. exact Hedge.
Qed.

(** With no locations in the running term, root reachability leaves no place
    from which an allocated cell could be reached. *)
Lemma linear_location_free_configuration_empty : forall s e a,
  configuration_typed Linear s e a -> locations e = [] -> s = [].
Proof.
  intros [| [l v] s] e a Htyped Hlocations; [reflexivity | exfalso].
  assert (Hallocated : In l (natmap_domain ((l, v) :: s))) by (simpl; auto).
  pose proof (linear_configuration_root_reachable
    ((l, v) :: s) e a l Htyped Hallocated) as Hreachable.
  unfold root_reachable, graph_root_reachable in Hreachable.
  rewrite Hlocations in Hreachable. simpl in Hreachable.
  destruct Hreachable as [Hroot | [root [Hroot _]]]; contradiction.
Qed.

(** A terminating closed linear program of type [nat] cannot leave allocated
    cells. Source typing initializes the empty configuration; preservation and
    the canonical form of the final value reduce the result to the preceding
    root-reachability argument. *)
Theorem no_leak : forall e s v,
  has_type Linear [] [] [] e TNat ->
  reaches ([], e) (s, v) -> value v -> s = [].
Proof.
  intros e s v Htype Hreaches Hvalue.
  assert (Hfinal : configuration_typed Linear s v TNat).
  { exact (reaches_configuration_preservation Linear ([], e) (s, v) TNat
      Hreaches (source_configuration Linear e TNat Htype)). }
  assert (Hcanonical : exists n, v = Nat n).
  { destruct Hfinal as
      [[S Rt Rr Rc Rf Hnd Hcells Hterm Hsplit Hrest Hmode] Hacy].
    eapply canonical_nat; eassumption. }
  destruct Hcanonical as [n ->].
  eapply linear_location_free_configuration_empty.
  - exact Hfinal.
  - reflexivity.
Qed.
