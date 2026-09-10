(** * Deterministic small-step evaluation

    Evaluation is call by value and left to right in every strict position.
    Lambda bodies, promotions and additive pair components remain suspended.
    The typing flag is absent: programs accepted in both modes execute with
    the same relation and function.

    [step_raw] is structurally recursive on the term. [small_step] is an
    independent relation using the same deterministic allocator [fresh]. *)

From Stdlib Require Import List Arith.
From DILLref Require Import Prelude Syntax Substitution NatMap Store.
Import ListNotations.

Definition config : Type := (store * term)%type.

(** Store events are emitted only by successful primitive operations. *)
Inductive store_event : Type :=
  | EventAlloc : nat -> store_event
  | EventSwap : nat -> store_event
  | EventFree : nat -> store_event.

Definition store_event_eq_dec (left right : store_event)
    : {left = right} + {left <> right}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Inductive raw_step_result : Type :=
  | RawValue : raw_step_result
  | RawStuck : raw_step_result
  | RawStep : config -> option store_event -> raw_step_result.

Inductive step_result : Type :=
  | SValue : step_result
  | SStuck : step_result
  | SStep : config -> step_result.

(** The worker reports whether the current term is already a value, is stuck,
    or takes exactly one optionally labelled step. Recursive calls are only on
    strict immediate subterms; a label is propagated through the surrounding
    evaluation context without another traversal. *)
Fixpoint step_raw (s : store) (e : term) {struct e} : raw_step_result :=
  match e with
  | LVar _ | UVar _ => RawStuck
  | Loc _ | Lam _ _ | Unit | With _ _ | Bang _ | Nat _ | Bool _ => RawValue
  | App e1 e2 =>
      match step_raw s e1 with
      | RawStep (s', e1') event => RawStep (s', App e1' e2) event
      | RawStuck => RawStuck
      | RawValue =>
          match step_raw s e2 with
          | RawStep (s', e2') event => RawStep (s', App e1 e2') event
          | RawStuck => RawStuck
          | RawValue =>
              match e1 with
              | Lam _ body => RawStep (s, subst_l e2 body) None
              | _ => RawStuck
              end
          end
      end
  | LetUnit e1 body =>
      match step_raw s e1 with
      | RawStep (s', e1') event => RawStep (s', LetUnit e1' body) event
      | RawStuck => RawStuck
      | RawValue =>
          match e1 with Unit => RawStep (s, body) None | _ => RawStuck end
      end
  | Pair e1 e2 =>
      match step_raw s e1 with
      | RawStep (s', e1') event => RawStep (s', Pair e1' e2) event
      | RawStuck => RawStuck
      | RawValue =>
          match step_raw s e2 with
          | RawStep (s', e2') event => RawStep (s', Pair e1 e2') event
          | RawStuck => RawStuck
          | RawValue => RawValue
          end
      end
  | LetPair e1 body =>
      match step_raw s e1 with
      | RawStep (s', e1') event => RawStep (s', LetPair e1' body) event
      | RawStuck => RawStuck
      | RawValue =>
          match e1 with
          | Pair v1 v2 => RawStep (s, subst_l v1 (subst_l v2 body)) None
          | _ => RawStuck
          end
      end
  | Fst e1 =>
      match step_raw s e1 with
      | RawStep (s', e1') event => RawStep (s', Fst e1') event
      | RawStuck => RawStuck
      | RawValue =>
          match e1 with
          | With e_left _ => RawStep (s, e_left) None
          | _ => RawStuck
          end
      end
  | Snd e1 =>
      match step_raw s e1 with
      | RawStep (s', e1') event => RawStep (s', Snd e1') event
      | RawStuck => RawStuck
      | RawValue =>
          match e1 with
          | With _ e_right => RawStep (s, e_right) None
          | _ => RawStuck
          end
      end
  | LetBang e1 body =>
      match step_raw s e1 with
      | RawStep (s', e1') event => RawStep (s', LetBang e1' body) event
      | RawStuck => RawStuck
      | RawValue =>
          match e1 with
          | Bang suspended => RawStep (s, subst_u suspended body) None
          | _ => RawStuck
          end
      end
  | Succ e1 =>
      match step_raw s e1 with
      | RawStep (s', e1') event => RawStep (s', Succ e1') event
      | RawStuck => RawStuck
      | RawValue =>
          match e1 with Nat n => RawStep (s, Nat (S n)) None | _ => RawStuck end
      end
  | Iter count step_term seed =>
      match step_raw s count with
      | RawStep (s', count') event =>
          RawStep (s', Iter count' step_term seed) event
      | RawStuck => RawStuck
      | RawValue =>
          match step_raw s step_term with
          | RawStep (s', step_term') event =>
              RawStep (s', Iter count step_term' seed) event
          | RawStuck => RawStuck
          | RawValue =>
              match step_raw s seed with
              | RawStep (s', seed') event =>
                  RawStep (s', Iter count step_term seed') event
              | RawStuck => RawStuck
              | RawValue =>
                  match count, step_term with
                  | Nat 0, Bang _ => RawStep (s, seed) None
                  | Nat (S n), Bang body =>
                      RawStep (s, Iter (Nat n) step_term (App body seed)) None
                  | _, _ => RawStuck
                  end
              end
          end
      end
  | If condition e1 e2 =>
      match step_raw s condition with
      | RawStep (s', condition') event =>
          RawStep (s', If condition' e1 e2) event
      | RawStuck => RawStuck
      | RawValue =>
          match condition with
          | Bool true => RawStep (s, e1) None
          | Bool false => RawStep (s, e2) None
          | _ => RawStuck
          end
      end
  | New e1 =>
      match step_raw s e1 with
      | RawStep (s', e1') event => RawStep (s', New e1') event
      | RawStuck => RawStuck
      | RawValue =>
          let l := fresh s in
          RawStep (store_insert l e1 s, Loc l) (Some (EventAlloc l))
      end
  | Swap e1 e2 =>
      match step_raw s e1 with
      | RawStep (s', e1') event => RawStep (s', Swap e1' e2) event
      | RawStuck => RawStuck
      | RawValue =>
          match step_raw s e2 with
          | RawStep (s', e2') event => RawStep (s', Swap e1 e2') event
          | RawStuck => RawStuck
          | RawValue =>
              match e1 with
              | Loc l =>
                  match natmap_lookup l s with
                  | Some old =>
                      RawStep (store_update l e2 s, Pair old (Loc l))
                        (Some (EventSwap l))
                  | None => RawStuck
                  end
              | _ => RawStuck
              end
          end
      end
  | Free e1 =>
      match step_raw s e1 with
      | RawStep (s', e1') event => RawStep (s', Free e1') event
      | RawStuck => RawStuck
      | RawValue =>
          match e1 with
          | Loc l =>
              match natmap_lookup l s with
              | Some Unit =>
                  RawStep (store_remove l s, Unit) (Some (EventFree l))
              | _ => RawStuck
              end
          | _ => RawStuck
          end
      end
  end.

Definition raw_result_step (result : raw_step_result) : step_result :=
  match result with
  | RawValue => SValue
  | RawStuck => SStuck
  | RawStep c _ => SStep c
  end.

Definition raw_result_event (result : raw_step_result) : option store_event :=
  match result with
  | RawStep _ event => event
  | RawValue | RawStuck => None
  end.

Definition observed_step (c : config) : raw_step_result :=
  step_raw (fst c) (snd c).

Definition step (c : config) : step_result :=
  raw_result_step (observed_step c).

Definition step_event (c : config) : option store_event :=
  raw_result_event (observed_step c).

Definition labelled_step (event : store_event) (c c' : config) : Prop :=
  observed_step c = RawStep c' (Some event).

Definition silent_step (c c' : config) : Prop :=
  observed_step c = RawStep c' None.

Definition event_store_transition
    (event : store_event) (before after : store) : Prop :=
  match event with
  | EventAlloc l =>
      ~ In l (natmap_domain before) /\
      natmap_domain after = l :: natmap_domain before
  | EventSwap l =>
      In l (natmap_domain before) /\
      natmap_domain after = natmap_domain before
  | EventFree l =>
      In l (natmap_domain before) /\
      natmap_domain after =
        filter (fun k => negb (Nat.eqb l k)) (natmap_domain before)
  end.

Inductive run_result : Type :=
  | RValue : config -> run_result
  | RStuck : config -> run_result
  | Timeout : config -> run_result.

(** Values and stuck terms are recognized without spending fuel. One unit of
    fuel is spent only when following an actual small step. *)
Fixpoint runFuel (fuel : nat) (c : config) : run_result :=
  match step c with
  | SValue => RValue c
  | SStuck => RStuck c
  | SStep c' =>
      match fuel with
      | 0 => Timeout c
      | S fuel' => runFuel fuel' c'
      end
  end.

(** A traced run has the same terminal classification as [runFuel] and a
    chronological list of the store events performed before that outcome. *)
Inductive trace_result : Type :=
  | TraceValue : list store_event -> config -> trace_result
  | TraceStuck : list store_event -> config -> trace_result
  | TraceTimeout : list store_event -> config -> trace_result.

Definition trace_result_events (result : trace_result) : list store_event :=
  match result with
  | TraceValue events _ | TraceStuck events _ | TraceTimeout events _ => events
  end.

Definition trace_result_config (result : trace_result) : config :=
  match result with
  | TraceValue _ c | TraceStuck _ c | TraceTimeout _ c => c
  end.

Definition trace_result_run (result : trace_result) : run_result :=
  match result with
  | TraceValue _ c => RValue c
  | TraceStuck _ c => RStuck c
  | TraceTimeout _ c => Timeout c
  end.

Definition trace_prepend (event : store_event) (result : trace_result)
    : trace_result :=
  match result with
  | TraceValue events c => TraceValue (event :: events) c
  | TraceStuck events c => TraceStuck (event :: events) c
  | TraceTimeout events c => TraceTimeout (event :: events) c
  end.

Fixpoint runFuelTrace (fuel : nat) (c : config) : trace_result :=
  match observed_step c with
  | RawValue => TraceValue [] c
  | RawStuck => TraceStuck [] c
  | RawStep c' event =>
      match fuel with
      | 0 => TraceTimeout [] c
      | S fuel' =>
          match event with
          | Some event => trace_prepend event (runFuelTrace fuel' c')
          | None => runFuelTrace fuel' c'
          end
      end
  end.

(** ** Relational semantics *)

Inductive small_step : config -> config -> Prop :=
  | StepAppFun : forall s s' e1 e1' e2,
      small_step (s, e1) (s', e1') ->
      small_step (s, App e1 e2) (s', App e1' e2)
  | StepAppArg : forall s s' v1 e2 e2',
      value v1 -> small_step (s, e2) (s', e2') ->
      small_step (s, App v1 e2) (s', App v1 e2')
  | StepAppBeta : forall s a body v,
      value v ->
      small_step (s, App (Lam a body) v) (s, subst_l v body)
  | StepLetUnit : forall s s' e1 e1' body,
      small_step (s, e1) (s', e1') ->
      small_step (s, LetUnit e1 body) (s', LetUnit e1' body)
  | StepLetUnitBeta : forall s body,
      small_step (s, LetUnit Unit body) (s, body)
  | StepPairLeft : forall s s' e1 e1' e2,
      small_step (s, e1) (s', e1') ->
      small_step (s, Pair e1 e2) (s', Pair e1' e2)
  | StepPairRight : forall s s' v1 e2 e2',
      value v1 -> small_step (s, e2) (s', e2') ->
      small_step (s, Pair v1 e2) (s', Pair v1 e2')
  | StepLetPair : forall s s' e1 e1' body,
      small_step (s, e1) (s', e1') ->
      small_step (s, LetPair e1 body) (s', LetPair e1' body)
  | StepLetPairBeta : forall s v1 v2 body,
      value v1 -> value v2 ->
      small_step (s, LetPair (Pair v1 v2) body)
        (s, subst_l v1 (subst_l v2 body))
  | StepFst : forall s s' e e',
      small_step (s, e) (s', e') -> small_step (s, Fst e) (s', Fst e')
  | StepFstBeta : forall s e1 e2,
      small_step (s, Fst (With e1 e2)) (s, e1)
  | StepSnd : forall s s' e e',
      small_step (s, e) (s', e') -> small_step (s, Snd e) (s', Snd e')
  | StepSndBeta : forall s e1 e2,
      small_step (s, Snd (With e1 e2)) (s, e2)
  | StepLetBang : forall s s' e1 e1' body,
      small_step (s, e1) (s', e1') ->
      small_step (s, LetBang e1 body) (s', LetBang e1' body)
  | StepLetBangBeta : forall s suspended body,
      small_step (s, LetBang (Bang suspended) body) (s, subst_u suspended body)
  | StepSucc : forall s s' e e',
      small_step (s, e) (s', e') -> small_step (s, Succ e) (s', Succ e')
  | StepSuccNat : forall s n,
      small_step (s, Succ (Nat n)) (s, Nat (S n))
  | StepIterCount : forall s s' count count' step_term seed,
      small_step (s, count) (s', count') ->
      small_step (s, Iter count step_term seed) (s', Iter count' step_term seed)
  | StepIterStep : forall s s' count step_term step_term' seed,
      value count -> small_step (s, step_term) (s', step_term') ->
      small_step (s, Iter count step_term seed) (s', Iter count step_term' seed)
  | StepIterSeed : forall s s' count step_term seed seed',
      value count -> value step_term -> small_step (s, seed) (s', seed') ->
      small_step (s, Iter count step_term seed) (s', Iter count step_term seed')
  | StepIterZero : forall s body seed,
      value seed -> small_step (s, Iter (Nat 0) (Bang body) seed) (s, seed)
  | StepIterSucc : forall s n body seed,
      value seed ->
      small_step (s, Iter (Nat (S n)) (Bang body) seed)
        (s, Iter (Nat n) (Bang body) (App body seed))
  | StepIf : forall s s' condition condition' e1 e2,
      small_step (s, condition) (s', condition') ->
      small_step (s, If condition e1 e2) (s', If condition' e1 e2)
  | StepIfTrue : forall s e1 e2,
      small_step (s, If (Bool true) e1 e2) (s, e1)
  | StepIfFalse : forall s e1 e2,
      small_step (s, If (Bool false) e1 e2) (s, e2)
  | StepNew : forall s s' e e',
      small_step (s, e) (s', e') -> small_step (s, New e) (s', New e')
  | StepNewValue : forall s v,
      value v ->
      small_step (s, New v)
        (store_insert (fresh s) v s, Loc (fresh s))
  | StepSwapLeft : forall s s' e1 e1' e2,
      small_step (s, e1) (s', e1') ->
      small_step (s, Swap e1 e2) (s', Swap e1' e2)
  | StepSwapRight : forall s s' v1 e2 e2',
      value v1 -> small_step (s, e2) (s', e2') ->
      small_step (s, Swap v1 e2) (s', Swap v1 e2')
  | StepSwapValue : forall s l v old,
      value v -> In_opt old (natmap_lookup l s) ->
      small_step (s, Swap (Loc l) v)
        (store_update l v s, Pair old (Loc l))
  | StepFree : forall s s' e e',
      small_step (s, e) (s', e') -> small_step (s, Free e) (s', Free e')
  | StepFreeLoc : forall s l,
      In_opt Unit (natmap_lookup l s) ->
      small_step (s, Free (Loc l)) (store_remove l s, Unit).

Inductive reaches : config -> config -> Prop :=
  | ReachesRefl : forall c, reaches c c
  | ReachesStep : forall c1 c2 c3,
      small_step c1 c2 -> reaches c2 c3 -> reaches c1 c3.

Inductive pure_redex : term -> term -> Prop :=
  | PureAppBeta : forall a body v,
      value v -> pure_redex (App (Lam a body) v) (subst_l v body)
  | PureLetUnit : forall body, pure_redex (LetUnit Unit body) body
  | PureLetPair : forall v1 v2 body,
      value v1 -> value v2 ->
      pure_redex (LetPair (Pair v1 v2) body)
        (subst_l v1 (subst_l v2 body))
  | PureFst : forall e1 e2, pure_redex (Fst (With e1 e2)) e1
  | PureSnd : forall e1 e2, pure_redex (Snd (With e1 e2)) e2
  | PureLetBang : forall suspended body,
      pure_redex (LetBang (Bang suspended) body) (subst_u suspended body)
  | PureSucc : forall n, pure_redex (Succ (Nat n)) (Nat (S n))
  | PureIterZero : forall body seed,
      value seed -> pure_redex (Iter (Nat 0) (Bang body) seed) seed
  | PureIterSucc : forall n body seed,
      value seed ->
      pure_redex (Iter (Nat (S n)) (Bang body) seed)
        (Iter (Nat n) (Bang body) (App body seed))
  | PureIfTrue : forall e1 e2, pure_redex (If (Bool true) e1 e2) e1
  | PureIfFalse : forall e1 e2, pure_redex (If (Bool false) e1 e2) e2.

Inductive head_step : config -> option store_event -> config -> Prop :=
  | HeadPure : forall s e e',
      pure_redex e e' -> head_step (s, e) None (s, e')
  | HeadNew : forall s v,
      value v ->
      head_step (s, New v) (Some (EventAlloc (fresh s)))
        (store_insert (fresh s) v s, Loc (fresh s))
  | HeadSwap : forall s l v old,
      value v -> In_opt old (natmap_lookup l s) ->
      head_step (s, Swap (Loc l) v) (Some (EventSwap l))
        (store_update l v s, Pair old (Loc l))
  | HeadFree : forall s l,
      In_opt Unit (natmap_lookup l s) ->
      head_step (s, Free (Loc l)) (Some (EventFree l))
        (store_remove l s, Unit).

Lemma pure_redex_small_step : forall s e e',
  pure_redex e e' -> small_step (s, e) (s, e').
Proof. intros s e e' Hred. destruct Hred; eauto using small_step. Qed.

Lemma head_step_small_step : forall c event c',
  head_step c event c' -> small_step c c'.
Proof.
  intros c event c' Hhead. destruct Hhead.
  - eapply pure_redex_small_step. exact H.
  - constructor. exact H.
  - econstructor; eassumption.
  - constructor. exact H.
Qed.

Lemma head_step_store_effect : forall s e event s' e',
  head_step (s, e) event (s', e') ->
  match event with
  | None => s' = s
  | Some store_event => event_store_transition store_event s s'
  end.
Proof.
  intros s e event s' e' Hhead. inversion Hhead; subst; simpl.
  - reflexivity.
  - split.
    + apply fresh_not_allocated.
    + exact (store_insert_domain (fresh s) Unit s).
  - split.
    + match goal with
      | Hlookup : In_opt _ (natmap_lookup _ _) |- _ =>
          eapply natmap_lookup_in in Hlookup;
          apply (in_map fst) in Hlookup; exact Hlookup
      end.
    + exact (store_update_domain l v s).
  - split.
    + match goal with
      | Hlookup : In_opt _ (natmap_lookup _ _) |- _ =>
          eapply natmap_lookup_in in Hlookup;
          apply (in_map fst) in Hlookup; exact Hlookup
      end.
    + eapply store_remove_domain.
Qed.

Inductive eval_context : Type :=
  | ECHole : eval_context
  | ECAppFun : eval_context -> term -> eval_context
  | ECAppArg : term -> eval_context -> eval_context
  | ECLetUnit : eval_context -> term -> eval_context
  | ECPairLeft : eval_context -> term -> eval_context
  | ECPairRight : term -> eval_context -> eval_context
  | ECLetPair : eval_context -> term -> eval_context
  | ECFst : eval_context -> eval_context
  | ECSnd : eval_context -> eval_context
  | ECLetBang : eval_context -> term -> eval_context
  | ECSucc : eval_context -> eval_context
  | ECIterCount : eval_context -> term -> term -> eval_context
  | ECIterStep : term -> eval_context -> term -> eval_context
  | ECIterSeed : term -> term -> eval_context -> eval_context
  | ECIf : eval_context -> term -> term -> eval_context
  | ECNew : eval_context -> eval_context
  | ECSwapLeft : eval_context -> term -> eval_context
  | ECSwapRight : term -> eval_context -> eval_context
  | ECFree : eval_context -> eval_context.

Fixpoint plug (K : eval_context) (e : term) : term :=
  match K with
  | ECHole => e
  | ECAppFun K e2 => App (plug K e) e2
  | ECAppArg v1 K => App v1 (plug K e)
  | ECLetUnit K body => LetUnit (plug K e) body
  | ECPairLeft K e2 => Pair (plug K e) e2
  | ECPairRight v1 K => Pair v1 (plug K e)
  | ECLetPair K body => LetPair (plug K e) body
  | ECFst K => Fst (plug K e)
  | ECSnd K => Snd (plug K e)
  | ECLetBang K body => LetBang (plug K e) body
  | ECSucc K => Succ (plug K e)
  | ECIterCount K step_term seed => Iter (plug K e) step_term seed
  | ECIterStep count K seed => Iter count (plug K e) seed
  | ECIterSeed count step_term K => Iter count step_term (plug K e)
  | ECIf K e1 e2 => If (plug K e) e1 e2
  | ECNew K => New (plug K e)
  | ECSwapLeft K e2 => Swap (plug K e) e2
  | ECSwapRight v1 K => Swap v1 (plug K e)
  | ECFree K => Free (plug K e)
  end.

Inductive cbv_context : eval_context -> Prop :=
  | CBVHole : cbv_context ECHole
  | CBVAppFun : forall K e2,
      cbv_context K -> cbv_context (ECAppFun K e2)
  | CBVAppArg : forall v1 K,
      value v1 -> cbv_context K -> cbv_context (ECAppArg v1 K)
  | CBVLetUnit : forall K body,
      cbv_context K -> cbv_context (ECLetUnit K body)
  | CBVPairLeft : forall K e2,
      cbv_context K -> cbv_context (ECPairLeft K e2)
  | CBVPairRight : forall v1 K,
      value v1 -> cbv_context K -> cbv_context (ECPairRight v1 K)
  | CBVLetPair : forall K body,
      cbv_context K -> cbv_context (ECLetPair K body)
  | CBVFst : forall K, cbv_context K -> cbv_context (ECFst K)
  | CBVSnd : forall K, cbv_context K -> cbv_context (ECSnd K)
  | CBVLetBang : forall K body,
      cbv_context K -> cbv_context (ECLetBang K body)
  | CBVSucc : forall K, cbv_context K -> cbv_context (ECSucc K)
  | CBVIterCount : forall K step_term seed,
      cbv_context K -> cbv_context (ECIterCount K step_term seed)
  | CBVIterStep : forall count K seed,
      value count -> cbv_context K -> cbv_context (ECIterStep count K seed)
  | CBVIterSeed : forall count step_term K,
      value count -> value step_term -> cbv_context K ->
      cbv_context (ECIterSeed count step_term K)
  | CBVIf : forall K e1 e2,
      cbv_context K -> cbv_context (ECIf K e1 e2)
  | CBVNew : forall K, cbv_context K -> cbv_context (ECNew K)
  | CBVSwapLeft : forall K e2,
      cbv_context K -> cbv_context (ECSwapLeft K e2)
  | CBVSwapRight : forall v1 K,
      value v1 -> cbv_context K -> cbv_context (ECSwapRight v1 K)
  | CBVFree : forall K, cbv_context K -> cbv_context (ECFree K).

Theorem small_step_under_context : forall K s e s' e',
  cbv_context K -> small_step (s, e) (s', e') ->
  small_step (s, plug K e) (s', plug K e').
Proof.
  intros K s e s' e' Hcontext. induction Hcontext; intros Hstep; simpl;
    eauto using small_step.
Qed.

(** ** Values and the executable classifier *)

Lemma step_raw_value : forall s e,
  value e -> step_raw s e = RawValue.
Proof.
  intros s e Hvalue. induction Hvalue; cbn; try reflexivity.
  rewrite IHHvalue1, IHHvalue2. reflexivity.
Qed.

Lemma step_raw_value_inv : forall s e,
  step_raw s e = RawValue -> value e.
Proof.
  intros s e. revert s. induction e; intros s Hstep; cbn in Hstep.
  - discriminate.
  - discriminate.
  - constructor.
  - constructor.
  - destruct (step_raw s e1) as [| | [s1 e1'] event1] eqn:E1;
      try discriminate.
    destruct (step_raw s e2) as [| | [s2 e2'] event2] eqn:E2;
      try discriminate.
    destruct e1; inversion Hstep.
  - constructor.
  - destruct (step_raw s e1) as [| | [s1 e1'] event1] eqn:E1;
      try discriminate.
    destruct e1; discriminate.
  - destruct (step_raw s e1) as [| | [s1 e1'] event1] eqn:E1;
      try discriminate.
    destruct (step_raw s e2) as [| | [s2 e2'] event2] eqn:E2;
      try discriminate.
    constructor.
    + apply IHe1 with s. exact E1.
    + apply IHe2 with s. exact E2.
  - destruct (step_raw s e1) as [| | [s1 e1'] event1] eqn:E1;
      try discriminate.
    destruct e1; discriminate.
  - constructor.
  - destruct (step_raw s e) as [| | [s' e'] event] eqn:E; try discriminate.
    destruct e; discriminate.
  - destruct (step_raw s e) as [| | [s' e'] event] eqn:E; try discriminate.
    destruct e; discriminate.
  - constructor.
  - destruct (step_raw s e1) as [| | [s1 e1'] event1] eqn:E1;
      try discriminate.
    destruct e1; discriminate.
  - constructor.
  - destruct (step_raw s e) as [| | [s' e'] event] eqn:E; try discriminate.
    destruct e; discriminate.
  - destruct (step_raw s e1) as [| | [s1 e1'] event1] eqn:E1;
      try discriminate.
    destruct (step_raw s e2) as [| | [s2 e2'] event2] eqn:E2;
      try discriminate.
    destruct (step_raw s e3) as [| | [s3 e3'] event3] eqn:E3;
      try discriminate.
    destruct e1; destruct e2; try discriminate.
    all: destruct n; discriminate.
  - constructor.
  - destruct (step_raw s e1) as [| | [s1 e1'] event1] eqn:E1;
      try discriminate.
    destruct e1; try discriminate.
    destruct b; discriminate.
  - destruct (step_raw s e) as [| | [s' e'] event] eqn:E; discriminate.
  - destruct (step_raw s e1) as [| | [s1 e1'] event1] eqn:E1;
      try discriminate.
    destruct (step_raw s e2) as [| | [s2 e2'] event2] eqn:E2;
      try discriminate.
    destruct e1; try discriminate.
    destruct (natmap_lookup n s); discriminate.
  - destruct (step_raw s e) as [| | [s' e'] event] eqn:E; try discriminate.
    destruct e; try discriminate.
    destruct (natmap_lookup n s) as [stored |]; try discriminate.
    destruct stored; discriminate.
Qed.

Theorem step_value : forall c,
  step c = SValue <-> value (snd c).
Proof.
  intros [s e]. unfold step, observed_step. cbn [fst snd] in *.
  split; intros H.
  - destruct (step_raw s e) as [| | next event] eqn:Hraw;
      try discriminate.
    eapply step_raw_value_inv. exact Hraw.
  - rewrite (step_raw_value s e H). reflexivity.
Qed.

(** ** Correspondence between the function and the relation *)

Lemma step_raw_complete : forall c c',
  small_step c c' ->
  exists event, step_raw (fst c) (snd c) = RawStep c' event.
Proof.
  intros c c' Hstep. induction Hstep; cbn in *.
  - destruct IHHstep as [event ->]. exists event. reflexivity.
  - destruct IHHstep as [event ->]. rewrite (step_raw_value s v1 H).
    exists event. reflexivity.
  - rewrite (step_raw_value s v H). exists None. reflexivity.
  - destruct IHHstep as [event ->]. exists event. reflexivity.
  - exists None. reflexivity.
  - destruct IHHstep as [event ->]. exists event. reflexivity.
  - destruct IHHstep as [event ->]. rewrite (step_raw_value s v1 H).
    exists event. reflexivity.
  - destruct IHHstep as [event ->]. exists event. reflexivity.
  - rewrite (step_raw_value s v1 H), (step_raw_value s v2 H0).
    exists None. reflexivity.
  - destruct IHHstep as [event ->]. exists event. reflexivity.
  - exists None. reflexivity.
  - destruct IHHstep as [event ->]. exists event. reflexivity.
  - exists None. reflexivity.
  - destruct IHHstep as [event ->]. exists event. reflexivity.
  - exists None. reflexivity.
  - destruct IHHstep as [event ->]. exists event. reflexivity.
  - exists None. reflexivity.
  - destruct IHHstep as [event ->]. exists event. reflexivity.
  - destruct IHHstep as [event ->]. rewrite (step_raw_value s count H).
    exists event. reflexivity.
  - destruct IHHstep as [event ->].
    rewrite (step_raw_value s count H), (step_raw_value s step_term H0).
    exists event. reflexivity.
  - rewrite (step_raw_value s seed H). exists None. reflexivity.
  - rewrite (step_raw_value s seed H). exists None. reflexivity.
  - destruct IHHstep as [event ->]. exists event. reflexivity.
  - exists None. reflexivity.
  - exists None. reflexivity.
  - destruct IHHstep as [event ->]. exists event. reflexivity.
  - rewrite (step_raw_value s v H). exists (Some (EventAlloc (fresh s))).
    reflexivity.
  - destruct IHHstep as [event ->]. exists event. reflexivity.
  - destruct IHHstep as [event ->]. rewrite (step_raw_value s v1 H).
    exists event. reflexivity.
  - rewrite (step_raw_value s v H), (In_opt_Some H0).
    exists (Some (EventSwap l)). reflexivity.
  - destruct IHHstep as [event ->]. exists event. reflexivity.
  - rewrite (In_opt_Some H). exists (Some (EventFree l)). reflexivity.
Qed.

Theorem step_complete : forall c c',
  small_step c c' -> step c = SStep c'.
Proof.
  intros c c' Hstep. unfold step, observed_step.
  destruct (step_raw_complete c c' Hstep) as [event ->]. reflexivity.
Qed.

(** The executable worker exposes exactly one CBV context around a labelled
    head reduction. This is the sole structural analysis of a successful
    [step_raw] call; soundness and store-effect facts are projections of it. *)
Lemma step_raw_decompose : forall s e c' event,
  step_raw s e = RawStep c' event ->
  exists K redex reduct,
    e = plug K redex /\ snd c' = plug K reduct /\ cbv_context K /\
    head_step (s, redex) event (fst c', reduct).
Proof.
  intros s e. revert s. induction e; intros s [s' e'] event Hresult;
    cbn in Hresult; try discriminate.
  - destruct (step_raw s e1) as [| | [s1 e1'] event1] eqn:E1.
    + destruct (step_raw s e2) as [| | [s2 e2'] event2] eqn:E2.
      * pose proof (step_raw_value_inv s e2 E2) as Hvalue2.
        destruct e1; cbn in Hresult; try discriminate.
        inversion Hresult; subst.
        eexists ECHole, _, _. cbn.
        repeat split; eauto using cbv_context, head_step, pure_redex.
      * discriminate.
      * destruct (IHe2 s (s2, e2') event2 E2) as
          [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
        inversion Hresult; subst.
        exists (ECAppArg e1 K), redex, reduct. cbn.
        repeat split; try (now rewrite Hredex);
          try (cbn in Hreduct; now rewrite Hreduct).
        -- constructor; [eapply step_raw_value_inv; exact E1 | exact Hcontext].
        -- exact Hhead.
    + discriminate.
    + destruct (IHe1 s (s1, e1') event1 E1) as
        [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
      inversion Hresult; subst.
      exists (ECAppFun K e2), redex, reduct. cbn.
      repeat split; try (now rewrite Hredex);
        try (cbn in Hreduct; now rewrite Hreduct).
      * constructor. exact Hcontext.
      * exact Hhead.
  - destruct (step_raw s e1) as [| | [s1 e1'] event1] eqn:E1.
    + destruct e1; cbn in Hresult; try discriminate.
      inversion Hresult; subst.
      eexists ECHole, _, _. cbn.
      repeat split; eauto using cbv_context, head_step, pure_redex.
    + discriminate.
    + destruct (IHe1 s (s1, e1') event1 E1) as
        [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
      inversion Hresult; subst.
      exists (ECLetUnit K e2), redex, reduct. cbn.
      repeat split; try (now rewrite Hredex);
        try (cbn in Hreduct; now rewrite Hreduct).
      * constructor. exact Hcontext.
      * exact Hhead.
  - destruct (step_raw s e1) as [| | [s1 e1'] event1] eqn:E1.
    + destruct (step_raw s e2) as [| | [s2 e2'] event2] eqn:E2;
        try discriminate.
      destruct (IHe2 s (s2, e2') event2 E2) as
        [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
      inversion Hresult; subst.
      exists (ECPairRight e1 K), redex, reduct. cbn.
      repeat split; try (now rewrite Hredex);
        try (cbn in Hreduct; now rewrite Hreduct).
      * constructor; [eapply step_raw_value_inv; exact E1 | exact Hcontext].
      * exact Hhead.
    + discriminate.
    + destruct (IHe1 s (s1, e1') event1 E1) as
        [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
      inversion Hresult; subst.
      exists (ECPairLeft K e2), redex, reduct. cbn.
      repeat split; try (now rewrite Hredex);
        try (cbn in Hreduct; now rewrite Hreduct).
      * constructor. exact Hcontext.
      * exact Hhead.
  - destruct (step_raw s e1) as [| | [s1 e1'] event1] eqn:E1.
    + pose proof (step_raw_value_inv s e1 E1) as Hpair.
      destruct e1; cbn in Hresult; try discriminate.
      inversion Hresult; subst.
      inversion Hpair; subst.
      eexists ECHole, _, _. cbn.
      repeat split; eauto using cbv_context, head_step, pure_redex.
    + discriminate.
    + destruct (IHe1 s (s1, e1') event1 E1) as
        [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
      inversion Hresult; subst.
      exists (ECLetPair K e2), redex, reduct. cbn.
      repeat split; try (now rewrite Hredex);
        try (cbn in Hreduct; now rewrite Hreduct).
      * constructor. exact Hcontext.
      * exact Hhead.
  - destruct (step_raw s e) as [| | [s1 e1'] child_event] eqn:E.
    + destruct e; cbn in Hresult; try discriminate.
      inversion Hresult; subst.
      eexists ECHole, _, _. cbn.
      repeat split; eauto using cbv_context, head_step, pure_redex.
    + discriminate.
    + destruct (IHe s (s1, e1') child_event E) as
        [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
      inversion Hresult; subst.
      exists (ECFst K), redex, reduct. cbn.
      repeat split; try (now rewrite Hredex);
        try (cbn in Hreduct; now rewrite Hreduct).
      * constructor. exact Hcontext.
      * exact Hhead.
  - destruct (step_raw s e) as [| | [s1 e1'] child_event] eqn:E.
    + destruct e; cbn in Hresult; try discriminate.
      inversion Hresult; subst.
      eexists ECHole, _, _. cbn.
      repeat split; eauto using cbv_context, head_step, pure_redex.
    + discriminate.
    + destruct (IHe s (s1, e1') child_event E) as
        [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
      inversion Hresult; subst.
      exists (ECSnd K), redex, reduct. cbn.
      repeat split; try (now rewrite Hredex);
        try (cbn in Hreduct; now rewrite Hreduct).
      * constructor. exact Hcontext.
      * exact Hhead.
  - destruct (step_raw s e1) as [| | [s1 e1'] event1] eqn:E1.
    + destruct e1; cbn in Hresult; try discriminate.
      inversion Hresult; subst.
      eexists ECHole, _, _. cbn.
      repeat split; eauto using cbv_context, head_step, pure_redex.
    + discriminate.
    + destruct (IHe1 s (s1, e1') event1 E1) as
        [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
      inversion Hresult; subst.
      exists (ECLetBang K e2), redex, reduct. cbn.
      repeat split; try (now rewrite Hredex);
        try (cbn in Hreduct; now rewrite Hreduct).
      * constructor. exact Hcontext.
      * exact Hhead.
  - destruct (step_raw s e) as [| | [s1 e1'] child_event] eqn:E.
    + destruct e; cbn in Hresult; try discriminate.
      inversion Hresult; subst.
      eexists ECHole, _, _. cbn.
      repeat split; eauto using cbv_context, head_step, pure_redex.
    + discriminate.
    + destruct (IHe s (s1, e1') child_event E) as
        [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
      inversion Hresult; subst.
      exists (ECSucc K), redex, reduct. cbn.
      repeat split; try (now rewrite Hredex);
        try (cbn in Hreduct; now rewrite Hreduct).
      * constructor. exact Hcontext.
      * exact Hhead.
  - destruct (step_raw s e1) as [| | [s1 e1'] event1] eqn:E1.
    + destruct (step_raw s e2) as [| | [s2 e2'] event2] eqn:E2.
      * destruct (step_raw s e3) as [| | [s3 e3'] event3] eqn:E3.
        -- pose proof (step_raw_value_inv s e3 E3) as Hseed.
           destruct e1; try discriminate. destruct n; destruct e2;
             cbn in Hresult; try discriminate; inversion Hresult; subst;
             eexists ECHole, _, _; cbn;
             repeat split; eauto using cbv_context, head_step, pure_redex.
        -- discriminate.
        -- destruct (IHe3 s (s3, e3') event3 E3) as
             [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
           inversion Hresult; subst.
           exists (ECIterSeed e1 e2 K), redex, reduct. cbn.
           repeat split; try (now rewrite Hredex);
             try (cbn in Hreduct; now rewrite Hreduct).
           ++ constructor.
              ** eapply step_raw_value_inv. exact E1.
              ** eapply step_raw_value_inv. exact E2.
              ** exact Hcontext.
           ++ exact Hhead.
      * discriminate.
      * destruct (IHe2 s (s2, e2') event2 E2) as
          [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
        inversion Hresult; subst.
        exists (ECIterStep e1 K e3), redex, reduct. cbn.
        repeat split; try (now rewrite Hredex);
          try (cbn in Hreduct; now rewrite Hreduct).
        -- constructor; [eapply step_raw_value_inv; exact E1 | exact Hcontext].
        -- exact Hhead.
    + discriminate.
    + destruct (IHe1 s (s1, e1') event1 E1) as
        [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
      inversion Hresult; subst.
      exists (ECIterCount K e2 e3), redex, reduct. cbn.
      repeat split; try (now rewrite Hredex);
        try (cbn in Hreduct; now rewrite Hreduct).
      * constructor. exact Hcontext.
      * exact Hhead.
  - destruct (step_raw s e1) as [| | [s1 e1'] event1] eqn:E1.
    + destruct e1; try discriminate. destruct b; cbn in Hresult;
        inversion Hresult; subst;
        eexists ECHole, _, _; cbn;
        repeat split; eauto using cbv_context, head_step, pure_redex.
    + discriminate.
    + destruct (IHe1 s (s1, e1') event1 E1) as
        [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
      inversion Hresult; subst.
      exists (ECIf K e2 e3), redex, reduct. cbn.
      repeat split; try (now rewrite Hredex);
        try (cbn in Hreduct; now rewrite Hreduct).
      * constructor. exact Hcontext.
      * exact Hhead.
  - destruct (step_raw s e) as [| | [s1 e1'] child_event] eqn:E.
    + pose proof (step_raw_value_inv s e E) as Hvalue.
      inversion Hresult; subst.
      eexists ECHole, _, _. cbn.
      repeat split; eauto using cbv_context, head_step.
    + discriminate.
    + destruct (IHe s (s1, e1') child_event E) as
        [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
      inversion Hresult; subst.
      exists (ECNew K), redex, reduct. cbn.
      repeat split; try (now rewrite Hredex);
        try (cbn in Hreduct; now rewrite Hreduct).
      * constructor. exact Hcontext.
      * exact Hhead.
  - destruct (step_raw s e1) as [| | [s1 e1'] event1] eqn:E1.
    + destruct (step_raw s e2) as [| | [s2 e2'] event2] eqn:E2.
      * pose proof (step_raw_value_inv s e2 E2) as Hvalue2.
        destruct e1; cbn in Hresult; try discriminate.
        destruct (natmap_lookup n s) as [old |] eqn:Elookup;
          cbn in Hresult; try discriminate.
        inversion Hresult; subst.
        eexists ECHole, _, _. cbn.
        repeat split; eauto using cbv_context, head_step, Some_In_opt.
      * discriminate.
      * destruct (IHe2 s (s2, e2') event2 E2) as
          [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
        inversion Hresult; subst.
        exists (ECSwapRight e1 K), redex, reduct. cbn.
        repeat split; try (now rewrite Hredex);
          try (cbn in Hreduct; now rewrite Hreduct).
        -- constructor; [eapply step_raw_value_inv; exact E1 | exact Hcontext].
        -- exact Hhead.
    + discriminate.
    + destruct (IHe1 s (s1, e1') event1 E1) as
        [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
      inversion Hresult; subst.
      exists (ECSwapLeft K e2), redex, reduct. cbn.
      repeat split; try (now rewrite Hredex);
        try (cbn in Hreduct; now rewrite Hreduct).
      * constructor. exact Hcontext.
      * exact Hhead.
  - destruct (step_raw s e) as [| | [s1 e1'] child_event] eqn:E.
    + destruct e; cbn in Hresult; try discriminate.
      destruct (natmap_lookup n s) as [stored |] eqn:Elookup;
        cbn in Hresult; try discriminate.
      destruct stored; cbn in Hresult; try discriminate.
      inversion Hresult; subst.
      eexists ECHole, _, _. cbn.
      repeat split; eauto using cbv_context, head_step, Some_In_opt.
    + discriminate.
    + destruct (IHe s (s1, e1') child_event E) as
        [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
      inversion Hresult; subst.
      exists (ECFree K), redex, reduct. cbn.
      repeat split; try (now rewrite Hredex);
        try (cbn in Hreduct; now rewrite Hreduct).
      * constructor. exact Hcontext.
      * exact Hhead.
Qed.

Lemma step_raw_sound : forall s e c' event,
  step_raw s e = RawStep c' event -> small_step (s, e) c'.
Proof.
  intros s e [s' e'] event Hstep.
  destruct (step_raw_decompose s e (s', e') event Hstep) as
    [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
  cbn [fst snd] in Hreduct, Hhead.
  subst e. rewrite Hreduct.
  eapply small_step_under_context; [exact Hcontext | ].
  eapply head_step_small_step. exact Hhead.
Qed.

(** A relational step is exactly a CBV evaluation context surrounding one
    optionally labelled head reduction. *)
Theorem small_step_decompose : forall s e s' e',
  small_step (s, e) (s', e') <->
  exists K redex reduct event,
    e = plug K redex /\ e' = plug K reduct /\ cbv_context K /\
    head_step (s, redex) event (s', reduct).
Proof.
  intros s e s' e'. split.
  - intros Hstep.
    destruct (step_raw_complete (s, e) (s', e') Hstep) as [event Hraw].
    destruct (step_raw_decompose s e (s', e') event Hraw) as
      [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
    cbn [fst snd] in Hreduct, Hhead.
    exists K, redex, reduct, event.
    repeat split; assumption.
  - intros [K [redex [reduct [event [-> [-> [Hcontext Hhead]]]]]]].
    eapply small_step_under_context; [exact Hcontext | ].
    eapply head_step_small_step. exact Hhead.
Qed.

Theorem step_sound : forall c c',
  step c = SStep c' -> small_step c c'.
Proof.
  intros [s e] c' Hstep. unfold step, observed_step in Hstep.
  cbn [fst snd] in Hstep.
  destruct (step_raw s e) as [| | next event] eqn:Hraw; try discriminate.
  inversion Hstep; subst. eapply step_raw_sound. exact Hraw.
Qed.


(** Every executable step carries the store effect of its focused head
    reduction. Evaluation contexts do not inspect or change the store. *)
Lemma step_raw_store_effect : forall s e c' event,
  step_raw s e = RawStep c' event ->
  match event with
  | None => fst c' = s
  | Some store_event => event_store_transition store_event s (fst c')
  end.
Proof.
  intros s e [s' e'] event Hstep.
  destruct (step_raw_decompose s e (s', e') event Hstep) as
    [K [redex [reduct [Hredex [Hreduct [Hcontext Hhead]]]]]].
  cbn [fst snd] in Hhead |- *.
  eapply head_step_store_effect. exact Hhead.
Qed.

Theorem labelled_step_store_transition : forall event s e s' e',
  labelled_step event (s, e) (s', e') ->
  event_store_transition event s s'.
Proof.
  intros event s e s' e' Hstep.
  exact (step_raw_store_effect s e (s', e') (Some event) Hstep).
Qed.

Corollary silent_step_store_unchanged : forall s e s' e',
  silent_step (s, e) (s', e') -> s' = s.
Proof.
  intros s e s' e' Hstep.
  exact (step_raw_store_effect s e (s', e') None Hstep).
Qed.

Corollary step_value_iff : forall c,
  step c = SValue <-> value (snd c).
Proof. apply step_value. Qed.

Theorem step_stuck_iff : forall c,
  step c = SStuck <->
    ~ value (snd c) /\ forall c', ~ small_step c c'.
Proof.
  intros c. split.
  - intros Hstuck. split.
    + intros Hvalue.
      pose proof (proj2 (step_value c) Hvalue) as Hvalue_step.
      rewrite Hstuck in Hvalue_step. discriminate.
    + intros c' Hsmall.
      pose proof (step_complete c c' Hsmall) as Hcomplete.
      rewrite Hstuck in Hcomplete. discriminate.
  - intros [Hnot_value Hnormal]. destruct (step c) as [| | c'] eqn:Hstep.
    + exfalso. apply Hnot_value. apply (proj1 (step_value c)). exact Hstep.
    + reflexivity.
    + exfalso. apply (Hnormal c'). apply step_sound. exact Hstep.
Qed.

Corollary small_step_deterministic : forall c c1 c2,
  small_step c c1 -> small_step c c2 -> c1 = c2.
Proof.
  intros c c1 c2 H1 H2.
  pose proof (step_complete c c1 H1) as E1.
  pose proof (step_complete c c2 H2) as E2.
  rewrite E1 in E2. inversion E2. reflexivity.
Qed.

(** Event traces erase silent reductions while retaining their reachability. *)
Inductive event_trace : config -> list store_event -> config -> Prop :=
  | EventTraceRefl : forall c, event_trace c [] c
  | EventTraceSilent : forall c1 c2 c3 events,
      silent_step c1 c2 -> event_trace c2 events c3 ->
      event_trace c1 events c3
  | EventTraceEvent : forall c1 c2 c3 event events,
      labelled_step event c1 c2 -> event_trace c2 events c3 ->
      event_trace c1 (event :: events) c3.

Lemma labelled_step_sound : forall event c c',
  labelled_step event c c' -> small_step c c'.
Proof.
  intros event [s e] [s' e'] Hstep.
  unfold labelled_step, observed_step in Hstep. cbn [fst snd] in Hstep.
  eapply step_raw_sound. exact Hstep.
Qed.

Lemma silent_step_sound : forall c c',
  silent_step c c' -> small_step c c'.
Proof.
  intros [s e] [s' e'] Hstep.
  unfold silent_step, observed_step in Hstep. cbn [fst snd] in Hstep.
  eapply step_raw_sound. exact Hstep.
Qed.

Lemma small_step_observed : forall c c',
  small_step c c' ->
  (exists event, labelled_step event c c') \/ silent_step c c'.
Proof.
  intros c c' Hsmall.
  destruct (step_raw_complete c c' Hsmall) as [event Hstep].
  destruct event as [event |].
  - left. exists event. exact Hstep.
  - right. exact Hstep.
Qed.

Lemma event_trace_reaches : forall c events c',
  event_trace c events c' -> reaches c c'.
Proof.
  intros c events c' Htrace. induction Htrace.
  - constructor.
  - eapply ReachesStep.
    + eapply silent_step_sound. exact H.
    + exact IHHtrace.
  - eapply ReachesStep.
    + eapply labelled_step_sound. exact H.
    + exact IHHtrace.
Qed.

(** ** Fuelled execution *)

Definition run_result_config (result : run_result) : config :=
  match result with
  | RValue c | RStuck c | Timeout c => c
  end.

Lemma runFuel_reachable : forall fuel c,
  reaches c (run_result_config (runFuel fuel c)).
Proof.
  induction fuel as [| fuel IH]; intros c; cbn [runFuel].
  - destruct (step c) as [| | c'] eqn:Hstep; apply ReachesRefl.
  - destruct (step c) as [| | c'] eqn:Hstep.
    + apply ReachesRefl.
    + apply ReachesRefl.
    + eapply ReachesStep.
      * apply step_sound. exact Hstep.
      * apply IH.
Qed.

Lemma runFuel_value_final : forall fuel c c',
  runFuel fuel c = RValue c' -> step c' = SValue.
Proof.
  induction fuel as [| fuel IH]; intros c c' Hrun; cbn [runFuel] in Hrun.
  - destruct (step c) as [| | next] eqn:Hstep; try discriminate.
    inversion Hrun; subst. exact Hstep.
  - destruct (step c) as [| | next] eqn:Hstep; try discriminate.
    + inversion Hrun; subst. exact Hstep.
    + apply IH with next. exact Hrun.
Qed.

Lemma runFuel_stuck_final : forall fuel c c',
  runFuel fuel c = RStuck c' -> step c' = SStuck.
Proof.
  induction fuel as [| fuel IH]; intros c c' Hrun; cbn [runFuel] in Hrun.
  - destruct (step c) as [| | next] eqn:Hstep; try discriminate.
    inversion Hrun; subst. exact Hstep.
  - destruct (step c) as [| | next] eqn:Hstep; try discriminate.
    + inversion Hrun; subst. exact Hstep.
    + apply IH with next. exact Hrun.
Qed.

Lemma runFuel_timeout_final : forall fuel c c',
  runFuel fuel c = Timeout c' -> exists next, step c' = SStep next.
Proof.
  induction fuel as [| fuel IH]; intros c c' Hrun; cbn [runFuel] in Hrun.
  - destruct (step c) as [| | next] eqn:Hstep; try discriminate.
    inversion Hrun; subst. exists next. exact Hstep.
  - destruct (step c) as [| | next] eqn:Hstep; try discriminate.
    apply IH with next. exact Hrun.
Qed.

Theorem runFuel_value_sound : forall fuel c c',
  runFuel fuel c = RValue c' -> reaches c c' /\ value (snd c').
Proof.
  intros fuel c c' Hrun. split.
  - pose proof (runFuel_reachable fuel c) as Hreach.
    rewrite Hrun in Hreach. exact Hreach.
  - apply (proj1 (step_value c')).
    apply runFuel_value_final with fuel c. exact Hrun.
Qed.

Theorem runFuel_stuck_sound : forall fuel c c',
  runFuel fuel c = RStuck c' ->
  reaches c c' /\ ~ value (snd c') /\ forall next, ~ small_step c' next.
Proof.
  intros fuel c c' Hrun.
  pose proof (runFuel_stuck_final fuel c c' Hrun) as Hstuck.
  split.
  - pose proof (runFuel_reachable fuel c) as Hreach.
    rewrite Hrun in Hreach. exact Hreach.
  - apply (proj1 (step_stuck_iff c')). exact Hstuck.
Qed.

Theorem runFuel_timeout_sound : forall fuel c c',
  runFuel fuel c = Timeout c' ->
  reaches c c' /\ exists next, step c' = SStep next.
Proof.
  intros fuel c c' Hrun. split.
  - pose proof (runFuel_reachable fuel c) as Hreach.
    rewrite Hrun in Hreach. exact Hreach.
  - apply runFuel_timeout_final with fuel c. exact Hrun.
Qed.

Lemma trace_prepend_events : forall event result,
  trace_result_events (trace_prepend event result) =
  event :: trace_result_events result.
Proof. intros event []; reflexivity. Qed.

Lemma trace_prepend_config : forall event result,
  trace_result_config (trace_prepend event result) = trace_result_config result.
Proof. intros event []; reflexivity. Qed.

Lemma trace_prepend_run : forall event result,
  trace_result_run (trace_prepend event result) = trace_result_run result.
Proof. intros event []; reflexivity. Qed.

Theorem runFuelTrace_erases : forall fuel c,
  trace_result_run (runFuelTrace fuel c) = runFuel fuel c.
Proof.
  induction fuel as [| fuel IH]; intros [s e];
    cbn [runFuelTrace runFuel step observed_step].
  all: unfold step, observed_step; cbn [fst snd raw_result_step].
  - destruct (step_raw s e) as [| | c' event]; reflexivity.
  - destruct (step_raw s e) as [| | c' event]; try reflexivity.
    destruct event as [event |].
    + rewrite trace_prepend_run. apply IH.
    + apply IH.
Qed.

Theorem runFuelTrace_event_trace : forall fuel c,
  event_trace c (trace_result_events (runFuelTrace fuel c))
    (trace_result_config (runFuelTrace fuel c)).
Proof.
  induction fuel as [| fuel IH]; intros [s e];
    cbn [runFuelTrace observed_step].
  all: unfold observed_step; cbn [fst snd].
  - destruct (step_raw s e) as [| | c' event]; constructor.
  - destruct (step_raw s e) as [| | c' event] eqn:Hstep; try constructor.
    destruct event as [event |].
    + rewrite trace_prepend_events, trace_prepend_config.
      eapply EventTraceEvent; [exact Hstep | apply IH].
    + eapply EventTraceSilent; [exact Hstep | apply IH].
Qed.

Corollary runFuelTrace_reachable : forall fuel c,
  reaches c (trace_result_config (runFuelTrace fuel c)).
Proof.
  intros. eapply event_trace_reaches with
    (events := trace_result_events (runFuelTrace fuel c)).
  apply runFuelTrace_event_trace.
Qed.
