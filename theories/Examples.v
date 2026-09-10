(** * Example programs

    Core examples are complemented by named source terms and resolution checks.
    Typing derivations and rejection proofs cover every bundled source example
    in both modes. Executable evaluation checks include successful runs, stuck
    configurations, allocation order, strong update, deallocation and timeout. *)

From Stdlib Require Import List String Permutation Lia.
From DILLref Require Import Prelude Ty Syntax Index Scoping Mask Split Typing Infer.
From DILLref Require Import Renaming Substitution.
From DILLref Require Import NamedSyntax Resolve.
From DILLref Require Import Graph NatMap Store Semantics StoreTyping.
From DILLref Require Import StoreTypingSubst EvaluationContext Preservation.
Import ListNotations.
Open Scope string_scope.

(** ** Source programs

    Positive programs, programs accepted only in affine mode, and rejected
    programs are collected in [source_examples]. *)
Section SourceExamples.

(** [λx:A. x] *)
Definition linear_id (a : ty) : term := Lam a (LVar 0).

(** [nat ⊸ nat]: consumes its argument once. *)
Definition successor : term := Lam TNat (Succ (LVar 0)).

(** [add : nat ⊸ nat ⊸ nat], defined by iterating successor.
    Inside the two lambdas, [n] is index 0 and [m] is index 1. The step
    is closed and promoted; [m] supplies the linear accumulator.
    Applying this curried function evaluates [m] before [n] under CBV. *)
Definition add : term :=
  Lam TNat (Lam TNat (Iter (LVar 0) (Bang successor) (LVar 1))).

(** Expected result: [5], with an empty store, in both modes. *)
Definition add_two_three : term := App (App add (Nat 2)) (Nat 3).

(** A reference is allocated once as the seed, threaded through the iterator,
    then freed. Each evaluation of the step thunk allocates and frees a
    separate unit cell before producing the identity function.
    Expected result: [0] and an empty store in both modes, with [S n]
    allocations and frees. At zero only the seed cell is allocated. *)
Definition iter_ref (n : nat) : term :=
  LetUnit
    (Free
      (Iter (Nat n)
        (Bang (LetUnit (Free (New Unit)) (linear_id (TRef TUnit))))
        (New Unit)))
    (Nat 0).

(** Rejected in both modes: the step must have type [!(A ⊸ A)]. *)
Definition iter_unboxed_step : term := Iter (Nat 2) successor (Nat 0).

(** Rejected in both modes, even at zero: the promoted step captures [r].
    Inside the step lambda, its unit argument is index 0 and [r] is index 1. *)
Definition iter_captures_ref : term :=
  App
    (Lam (TRef TUnit)
      (Iter (Nat 0)
        (Bang (Lam TUnit (LetUnit (LVar 0) (Free (LVar 1))))) Unit))
    (New Unit).

(** Rejected in linear mode and accepted in affine mode: the step drops its
    accumulator. Expected affine result: [0], with an empty store. *)
Definition iter_drops_accumulator : term :=
  Iter (Nat 2) (Bang (Lam TNat (Nat 0))) (Nat 7).

(** [λf:(A ⊗ B ⊸ C). λx:A. λy:B. f (x, y)] *)
Definition curry (a b c : ty) : term :=
  Lam (TLolli (TTensor a b) c)
    (Lam a (Lam b (App (LVar 2) (Pair (LVar 1) (LVar 0))))).

(** [λf:(A ⊸ B ⊸ C). λp:A ⊗ B. let (x, y) = p in f x y].
    Inside the [let], [y] is index 0, [x] is index 1, the consumed [p] keeps
    index 2 and [f] is index 3. *)
Definition uncurry (a b c : ty) : term :=
  Lam (TLolli a (TLolli b c))
    (Lam (TTensor a b)
      (LetPair (LVar 0) (App (App (LVar 3) (LVar 1)) (LVar 0)))).

(** [λp:A ⊗ B. let (x, y) = p in (y, x)] *)
Definition sym_ten (a b : ty) : term :=
  Lam (TTensor a b) (LetPair (LVar 0) (Pair (LVar 0) (LVar 1))).

(** [λp:A & B. fst p]: accepted in both modes. *)
Definition with_fst (a b : ty) : term := Lam (TWith a b) (Fst (LVar 0)).

(** [λp:A ⊗ B. let (x, y) = p in x]: [y] is dropped, so this is rejected in
    linear mode and accepted in affine mode. *)
Definition tensor_fst (a b : ty) : term :=
  Lam (TTensor a b) (LetPair (LVar 0) (LVar 1)).

(** Counter: allocate, swap twice with rebinding, take the contents out,
    free, and add the two observed values. Evaluates to [1] with an empty
    final store. *)
Definition counter : term :=
  App
    (Lam (TRef TNat)
      (LetPair (Swap (LVar 0) (Nat 1))
        (LetPair (Swap (LVar 0) Unit)
          (LetUnit (Free (LVar 0)) (App (App add (LVar 3)) (LVar 1))))))
    (New (Nat 0)).

(** [let !u = !(new 0) in (u, u)]: each use of [u] allocates its own cell. *)
Definition bang_new_twice : term :=
  LetBang (Bang (New (Nat 0))) (Pair (UVar 0) (UVar 0)).

(** [(λr:ref nat. !r) (new 0)]: a resource captured under promotion,
    rejected in both modes. *)
Definition bang_captures_ref : term :=
  App (Lam (TRef TNat) (Bang (LVar 0))) (New (Nat 0)).

(** [λr:ref unit. if false then free r else ()]: accepted only in affine mode;
    applied to [new ()] it leaks the cell. *)
Definition affine_leak : term :=
  App
    (Lam (TRef TUnit)
      (LetUnit (If (Bool false) (Free (LVar 0)) Unit) (Nat 0)))
    (New Unit).

(** Modal structural maps consume the box once and bind a shared hypothesis. *)
Definition derelict (a : ty) : term :=
  Lam (TBang a) (LetBang (LVar 0) (UVar 0)).
Definition dig (a : ty) : term :=
  Lam (TBang a) (LetBang (LVar 0) (Bang (Bang (UVar 0)))).
Definition dup (a : ty) : term :=
  Lam (TBang a) (LetBang (LVar 0) (Pair (Bang (UVar 0)) (Bang (UVar 0)))).
Definition del (a : ty) : term := Lam (TBang a) (LetBang (LVar 0) Unit).

(** Each step is checked even when the count is zero. *)
Definition iter_mismatched_step (n : nat) : term :=
  Iter (Nat n) (Bang (Lam TUnit (LetUnit (LVar 0) (Nat 0)))) Unit.
Definition iter_mismatched_seed (n : nat) : term := Iter (Nat n) (Bang successor) Unit.
Definition iter_duplicates_accumulator (n : nat) : term :=
  Iter (Nat n) (Bang (Lam TUnit (LetUnit (LVar 0) (LVar 0)))) Unit.

Definition free_in_both_branches : term :=
  Lam (TRef TUnit) (If (Bool false) (Free (LVar 0)) (Free (LVar 0))).
Definition free_in_one_branch : term :=
  Lam (TRef TUnit) (If (Bool false) (Free (LVar 0)) Unit).
Definition free_in_one_component : term :=
  Lam (TRef TUnit) (With (Free (LVar 0)) Unit).
Definition free_after_branch : term :=
  Lam (TRef TUnit)
    (LetUnit (If (Bool false) (Free (LVar 0)) Unit) (Free (LVar 0))).
Definition free_nonunit : term := Free (New (Nat 0)).
Definition double_free : term :=
  Lam (TRef TUnit) (LetUnit (Free (LVar 0)) (Free (LVar 0))).
Definition alias_double_free : term :=
  Lam (TRef TUnit)
    (LetPair (Pair (LVar 0) (LVar 0))
      (LetUnit (Free (LVar 1)) (Free (LVar 0)))).

(** A closure owns the captured reference until it is applied. *)
Definition closure_ref : term :=
  App (App (Lam (TRef TUnit)
    (Lam TUnit (LetUnit (LVar 0) (Free (LVar 1))))) (New Unit)) Unit.

(** Extract the inner reference by strong update, then free both cells. *)
Definition nested_ref : term :=
  App (Lam (TRef (TRef TUnit))
    (LetPair (Swap (LVar 0) Unit)
      (LetUnit (Free (LVar 0)) (Free (LVar 1))))) (New (New Unit)).

(** Only the selected component is forced, so the two branches share a cell. *)
Definition lazy_shared_ref : term :=
  App (Lam (TRef TUnit) (Fst (With (Free (LVar 0)) (Free (LVar 0))))) (New Unit).

(** Strong update extracts the number and makes the cell freeable. *)
Definition read_and_free (n : nat) : term :=
  LetPair (Swap (New (Nat n)) Unit) (LetUnit (Free (LVar 0)) (LVar 1)).

(** The two argument traces allocate contents 2 and 3 respectively, so their
    order is observable even though the final store is empty. *)
Definition add_effects : term := App (App add (read_and_free 2)) (read_and_free 3).

(** Equal types do not identify two resource positions. *)
Definition sequential_two_refs : term :=
  Lam (TRef TUnit) (Lam (TRef TUnit)
    (LetUnit (Free (LVar 0)) (Free (LVar 1)))).

(** The named reading is lambda x:nat. lambda x:nat. x: the inner binder
    shadows the outer one, whose unused resource is allowed only affinely. *)
Definition shadowed_resource : term := Lam TNat (Lam TNat (LVar 0)).

Definition source_examples : list (string * term) :=
  [ ("linear_id", linear_id TNat);
    ("add", add);
    ("add_two_three", add_two_three);
    ("iter_zero", iter_ref 0);
    ("iter_ref", iter_ref 2);
    ("iter_unboxed_step", iter_unboxed_step);
    ("iter_captures_ref", iter_captures_ref);
    ("iter_drops_acc", iter_drops_accumulator);
    ("curry", curry TNat TBool TUnit);
    ("uncurry", uncurry TNat TBool TUnit);
    ("sym_ten", sym_ten TNat TBool);
    ("with_fst", with_fst TNat TBool);
    ("tensor_fst", tensor_fst TNat TBool);
    ("counter", counter);
    ("bang_new_twice", bang_new_twice);
    ("bang_captures_ref", bang_captures_ref);
    ("affine_leak", affine_leak);
    ("derelict", derelict TNat);
    ("dig", dig TNat);
    ("dup", dup TNat);
    ("del", del TNat);
    ("iter_bad_step", iter_mismatched_step 0);
    ("iter_bad_seed", iter_mismatched_seed 0);
    ("iter_duplicates_acc", iter_duplicates_accumulator 0);
    ("free_both_branches", free_in_both_branches);
    ("free_one_branch", free_in_one_branch);
    ("free_one_component", free_in_one_component);
    ("free_after_branch", free_after_branch);
    ("free_nonunit", free_nonunit);
    ("double_free", double_free);
    ("alias_double_free", alias_double_free);
    ("closure_ref", closure_ref);
    ("nested_ref", nested_ref);
    ("lazy_shared_ref", lazy_shared_ref);
    ("add_effects", add_effects);
    ("sequential_two_refs", sequential_two_refs);
    ("shadowed_resource", shadowed_resource) ].

Example source_examples_loc_free :
  forallb (fun p => loc_free (snd p)) source_examples = true.
Proof. reflexivity. Qed.

(** Source validation must inspect the step body even when the count is zero. *)
Example iter_zero_does_not_hide_location :
  loc_free
    (Iter (Nat 0)
      (Bang (Lam TUnit (LetUnit (LVar 0) (Free (Loc 0))))) Unit) = false.
Proof. reflexivity. Qed.
End SourceExamples.

(** ** Executable inference examples

    The expected results below are data independent of [infer]. Their exact
    equality with the computed results is proved in Rocq and checked again by
    the extracted OCaml driver. The source catalog is closed, so separate edge
    cases exercise nonempty leftovers and malformed inputs. *)
Section InferExamples.

Definition infer_result : Type := option (ty * mask).
Definition mode_infer_results : Type := infer_result * infer_result.

Definition inferred_both (a : ty) : mode_infer_results :=
  (Some (a, []), Some (a, [])).

Definition inferred_affine (a : ty) : mode_infer_results :=
  (None, Some (a, [])).

Definition rejected_both : mode_infer_results := (None, None).

Definition source_infer_expectations : list (string * mode_infer_results) :=
  [ ("linear_id", inferred_both (TLolli TNat TNat));
    ("add", inferred_both (TLolli TNat (TLolli TNat TNat)));
    ("add_two_three", inferred_both TNat);
    ("iter_zero", inferred_both TNat);
    ("iter_ref", inferred_both TNat);
    ("iter_unboxed_step", rejected_both);
    ("iter_captures_ref", rejected_both);
    ("iter_drops_acc", inferred_affine TNat);
    ("curry", inferred_both
      (TLolli (TLolli (TTensor TNat TBool) TUnit)
        (TLolli TNat (TLolli TBool TUnit))));
    ("uncurry", inferred_both
      (TLolli (TLolli TNat (TLolli TBool TUnit))
        (TLolli (TTensor TNat TBool) TUnit)));
    ("sym_ten", inferred_both
      (TLolli (TTensor TNat TBool) (TTensor TBool TNat)));
    ("with_fst", inferred_both (TLolli (TWith TNat TBool) TNat));
    ("tensor_fst", inferred_affine (TLolli (TTensor TNat TBool) TNat));
    ("counter", inferred_both TNat);
    ("bang_new_twice", inferred_both (TTensor (TRef TNat) (TRef TNat)));
    ("bang_captures_ref", rejected_both);
    ("affine_leak", inferred_affine TNat);
    ("derelict", inferred_both (TLolli (TBang TNat) TNat));
    ("dig", inferred_both (TLolli (TBang TNat) (TBang (TBang TNat))));
    ("dup", inferred_both
      (TLolli (TBang TNat) (TTensor (TBang TNat) (TBang TNat))));
    ("del", inferred_both (TLolli (TBang TNat) TUnit));
    ("iter_bad_step", rejected_both);
    ("iter_bad_seed", rejected_both);
    ("iter_duplicates_acc", rejected_both);
    ("free_both_branches", inferred_both (TLolli (TRef TUnit) TUnit));
    ("free_one_branch", inferred_affine (TLolli (TRef TUnit) TUnit));
    ("free_one_component", inferred_affine
      (TLolli (TRef TUnit) (TWith TUnit TUnit)));
    ("free_after_branch", rejected_both);
    ("free_nonunit", rejected_both);
    ("double_free", rejected_both);
    ("alias_double_free", rejected_both);
    ("closure_ref", inferred_both TUnit);
    ("nested_ref", inferred_both TUnit);
    ("lazy_shared_ref", inferred_both TUnit);
    ("add_effects", inferred_both TNat);
    ("sequential_two_refs", inferred_both
      (TLolli (TRef TUnit) (TLolli (TRef TUnit) TUnit)));
    ("shadowed_resource", inferred_affine
      (TLolli TNat (TLolli TNat TNat))) ].

Definition source_infer_results : list (string * mode_infer_results) :=
  map (fun p =>
    (fst p,
      (infer Linear [] [] [] (snd p),
       infer Affine [] [] [] (snd p)))) source_examples.

Example source_infer_results_expected :
  source_infer_results = source_infer_expectations.
Proof. reflexivity. Qed.

Inductive infer_case : Type :=
  | InferCase :
      string -> flag -> list ty -> list ty -> mask -> term -> infer_result ->
      infer_case.

Definition infer_case_name (c : infer_case) : string :=
  match c with InferCase name _ _ _ _ _ _ => name end.

Definition run_infer_case (c : infer_case) : infer_result :=
  match c with
  | InferCase _ f shared resources input e _ =>
      infer f shared resources input e
  end.

Definition expected_infer_case (c : infer_case) : infer_result :=
  match c with InferCase _ _ _ _ _ _ expected => expected end.

Definition infer_result_eqb (r1 r2 : infer_result) : bool :=
  match r1, r2 with
  | None, None => true
  | Some (a, O1), Some (b, O2) => ty_eqb a b && mask_eqb O1 O2
  | _, _ => false
  end.

Definition infer_case_passes (c : infer_case) : bool :=
  infer_result_eqb (run_infer_case c) (expected_infer_case c).

Definition infer_edge_cases : list infer_case :=
  [ InferCase "consume_first" Linear [] [TNat; TBool] [true; true]
      (LVar 0) (Some (TNat, [false; true]));
    InferCase "stable_second_index" Linear [] [TNat; TBool] [true; true]
      (Pair (LVar 0) (LVar 1))
      (Some (TTensor TNat TBool, [false; false]));
    InferCase "frame_without_second" Linear [] [TNat; TBool] [true; false]
      (LVar 0) (Some (TNat, [false; false]));
    InferCase "unavailable_resource" Linear [] [TNat] [false]
      (LVar 0) None;
    InferCase "branch_mismatch_linear" Linear [] [TRef TUnit] [true]
      (If (Bool false) (Free (LVar 0)) Unit) None;
    InferCase "branch_meet_affine" Affine [] [TRef TUnit] [true]
      (If (Bool false) (Free (LVar 0)) Unit) (Some (TUnit, [false]));
    InferCase "branch_then_reuse" Affine [] [TRef TUnit] [true]
      (LetUnit (If (Bool false) (Free (LVar 0)) Unit) (Free (LVar 0))) None;
    InferCase "with_meet_affine" Affine [] [TRef TUnit] [true]
      (With (Free (LVar 0)) Unit) (Some (TWith TUnit TUnit, [false]));
    InferCase "local_drop_linear" Linear [] [] []
      (Lam TUnit Unit) None;
    InferCase "local_drop_affine" Affine [] [] []
      (Lam TUnit Unit) (Some (TLolli TUnit TUnit, []));
    InferCase "pair_local_drop_linear" Linear [] [] []
      (LetPair (Pair Unit Unit) (LVar 1)) None;
    InferCase "pair_local_drop_affine" Affine [] [] []
      (LetPair (Pair Unit Unit) (LVar 1)) (Some (TUnit, []));
    InferCase "promotion_preserves_frame" Linear [] [TRef TUnit] [true]
      (Bang (Nat 0)) (Some (TBang TNat, [true]));
    InferCase "promotion_capture_affine" Affine [] [TRef TUnit] [true]
      (Bang (LVar 0)) None;
    InferCase "short_input_mask" Linear [] [TNat] []
      (LVar 0) None;
    InferCase "long_input_mask" Linear [] [] [true]
      Unit None;
    InferCase "resource_index_out_of_scope" Linear [] [TNat] [true]
      (LVar 1) None;
    InferCase "shared_index_out_of_scope" Linear [] [] []
      (UVar 0) None;
    InferCase "runtime_location" Linear [] [] []
      (Loc 0) None ].

Example infer_edge_cases_expected :
  forallb infer_case_passes infer_edge_cases = true.
Proof. reflexivity. Qed.

(** The checker result also records the type established or rejected by the
    independent declarative proofs below, not only the expected mode. *)
Definition infer_matches_classification (e : term) : Prop :=
  match infer Linear [] [] [] e, infer Affine [] [] [] e with
  | Some (a, out_linear), Some (b, out_affine) =>
      out_linear = [] /\ out_affine = [] /\
      has_type Linear [] [] [] e a /\ has_type Affine [] [] [] e b
  | None, Some (b, out_affine) =>
      out_affine = [] /\ (forall a, ~ has_type Linear [] [] [] e a) /\
      has_type Affine [] [] [] e b
  | None, None => forall f a, ~ has_type f [] [] [] e a
  | Some _, None => False
  end.

End InferExamples.

(** ** Executable evaluation examples *)
Section EvaluationExamples.

Definition evaluation_case : Type :=
  (string * (nat * (config * run_result)))%type.

Definition make_evaluation_case
    (name : string) (fuel : nat) (initial : config) (expected : run_result)
    : evaluation_case :=
  (name, (fuel, (initial, expected))).

Definition evaluation_case_name (case : evaluation_case) : string :=
  fst case.

Definition run_evaluation_case (case : evaluation_case) : run_result :=
  runFuel (fst (snd case)) (fst (snd (snd case))).

Definition expected_evaluation_case (case : evaluation_case) : run_result :=
  snd (snd (snd case)).

(** Expectations are written independently of [runFuel]. The cases expose
    evaluation order at zero iterations, repeated forcing through addition,
    allocation at fresh addresses, strong update, deallocation and both
    nonterminal outcomes. *)
Definition evaluation_examples : list evaluation_case :=
  [ make_evaluation_case "add_two_three" 100 ([], add_two_three)
      (RValue ([], Nat 5));
    make_evaluation_case "iter_zero" 100 ([], iter_ref 0)
      (RValue ([], Nat 0));
    make_evaluation_case "iter_ref" 200 ([], iter_ref 2)
      (RValue ([], Nat 0));
    make_evaluation_case "iter_strict_seed" 10
      ([], Iter (Nat 0) (Bang successor) (Succ (Nat 4)))
      (RValue ([], Nat 5));
    make_evaluation_case "counter" 200 ([], counter)
      (RValue ([], Nat 1));
    make_evaluation_case "bang_new_twice" 20 ([], bang_new_twice)
      (RValue ([(1, Nat 0); (0, Nat 0)], Pair (Loc 0) (Loc 1)));
    make_evaluation_case "affine_leak" 20 ([], affine_leak)
      (RValue ([(0, Unit)], Nat 0));
    make_evaluation_case "read_and_free" 20 ([], read_and_free 7)
      (RValue ([], Nat 7));
    make_evaluation_case "free_nonunit_stuck" 10 ([], free_nonunit)
      (RStuck ([(0, Nat 0)], Free (Loc 0)));
    make_evaluation_case "zero_fuel_timeout" 0 ([], Succ (Nat 0))
      (Timeout ([], Succ (Nat 0))) ].

Lemma evaluation_examples_correct :
  Forall
    (fun case => run_evaluation_case case = expected_evaluation_case case)
    evaluation_examples.
Proof. repeat constructor. Qed.

(** Store-event expectations are independent data, rather than projections of
    the expected final stores. They expose address reuse, argument order and
    repeated forcing of the iterator step thunk. *)
Definition event_trace_case : Type :=
  (string * (nat * (config * list store_event)))%type.

Definition make_event_trace_case
    (name : string) (fuel : nat) (initial : config)
    (expected : list store_event) : event_trace_case :=
  (name, (fuel, (initial, expected))).

Definition event_trace_case_name (case : event_trace_case) : string :=
  fst case.

Definition run_event_trace_case (case : event_trace_case) : list store_event :=
  trace_result_events
    (runFuelTrace (fst (snd case)) (fst (snd (snd case)))).

Definition expected_event_trace_case (case : event_trace_case)
    : list store_event :=
  snd (snd (snd case)).

Definition event_trace_examples : list event_trace_case :=
  [ make_event_trace_case "counter" 200 ([], counter)
      [EventAlloc 0; EventSwap 0; EventSwap 0; EventFree 0];
    make_event_trace_case "iter_zero" 100 ([], iter_ref 0)
      [EventAlloc 0; EventFree 0];
    make_event_trace_case "iter_ref" 200 ([], iter_ref 2)
      [EventAlloc 0; EventAlloc 1; EventFree 1;
       EventAlloc 1; EventFree 1; EventFree 0];
    make_event_trace_case "add_effects" 200 ([], add_effects)
      [EventAlloc 0; EventSwap 0; EventFree 0;
       EventAlloc 0; EventSwap 0; EventFree 0];
    make_event_trace_case "nested_ref" 100 ([], nested_ref)
      [EventAlloc 0; EventAlloc 1; EventSwap 1; EventFree 1; EventFree 0];
    make_event_trace_case "lazy_shared_ref" 100 ([], lazy_shared_ref)
      [EventAlloc 0; EventFree 0];
    make_event_trace_case "bang_new_twice" 20 ([], bang_new_twice)
      [EventAlloc 0; EventAlloc 1];
    make_event_trace_case "affine_leak" 20 ([], affine_leak)
      [EventAlloc 0] ].

Lemma event_trace_examples_correct :
  Forall
    (fun case => run_event_trace_case case = expected_event_trace_case case)
    event_trace_examples.
Proof. repeat constructor. Qed.

End EvaluationExamples.

(** ** Checks against declarative typing *)
Section TypingChecks.

Lemma linear_id_typed : forall f G L a,
  has_type f G L (mask_zero (List.length L)) (linear_id a) (TLolli a a).
Proof.
  intros. unfold linear_id. apply TyLam.
  change (has_type f G (a :: L) (mask_single (S (List.length L)) 0) (LVar 0) a).
  apply TyLVar. reflexivity.
Qed.

Lemma add_typed : forall f,
  has_type f [] [] [] add (TLolli TNat (TLolli TNat TNat)).
Proof.
  intros f. unfold add, successor. apply TyLam, TyLam.
  eapply TyIter with (Uc := [true; false]) (R := [false; true])
    (Us := [false; false]) (Uz := [false; true]).
  - repeat constructor.
  - repeat constructor.
  - change (has_type f [] [TNat; TNat]
      (mask_single 2 0) (LVar 0) TNat).
    apply TyLVar. reflexivity.
  - apply TyBang, TyLam, TySucc.
    change (has_type f [] [TNat; TNat; TNat]
      (mask_single 3 0) (LVar 0) TNat).
    apply TyLVar. reflexivity.
  - change (has_type f [] [TNat; TNat]
      (mask_single 2 1) (LVar 1) TNat).
    apply TyLVar. reflexivity.
Qed.

Lemma add_two_three_typed : forall f, has_type f [] [] [] add_two_three TNat.
Proof.
  intros f. unfold add_two_three.
  eapply TyApp with (U1 := []) (U2 := []); [constructor | | apply TyNat].
  eapply TyApp with (U1 := []) (U2 := []);
    [constructor | apply add_typed | apply TyNat].
Qed.

Lemma iter_ref_typed : forall f n, has_type f [] [] [] (iter_ref n) TNat.
Proof.
  intros f n. unfold iter_ref.
  eapply TyLetUnit with (U1 := []) (U2 := []); [constructor | | apply TyNat].
  apply TyFree.
  eapply TyIter with (Uc := []) (R := []) (Us := []) (Uz := []);
    try constructor.
  - eapply TyLetUnit with (U1 := []) (U2 := []); [constructor | | ].
    + apply TyFree, TyNew, TyUnit.
    + apply linear_id_typed.
  - apply TyUnit.
Qed.

Example unavailable_position_keeps_indices :
  has_type Linear [] [TNat; TNat] [false; true] (LVar 1) TNat.
Proof.
  change (has_type Linear [] [TNat; TNat]
    (mask_single 2 1) (LVar 1) TNat).
  apply TyLVar. reflexivity.
Qed.

Example additive_sharing :
  has_type Linear [] [TNat] [true]
    (With (LVar 0) (LVar 0)) (TWith TNat TNat).
Proof.
  apply TyWith; change (has_type Linear [] [TNat]
    (mask_single 1 0) (LVar 0) TNat); apply TyLVar; reflexivity.
Qed.

Example multiplicative_duplicate_rejected :
  ~ has_type Linear [] [TNat] [true]
    (Pair (LVar 0) (LVar 0)) (TTensor TNat TNat).
Proof.
  intros H. inversion H; subst.
  repeat match goal with
    | Hv : has_type _ _ _ _ (LVar _) _ |- _ => apply typing_lvar_available in Hv
    end.
  eapply splitM_no_overlap; eassumption.
Qed.

Example shared_binder_has_its_own_scope : forall f,
  has_type f [] [] []
    (LetBang (Bang (Nat 2)) (Pair (UVar 0) (UVar 0))) (TTensor TNat TNat).
Proof.
  intros f. eapply TyLetBang with (U1 := []) (U2 := []);
    [constructor | apply TyBang, TyNat | ].
  eapply TyPair with (U1 := []) (U2 := []); [constructor | | ];
    apply TyUVar; reflexivity.
Qed.

Example let_bang_does_not_bind_resource :
  ~ scoped 0 0 (LetBang (Bang (Nat 2)) (LVar 0)).
Proof.
  intros H. inversion H; subst.
  match goal with Hbody : scoped _ _ (LVar _) |- _ => inversion Hbody end.
  lia.
Qed.

Example affine_local_drop :
  has_type Affine [] [] [] (Lam TUnit Unit) (TLolli TUnit TUnit).
Proof.
  apply TyLam. eapply TyWeak with (U := [false]).
  - apply TyUnit.
  - repeat constructor.
Qed.

Example linear_local_drop_rejected :
  ~ has_type Linear [] [] [] (Lam TUnit Unit) (TLolli TUnit TUnit).
Proof.
  intros H. inversion H; subst.
  match goal with Hbody : has_type Linear _ _ _ Unit _ |- _ => inversion Hbody end.
Qed.

Example affine_branch_weakening :
  has_type Affine [] [TRef TUnit] [true]
    (If (Bool false) (Free (LVar 0)) Unit) TUnit.
Proof.
  eapply TyIf with (Uc := [false]) (Ub := [true]).
  - repeat constructor.
  - apply TyBool.
  - apply TyFree. change (has_type Affine [] [TRef TUnit]
      (mask_single 1 0) (LVar 0) (TRef TUnit)).
    apply TyLVar. reflexivity.
  - eapply TyWeak with (U := [false]); [apply TyUnit | repeat constructor].
Qed.

Example promotion_capture_rejected : forall f,
  ~ has_type f [] [TRef TNat] [true] (Bang (LVar 0)) (TBang (TRef TNat)).
Proof. intros. apply typing_bang_lvar_absurd. Qed.

End TypingChecks.

(** ** Context permutations

    Reordering a scope preserves allocation to the parts, but may change
    their internal order. Repeated entries are valid for the generic split;
    named resources additionally require unique keys. *)
Section ContextPermutations.
Example split_transport_reverses_parts :
  exists left right, Split [2; 1; 0] left right /\
    Permutation [0; 2] left /\ Permutation [1] right.
Proof.
  eapply split_permutation_transport with (l := [0; 1; 2]).
  - change (Permutation [0; 1; 2] (rev [0; 1; 2])). apply Permutation_rev.
  - apply SplitL, SplitR, SplitL, SplitNil.
Qed.

Example split_transport_cannot_fix_part_order :
  ~ Split [2; 1; 0] [0; 2] [1].
Proof. intros H. inversion H. Qed.

Example split_permutation_with_repeated_entries :
  exists left right, Split [0; 0] left right /\
    Permutation [0] left /\ Permutation [0] right.
Proof. apply split_permutation_iff. apply Permutation_refl. Qed.

Example keyed_split_reorders_a_part :
  NoDup (map fst [(7, TNat); (3, TBool)]) /\
    exists left right, Split [(7, TNat); (3, TBool)] left right /\
      Permutation [(3, TBool); (7, TNat)] left /\ Permutation [] right.
Proof.
  apply (proj1 (split_keyed_permutation_iff fst
    [(7, TNat); (3, TBool)] [(3, TBool); (7, TNat)] [])).
  split; [apply perm_swap | repeat constructor; simpl; intuition discriminate].
Qed.

(** Distinct complete bindings can still clash on their identifier. *)
Example keyed_split_duplicate_key_rejected :
  ~ (Permutation [(0, TNat); (0, TBool)] ([(0, TNat)] ++ [(0, TBool)]) /\
      NoDup (map fst ([(0, TNat)] ++ [(0, TBool)]))).
Proof.
  intros [_ Hnd]. inversion Hnd as [| k keys Hnot Htail]; subst.
  apply Hnot. simpl. auto.
Qed.
End ContextPermutations.

(** ** Binding operations

    These syntax checks deliberately include open terms and terms with
    locations. They
    test capture avoidance independently of the typing restrictions on the
    images of shared variables. The same cases run after extraction. *)
Section BindingOperations.
Definition binding_examples : list (string * (term * term)) :=
  [ ("rename_under_lambda",
      (rename S S (Lam TNat (Pair (LVar 0) (Pair (LVar 1) (UVar 0)))),
       Lam TNat (Pair (LVar 0) (Pair (LVar 2) (UVar 1)))));
    ("subst_under_shared_binder",
      (subst_l (UVar 0) (LetBang (Bang (Nat 2)) (LVar 0)),
       LetBang (Bang (Nat 2)) (UVar 1)));
    ("subst_under_resource_binder",
      (subst_u (LVar 0) (Lam TNat (UVar 0)),
       Lam TNat (LVar 1)));
    ("subst_under_pair_binders",
      (subst_l (Pair (LVar 0) (UVar 0))
        (LetPair (Pair Unit Unit) (Pair (LVar 1) (Pair (LVar 0) (LVar 2)))),
       LetPair (Pair Unit Unit)
         (Pair (LVar 1) (Pair (LVar 0) (Pair (LVar 2) (UVar 0))))));
    ("addresses_are_not_indices",
      (subst_l (Nat 7) (rename S id_ren (Pair (Loc 3) (LVar 0))),
       Pair (Loc 3) (Nat 7))) ].

Example binding_examples_correct :
  Forall (fun p => fst (snd p) = snd (snd p)) binding_examples.
Proof. repeat constructor. Qed.

Example linear_beta_uses_argument_resource : forall f,
  has_type f [] [TRef TUnit] [true] (subst_l (LVar 0) (Free (LVar 0))) TUnit.
Proof.
  intros f. eapply typing_subst_l with (a := TRef TUnit) (U := [false]) (V := [true]).
  - apply TyFree.
    change (has_type f [] [TRef TUnit; TRef TUnit]
      (mask_single 2 0) (LVar 0) (TRef TUnit)).
    apply TyLVar. reflexivity.
  - change (has_type f [] [TRef TUnit] (mask_single 1 0) (LVar 0) (TRef TUnit)).
    apply TyLVar. reflexivity.
  - repeat constructor.
Qed.

Example shared_beta_duplicates_computation : forall f,
  has_type f [] [] [] (subst_u (New (Nat 0)) (Pair (UVar 0) (UVar 0)))
    (TTensor (TRef TNat) (TRef TNat)).
Proof.
  intros f. eapply typing_subst_u with (a := TRef TNat).
  - eapply TyPair with (U1 := []) (U2 := []); [constructor | | ];
      apply TyUVar; reflexivity.
  - apply TyNew, TyNat.
Qed.

Example affine_beta_can_drop_argument :
  has_type Affine [] [TRef TUnit] [true] (subst_l (LVar 0) Unit) TUnit.
Proof.
  eapply typing_subst_l with (a := TRef TUnit) (U := [false]) (V := [true]).
  - eapply TyWeak with (U := [false; false]); [apply TyUnit | repeat constructor].
  - change (has_type Affine [] [TRef TUnit] (mask_single 1 0) (LVar 0) (TRef TUnit)).
    apply TyLVar. reflexivity.
  - repeat constructor.
Qed.

Example exchange_moves_availability : forall f,
  has_type f [] [TBool; TNat] [true; false]
    (rename id_ren exchange_ren (LVar 1)) TBool.
Proof.
  intros. apply typing_exchange_resource.
  change (has_type f [] [TNat; TBool] (mask_single 2 1) (LVar 1) TBool).
  apply TyLVar. reflexivity.
Qed.

Example shared_contraction_identifies_indices : forall f,
  has_type f [TNat] [] []
    (rename contract_ren id_ren (Pair (UVar 0) (UVar 1))) (TTensor TNat TNat).
Proof.
  intros. apply typing_contract_shared.
  eapply TyPair with (U1 := []) (U2 := []); [constructor | | ];
    apply TyUVar; reflexivity.
Qed.

Example shared_substitution_rejects_resource_capture : forall f,
  ~ shared_env f [] [TNat] [TNat] (fun _ => LVar 0).
Proof.
  intros f H. specialize (H 0 TNat eq_refl).
  apply typing_lvar_available in H. discriminate.
Qed.
End BindingOperations.

(** ** Derivations for the catalog

    Infer the exact premise masks from variables, then discharge the concrete
    split. Affine weakening is supplied explicitly in the examples below. *)
Local Ltac derive_type :=
    match goal with
    | |- has_type ?f ?G ?L _ (LVar ?i) ?a =>
        first [apply TyLVar; reflexivity |
          change (has_type f G L (mask_single (List.length L) i) (LVar i) a);
          apply TyLVar; reflexivity]
    | |- has_type ?f ?G ?L _ (UVar ?i) ?a =>
        first [apply TyUVar; reflexivity |
          change (has_type f G L (mask_zero (List.length L)) (UVar i) a);
          apply TyUVar; reflexivity]
    | |- has_type _ _ _ _ (Lam _ _) _ => apply TyLam; derive_type
    | |- has_type _ _ _ _ (App _ _) _ =>
        eapply TyApp; [ | derive_type | derive_type ]; repeat constructor
    | |- has_type _ _ _ _ Unit _ => apply TyUnit
    | |- has_type _ _ _ _ (LetUnit _ _) _ =>
        eapply TyLetUnit; [ | derive_type | derive_type ]; repeat constructor
    | |- has_type _ _ _ _ (Pair _ _) _ =>
        eapply TyPair; [ | derive_type | derive_type ]; repeat constructor
    | |- has_type _ _ _ _ (LetPair _ _) _ =>
        eapply TyLetPair; [ | derive_type | derive_type ]; repeat constructor
    | |- has_type _ _ _ _ (With _ _) _ => apply TyWith; derive_type
    | |- has_type _ _ _ _ (Fst _) _ => eapply TyFst; derive_type
    | |- has_type _ _ _ _ (Snd _) _ => eapply TySnd; derive_type
    | |- has_type _ _ _ _ (Bang _) _ => apply TyBang; derive_type
    | |- has_type _ _ _ _ (LetBang _ _) _ =>
        eapply TyLetBang; [ | derive_type | derive_type ]; repeat constructor
    | |- has_type _ _ _ _ (Nat _) _ => apply TyNat
    | |- has_type _ _ _ _ (Succ _) _ => apply TySucc; derive_type
    | |- has_type _ _ _ _ (Iter _ _ _) _ =>
        eapply TyIter; [ | | derive_type | derive_type | derive_type ]; repeat constructor
    | |- has_type _ _ _ _ (Bool _) _ => apply TyBool
    | |- has_type _ _ _ _ (If _ _ _) _ =>
        eapply TyIf; [ | derive_type | derive_type | derive_type ]; repeat constructor
    | |- has_type _ _ _ _ (New _) _ => apply TyNew; derive_type
    | |- has_type _ _ _ _ (Swap _ _) _ =>
        eapply TySwap; [ | derive_type | derive_type ]; repeat constructor
    | |- has_type _ _ _ _ (Free _) _ => apply TyFree; derive_type
    end.

Section CatalogDerivations.
Lemma curry_typed : forall f a b c,
  has_type f [] [] [] (curry a b c)
    (TLolli (TLolli (TTensor a b) c) (TLolli a (TLolli b c))).
Proof. intros. unfold curry. derive_type. Qed.

Lemma uncurry_typed : forall f a b c,
  has_type f [] [] [] (uncurry a b c)
    (TLolli (TLolli a (TLolli b c)) (TLolli (TTensor a b) c)).
Proof. intros. unfold uncurry. derive_type. Qed.

Lemma sym_ten_typed : forall f a b,
  has_type f [] [] [] (sym_ten a b) (TLolli (TTensor a b) (TTensor b a)).
Proof. intros. unfold sym_ten. derive_type. Qed.

Lemma with_fst_typed : forall f a b,
  has_type f [] [] [] (with_fst a b) (TLolli (TWith a b) a).
Proof. intros. unfold with_fst. derive_type. Qed.

Lemma derelict_typed : forall f a,
  has_type f [] [] [] (derelict a) (TLolli (TBang a) a).
Proof. intros. unfold derelict. derive_type. Qed.
Lemma dig_typed : forall f a,
  has_type f [] [] [] (dig a) (TLolli (TBang a) (TBang (TBang a))).
Proof. intros. unfold dig. derive_type. Qed.
Lemma dup_typed : forall f a,
  has_type f [] [] [] (dup a) (TLolli (TBang a) (TTensor (TBang a) (TBang a))).
Proof. intros. unfold dup. derive_type. Qed.
Lemma del_typed : forall f a,
  has_type f [] [] [] (del a) (TLolli (TBang a) TUnit).
Proof. intros. unfold del. derive_type. Qed.

Lemma counter_typed : forall f, has_type f [] [] [] counter TNat.
Proof. intros. unfold counter, add, successor. derive_type. Qed.
Lemma bang_new_twice_typed : forall f,
  has_type f [] [] [] bang_new_twice (TTensor (TRef TNat) (TRef TNat)).
Proof. intros. unfold bang_new_twice. derive_type. Qed.
Lemma closure_ref_typed : forall f, has_type f [] [] [] closure_ref TUnit.
Proof. intros. unfold closure_ref. derive_type. Qed.
Lemma nested_ref_typed : forall f, has_type f [] [] [] nested_ref TUnit.
Proof. intros. unfold nested_ref. derive_type. Qed.
Lemma lazy_shared_ref_typed : forall f, has_type f [] [] [] lazy_shared_ref TUnit.
Proof.
  intros. unfold lazy_shared_ref.
  eapply TyApp with (U1 := []) (U2 := []); [constructor | derive_type | derive_type].
Qed.
Lemma add_effects_typed : forall f, has_type f [] [] [] add_effects TNat.
Proof. intros. unfold add_effects, read_and_free, add, successor. derive_type. Qed.
Lemma free_in_both_branches_typed : forall f,
  has_type f [] [] [] free_in_both_branches (TLolli (TRef TUnit) TUnit).
Proof. intros. unfold free_in_both_branches. derive_type. Qed.
End CatalogDerivations.

(** ** Programs accepted only with affine weakening *)
Section AffineOnly.

Lemma tensor_fst_affine : forall a b,
  has_type Affine [] [] [] (tensor_fst a b) (TLolli (TTensor a b) a).
Proof.
  intros. unfold tensor_fst. apply TyLam.
  eapply TyLetPair with (U1 := [true]) (U2 := [false]); [repeat constructor | derive_type | ].
  eapply TyWeak with (U := [false; true; false]); [derive_type | repeat constructor].
Qed.

Lemma iter_drops_accumulator_affine : has_type Affine [] [] [] iter_drops_accumulator TNat.
Proof.
  unfold iter_drops_accumulator.
  eapply TyIter with (Uc := []) (R := []) (Us := []) (Uz := []);
    try solve [repeat constructor].
  apply TyBang, TyLam. eapply TyWeak with (U := [false]);
    [apply TyNat | repeat constructor].
Qed.

Lemma free_in_one_branch_affine :
  has_type Affine [] [] [] free_in_one_branch (TLolli (TRef TUnit) TUnit).
Proof.
  unfold free_in_one_branch. apply TyLam.
  eapply TyIf with (Uc := [false]) (Ub := [true]);
    try solve [repeat constructor | derive_type].
  eapply TyWeak with (U := [false]); [apply TyUnit | repeat constructor].
Qed.
Lemma free_in_one_component_affine :
  has_type Affine [] [] [] free_in_one_component (TLolli (TRef TUnit) (TWith TUnit TUnit)).
Proof.
  unfold free_in_one_component. apply TyLam, TyWith; try derive_type.
  eapply TyWeak with (U := [false]); [apply TyUnit | repeat constructor].
Qed.
Lemma affine_leak_typed : has_type Affine [] [] [] affine_leak TNat.
Proof.
  unfold affine_leak. eapply TyApp with (U1 := []) (U2 := []);
    [constructor | | derive_type].
  apply TyLam. eapply TyLetUnit with (U1 := [true]) (U2 := [false]);
    [repeat constructor | exact affine_branch_weakening | derive_type].
Qed.
End AffineOnly.

(** ** Rejected programs

    Expose syntax-directed premises through any outer affine weakening.
    In linear mode the exposed mask is exactly the original mask. *)
Local Ltac expose_typing H :=
  let M := fresh "used" in let Heq := fresh "Hexact" in
  let Hle := fresh "Hinclude" in let Hhead := fresh "Hhead" in
  destruct (typing_generation _ _ _ _ _ _ H) as [M [Heq [Hle Hhead]]]; clear H;
  try (specialize (Heq eq_refl); subst M);
  cbn [typing_head] in Hhead;
  repeat match goal with
  | H : exists _, _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  end; cbn in *; subst; try discriminate.

(** The examples have finite, concrete scopes. Inverting the pointwise mask
    relations detects incompatible availability and overlapping demands. *)
Local Ltac reject_typing :=
  repeat match goal with H : has_type _ _ _ _ _ _ |- _ => expose_typing H end;
  repeat match goal with
  | H : mask_le [] _ |- _ => inversion H; clear H; subst
  | H : mask_le (_ :: _) _ |- _ => inversion H; clear H; subst
  | H : mask_le _ [] |- _ => inversion H; clear H; subst
  | H : mask_le _ (_ :: _) |- _ => inversion H; clear H; subst
  | H : SplitM [] _ _ |- _ => inversion H; clear H; subst
  | H : SplitM (_ :: _) _ _ |- _ => inversion H; clear H; subst
  | H : SplitM _ [] _ |- _ => inversion H; clear H; subst
  | H : SplitM _ (_ :: _) _ |- _ => inversion H; clear H; subst
  end; congruence.

Section RejectedPrograms.
Lemma tensor_fst_linear_rejected : forall a b c,
  ~ has_type Linear [] [] [] (tensor_fst a b) c.
Proof. intros a b c H. unfold tensor_fst in H. reject_typing. Qed.

Lemma iter_unboxed_step_rejected : forall f a,
  ~ has_type f [] [] [] iter_unboxed_step a.
Proof. intros f a H. unfold iter_unboxed_step, successor in H. reject_typing. Qed.

Lemma iter_mismatched_step_rejected : forall f n a,
  ~ has_type f [] [] [] (iter_mismatched_step n) a.
Proof. intros f n a H. unfold iter_mismatched_step in H. reject_typing. Qed.

Lemma iter_mismatched_seed_rejected : forall f n a,
  ~ has_type f [] [] [] (iter_mismatched_seed n) a.
Proof. intros f n a H. unfold iter_mismatched_seed, successor in H. reject_typing. Qed.

Lemma iter_captures_ref_rejected : forall f a,
  ~ has_type f [] [] [] iter_captures_ref a.
Proof. intros f a H. unfold iter_captures_ref in H. reject_typing. Qed.

Lemma iter_duplicates_accumulator_rejected : forall f n a,
  ~ has_type f [] [] [] (iter_duplicates_accumulator n) a.
Proof. intros f n a H. unfold iter_duplicates_accumulator in H. reject_typing. Qed.

Lemma iter_drops_accumulator_linear_rejected : forall a,
  ~ has_type Linear [] [] [] iter_drops_accumulator a.
Proof. intros a H. unfold iter_drops_accumulator in H. reject_typing. Qed.

Lemma bang_captures_ref_rejected : forall f a,
  ~ has_type f [] [] [] bang_captures_ref a.
Proof. intros f a H. unfold bang_captures_ref in H. reject_typing. Qed.

Lemma free_in_one_branch_linear_rejected : forall a,
  ~ has_type Linear [] [] [] free_in_one_branch a.
Proof. intros a H. unfold free_in_one_branch in H. reject_typing. Qed.

Lemma free_in_one_component_linear_rejected : forall a,
  ~ has_type Linear [] [] [] free_in_one_component a.
Proof. intros a H. unfold free_in_one_component in H. reject_typing. Qed.

Lemma free_after_branch_rejected : forall f a,
  ~ has_type f [] [] [] free_after_branch a.
Proof. intros f a H. unfold free_after_branch in H. reject_typing. Qed.

Lemma free_nonunit_rejected : forall f a, ~ has_type f [] [] [] free_nonunit a.
Proof. intros f a H. unfold free_nonunit in H. reject_typing. Qed.

Lemma double_free_rejected : forall f a, ~ has_type f [] [] [] double_free a.
Proof. intros f a H. unfold double_free in H. reject_typing. Qed.

Lemma alias_double_free_rejected : forall f a,
  ~ has_type f [] [] [] alias_double_free a.
Proof. intros f a H. unfold alias_double_free in H. reject_typing. Qed.

Lemma affine_leak_linear_rejected : forall a, ~ has_type Linear [] [] [] affine_leak a.
Proof. intros a H. unfold affine_leak in H. reject_typing. Qed.

Lemma sequential_two_refs_typed : forall f,
  has_type f [] [] [] sequential_two_refs
    (TLolli (TRef TUnit) (TLolli (TRef TUnit) TUnit)).
Proof. intros. unfold sequential_two_refs. derive_type. Qed.

Lemma shadowed_resource_affine :
  has_type Affine [] [] [] shadowed_resource (TLolli TNat (TLolli TNat TNat)).
Proof.
  unfold shadowed_resource. apply TyLam, TyLam.
  eapply TyWeak with (U := [true; false]); [derive_type | repeat constructor].
Qed.
Lemma shadowed_resource_linear_rejected : forall a,
  ~ has_type Linear [] [] [] shadowed_resource a.
Proof. intros a H. unfold shadowed_resource in H. reject_typing. Qed.
End RejectedPrograms.

(** ** Classification of the catalog

    All negative examples are closed and lexically well-scoped: their
    rejection is a typing/resource issue, not a missing variable. *)
Section Classification.
Lemma source_examples_scoped :
  Forall (fun p => scoped 0 0 (snd p)) source_examples.
Proof. unfold source_examples. repeat constructor; lia. Qed.

(** Every bundled source program is accounted for in both modes. This
    proposition records proofs; it does not execute a type checker. *)
Definition example_classified (e : term) : Prop :=
  (exists a, has_type Linear [] [] [] e a /\ has_type Affine [] [] [] e a) \/
  ((forall a, ~ has_type Linear [] [] [] e a) /\
    exists a, has_type Affine [] [] [] e a) \/
  (forall f a, ~ has_type f [] [] [] e a).

#[local] Hint Resolve linear_id_typed add_typed add_two_three_typed iter_ref_typed
  curry_typed uncurry_typed sym_ten_typed with_fst_typed counter_typed
  bang_new_twice_typed derelict_typed dig_typed dup_typed del_typed
  closure_ref_typed nested_ref_typed lazy_shared_ref_typed add_effects_typed
  free_in_both_branches_typed sequential_two_refs_typed : example_classification.
#[local] Hint Resolve tensor_fst_affine iter_drops_accumulator_affine
  free_in_one_branch_affine free_in_one_component_affine affine_leak_typed
  tensor_fst_linear_rejected iter_drops_accumulator_linear_rejected
  free_in_one_branch_linear_rejected free_in_one_component_linear_rejected
  affine_leak_linear_rejected shadowed_resource_affine
  shadowed_resource_linear_rejected : example_classification.
#[local] Hint Resolve iter_unboxed_step_rejected iter_mismatched_step_rejected
  iter_mismatched_seed_rejected iter_captures_ref_rejected
  iter_duplicates_accumulator_rejected bang_captures_ref_rejected
  free_after_branch_rejected free_nonunit_rejected double_free_rejected
  alias_double_free_rejected : example_classification.

Lemma source_examples_classified :
  Forall (fun p => example_classified (snd p)) source_examples.
Proof.
  unfold source_examples.
  repeat (apply Forall_cons; [
    cbn [snd]; unfold example_classified;
    first [solve [left; eexists; split; eauto with example_classification] |
      solve [right; left; split; [intros | eexists]; eauto with example_classification] |
      solve [right; right; intros; eauto with example_classification]] | ]).
  constructor.
Qed.

Lemma source_examples_infer_classified :
  Forall (fun p => infer_matches_classification (snd p)) source_examples.
Proof.
  unfold source_examples.
  repeat (apply Forall_cons; [
    cbn [snd infer_matches_classification infer infer_raw merge_leftovers
      finish_binder mask_eqb mask_consume mask_meet ty_eqb
      iter_unboxed_step iter_captures_ref bang_captures_ref
      iter_mismatched_step iter_mismatched_seed iter_duplicates_accumulator
      free_after_branch free_nonunit double_free alias_double_free successor];
    repeat split; try intros; eauto with example_classification | ]).
  all: try constructor.
  - change (forall f a, ~ has_type f [] [] [] iter_unboxed_step a).
    apply iter_unboxed_step_rejected.
  - change (forall f a, ~ has_type f [] [] [] iter_captures_ref a).
    apply iter_captures_ref_rejected.
  - change (forall f a, ~ has_type f [] [] [] bang_captures_ref a).
    apply bang_captures_ref_rejected.
  - change (forall f a, ~ has_type f [] [] [] (iter_mismatched_step 0) a).
    intros f a. apply (iter_mismatched_step_rejected f 0 a).
  - change (forall f a, ~ has_type f [] [] [] (iter_mismatched_seed 0) a).
    intros f a. apply (iter_mismatched_seed_rejected f 0 a).
  - change (forall f a, ~ has_type f [] [] [] (iter_duplicates_accumulator 0) a).
    intros f a. apply (iter_duplicates_accumulator_rejected f 0 a).
  - change (forall f a, ~ has_type f [] [] [] free_after_branch a).
    apply free_after_branch_rejected.
  - change (forall f a, ~ has_type f [] [] [] free_nonunit a).
    apply free_nonunit_rejected.
  - change (forall f a, ~ has_type f [] [] [] double_free a).
    apply double_free_rejected.
  - change (forall f a, ~ has_type f [] [] [] alias_double_free a).
    apply alias_double_free_rejected.
Qed.
End Classification.

(** ** Runtime store examples

    These are proofs of static configurations and a primitive store update,
    not evaluator runs. Concrete address examples use keys 0 and 1. *)
Local Ltac derive_with_loc :=
  first [solve [eapply source_runtime; derive_type] |
    match goal with
    | |- has_type_with_loc _ _ _ _ _ (Loc _) _ => apply TyLoc
    | |- has_type_with_loc _ _ _ _ _ (Lam _ _) _ => apply TyLocLam; derive_with_loc
    | |- has_type_with_loc _ _ _ _ _ (Pair _ _) _ =>
        eapply TyLocPair; [ | | derive_with_loc | derive_with_loc]; repeat constructor
    | |- has_type_with_loc _ _ _ _ _ (LetPair _ _) _ =>
        eapply TyLocLetPair; [ | | derive_with_loc | derive_with_loc]; repeat constructor
    | |- has_type_with_loc _ _ _ _ _ (With _ _) _ => apply TyLocWith; derive_with_loc
    | |- has_type_with_loc _ _ _ _ _ (Swap _ _) _ =>
        eapply TyLocSwap; [ | | derive_with_loc | derive_with_loc]; repeat constructor
    end].

Section StoreExamples.
(** A stored closure owns its own address. Its body is well typed: strong
    update takes out the function, replaces it by unit, frees the reference,
    then calls the old function. No recursive type is needed. *)
Definition cyclic_value : term :=
  Lam TUnit
    (LetPair (Swap (Loc 0) Unit)
      (LetUnit (Free (LVar 0)) (App (LVar 1) (LVar 2)))).
Definition cyclic_store : store := [(0, cyclic_value)].
Definition cyclic_signature : store_sig := [(0, TLolli TUnit TUnit)].

Lemma cyclic_value_typed : forall f,
  has_type_with_loc f [] [] [] cyclic_signature cyclic_value
    (TLolli TUnit TUnit).
Proof. intros. unfold cyclic_value, cyclic_signature. derive_with_loc. Qed.

Lemma cyclic_store_balanced : forall f, store_balance f cyclic_store (Nat 0) TNat.
Proof.
  intros f. eapply StoreBalance with (S := cyclic_signature)
    (Rterm := []) (Rrest := cyclic_signature)
    (Rcells := cyclic_signature) (Rfree := []).
  - repeat constructor; simpl; tauto.
  - eapply CellsCons with (Rc := cyclic_signature) (Rt := []);
      [constructor | apply cyclic_value_typed | repeat constructor | constructor].
  - apply TyLocNat.
  - apply split_right.
  - apply split_left.
  - reflexivity.
Qed.

Lemma cyclic_store_self_edge : store_edge cyclic_store 0 0.
Proof. exists cyclic_value. split; simpl; auto. Qed.

Lemma cyclic_store_not_acyclic : ~ store_acyclic cyclic_store.
Proof. intros H. apply (H 0), PathOne, cyclic_store_self_edge. Qed.

Lemma cyclic_store_rejected : forall f, ~ configuration_typed f cyclic_store (Nat 0) TNat.
Proof. intros f [_ H]. exact (cyclic_store_not_acyclic H). Qed.

(** Valid ownership chain: root -> 1 -> 0. *)
Definition chain_store : store := [(0, Unit); (1, Loc 0)].
Definition chain_signature : store_sig := [(0, TUnit); (1, TRef TUnit)].

Lemma chain_store_acyclic : store_acyclic chain_store.
Proof.
  apply graph_acyclic_rank with (rank := fun l => l).
  intros x y [v [Hin Hy]]. simpl in Hin.
  destruct Hin as [E | [E | []]]; injection E as <- <-; simpl in Hy;
    intuition lia.
Qed.

Lemma chain_configuration : forall f,
  configuration_typed f chain_store (Loc 1) (TRef (TRef TUnit)).
Proof.
  intros f. split; [ | apply chain_store_acyclic].
  eapply StoreBalance with (S := chain_signature)
    (Rterm := [(1, TRef TUnit)]) (Rrest := [(0, TUnit)])
    (Rcells := [(0, TUnit)]) (Rfree := []).
  - repeat constructor; simpl; intuition discriminate.
  - eapply CellsCons with (Rc := []) (Rt := [(0, TUnit)]);
      [constructor | apply TyLocUnit | repeat constructor | ].
    eapply CellsCons with (Rc := [(0, TUnit)]) (Rt := []);
      [constructor | unfold chain_signature; derive_with_loc | repeat constructor | constructor].
  - unfold chain_signature. derive_with_loc.
  - repeat constructor.
  - apply split_left.
  - reflexivity.
Qed.

(** The same address can occur in either lazy component: it has one owner,
    and only the selected component will run. *)
Lemma additive_address_configuration : forall f,
  configuration_typed f [(0, Unit)] (With (Loc 0) (Loc 0))
    (TWith (TRef TUnit) (TRef TUnit)).
Proof.
  intros f. split.
  - eapply StoreBalance with (S := [(0, TUnit)])
      (Rterm := [(0, TUnit)]) (Rrest := []) (Rcells := []) (Rfree := []).
    + repeat constructor; simpl; tauto.
    + eapply CellsCons with (Rc := []) (Rt := []);
        [constructor | apply TyLocUnit | repeat constructor | constructor].
    + derive_with_loc.
    + apply split_left.
    + constructor.
    + reflexivity.
  - apply graph_acyclic_rank with (rank := fun l => l).
    intros x y [v [[E | []] Hy]]. injection E as <- <-. contradiction.
Qed.

(** Strong update changes the content type at the same key: nat becomes
    unit, while the returned old contents retain type nat. *)
Definition swap_before_store : store := [(0, Nat 7)].
Definition swap_after_store : store := natmap_replace 0 Unit swap_before_store.

Lemma swap_before_configuration : forall f,
  configuration_typed f swap_before_store (Swap (Loc 0) Unit) (TTensor TNat (TRef TUnit)).
Proof.
  intros f. split.
  - eapply StoreBalance with (S := [(0, TNat)])
      (Rterm := [(0, TNat)]) (Rrest := []) (Rcells := []) (Rfree := []).
    + repeat constructor; simpl; tauto.
    + eapply CellsCons with (Rc := []) (Rt := []);
        [constructor | apply TyLocNat | repeat constructor | constructor].
    + derive_with_loc.
    + apply split_left.
    + constructor.
    + reflexivity.
  - apply graph_acyclic_rank with (rank := fun l => l).
    intros x y [v [[E | []] Hy]]. injection E as <- <-. contradiction.
Qed.

Lemma swap_after_configuration : forall f,
  configuration_typed f swap_after_store (Pair (Nat 7) (Loc 0)) (TTensor TNat (TRef TUnit)).
Proof.
  intros f. eapply configuration_preservation.
  - apply StepSwapValue; [constructor | reflexivity].
  - apply swap_before_configuration.
Qed.

Lemma dangling_address_rejected : forall f a, ~ store_balance f [] (Loc 0) a.
Proof.
  intros f a H. assert (Hin : In 0 (natmap_domain ([] : store))).
  { eapply balance_allocated; [exact H | left; simpl; auto]. }
  contradiction.
Qed.

Lemma duplicate_store_keys_rejected : forall f e a,
  ~ store_balance f [(0, Unit); (0, Unit)] e a.
Proof.
  intros f e a H. apply balance_unique_addresses in H. inversion H; subst.
  apply H2. simpl; auto.
Qed.

(** A root and a cell cannot both own address 0, even in affine mode. *)
Lemma root_cell_alias_rejected : forall f a,
  ~ store_balance f chain_store (Loc 0) a.
Proof.
  intros f a H. eapply balance_root_no_incoming with (l := 0) (x := 1);
    [exact H | simpl; auto | ].
  exists (Loc 0). simpl; auto.
Qed.

Lemma self_swap_rejected : forall f G L U R a,
  NoDup (natmap_domain R) ->
  ~ has_type_with_loc f G L U R (Swap (Loc 0) (Loc 0)) a.
Proof.
  intros f G L U R a Hnd H. eapply runtime_swap_no_self_reference;
    [exact Hnd | exact H | simpl; auto].
Qed.

(** Affine balance may leave a cell without an owner. *)
Lemma affine_orphan_configuration : configuration_typed Affine [(0, Unit)] (Nat 0) TNat.
Proof.
  split.
  - eapply StoreBalance with (S := [(0, TUnit)])
      (Rterm := []) (Rrest := [(0, TUnit)])
      (Rcells := []) (Rfree := [(0, TUnit)]).
    + repeat constructor; simpl; tauto.
    + eapply CellsCons with (Rc := []) (Rt := []);
        [constructor | apply TyLocUnit | repeat constructor | constructor].
    + apply TyLocNat.
    + apply split_right.
    + apply split_right.
    + discriminate.
  - apply graph_acyclic_rank with (rank := fun l => l).
    intros x y [v [[E | []] Hy]]. injection E as <- <-. contradiction.
Qed.

Lemma linear_orphan_rejected : ~ store_balance Linear [(0, Unit)] (Nat 0) TNat.
Proof.
  intros [S Rt Rr Rc Rf Hnd Hcells Hterm Hsplit Hrest Hmode].
  inversion Hcells; subst.
  match goal with
  | Htail : cells_typed _ _ [] _ |- _ => inversion Htail; subst
  end.
  apply runtime_nat_resources in Hterm. destruct Hterm as [_ ->].
  match goal with
  | Hunit : has_type_with_loc Linear _ _ _ _ Unit _ |- _ =>
      apply runtime_unit_resources in Hunit; destruct Hunit as [_ ->]
  end.
  specialize (Hmode eq_refl). subst Rf.
  repeat match goal with
  | H : Split _ _ _ |- _ => inversion H; subst; clear H
  end.
Qed.

Lemma promotion_address_rejected : forall f G L U R a,
  ~ has_type_with_loc f G L U R (Bang (Loc 0)) a.
Proof. intros f G L U R a H. apply runtime_bang_no_locations in H. discriminate. Qed.

(** Address 7 occupies position 0 of the signature, not position 7. *)
Lemma sparse_address_configuration : forall f,
  configuration_typed f [(7, Unit)] (Loc 7) (TRef TUnit).
Proof.
  intros f. split.
  - eapply StoreBalance with (S := [(7, TUnit)])
      (Rterm := [(7, TUnit)]) (Rrest := []) (Rcells := []) (Rfree := []).
    + repeat constructor; simpl; tauto.
    + eapply CellsCons with (Rc := []) (Rt := []);
        [constructor | apply TyLocUnit | repeat constructor | constructor].
    + derive_with_loc.
    + apply split_left.
    + constructor.
    + reflexivity.
  - apply graph_acyclic_rank with (rank := fun l => l).
    intros x y [v [[E | []] Hy]]. injection E as <- <-. contradiction.
Qed.
End StoreExamples.

(** ** Runtime metatheory examples

    These small derivations exercise address-aware substitution, direct
    location fragments and typed evaluation contexts. *)
Section RuntimeMetatheoryExamples.

(** Substituting an owned address for a resource variable transfers that
    address right to the reduct. *)
Lemma runtime_substitution_address_example : forall f,
  has_type_with_loc f [] [] [] [(0, TUnit)]
    (subst_l (Loc 0) (Free (LVar 0))) TUnit.
Proof.
  intros f. eapply has_type_with_loc_subst_l with
    (U := []) (V := []) (Rbody := []) (Rarg := [(0, TUnit)])
    (a := TRef TUnit).
  - apply TyLocFree.
    change (has_type_with_loc f [] [TRef TUnit]
      (mask_single 1 0) [] (LVar 0) (TRef TUnit)).
    apply TyLocLVar. reflexivity.
  - apply TyLoc.
  - constructor.
  - apply split_right.
Qed.

(** A term records only the location fragment that it owns. *)
Lemma direct_location_fragment_example : forall f,
  has_type_with_loc f [] [] [] [(1, TUnit)] (Loc 1) (TRef TUnit).
Proof. intros. apply TyLoc. Qed.

Definition free_application_context : eval_context :=
  ECFree (ECAppArg (Lam (TRef TUnit) (LVar 0)) ECHole).

Lemma free_application_context_typed : forall f,
  typed_eval_context f [] [] free_application_context
    [] [(0, TUnit)] (TRef TUnit) [] [(0, TUnit)] TUnit.
Proof.
  intros f. unfold free_application_context. apply TCtxFree.
  eapply TCtxAppArg with
    (U1 := []) (U2 := []) (R1 := []) (R2 := [(0, TUnit)])
    (a := TRef TUnit).
  - constructor.
  - apply TyLocLam.
    change (has_type_with_loc f [] [TRef TUnit]
      (mask_single 1 0) [] (LVar 0) (TRef TUnit)).
    apply TyLocLVar. reflexivity.
  - constructor.
  - constructor.
  - repeat constructor.
Qed.

Lemma free_application_context_filled : forall f,
  has_type_with_loc f [] [] [] [(0, TUnit)]
    (plug free_application_context (Loc 0)) TUnit.
Proof.
  intros f. eapply typed_eval_context_fill.
  - apply free_application_context_typed.
  - apply TyLoc.
Qed.

Lemma nested_context_step_example : forall s,
  small_step (s, New (Succ (Nat 0))) (s, New (Nat 1)).
Proof.
  intros s. change (small_step
    (s, plug (ECNew ECHole) (Succ (Nat 0)))
    (s, plug (ECNew ECHole) (Nat 1))).
  eapply small_step_under_context.
  - repeat constructor.
  - apply StepSuccNat.
Qed.

End RuntimeMetatheoryExamples.

(** ** Executable store checks

    These supplement the configuration proofs after extraction. Allocation
    inserts at the head, uses zero for an empty store and otherwise chooses
    one above the greatest live key. *)
Section StoreChecks.
Definition store_examples : list (string * (store * store)) :=
  [("strong_update", (swap_after_store, [(0, Unit)]));
   ("update_address_key",
     (natmap_replace 7 (Loc 2) [(2, Unit); (7, Nat 3)], [(2, Unit); (7, Loc 2)]));
   ("update_absent_key", (natmap_replace 7 Unit [(2, Nat 3)], [(2, Nat 3)]));
   ("allocate_empty",
     (store_insert (fresh []) (Nat 4) [], [(0, Nat 4)]));
   ("allocate_above_max",
     (store_insert (fresh [(2, Unit); (7, Nat 3)]) (Bool true)
       [(2, Unit); (7, Nat 3)],
      [(8, Bool true); (2, Unit); (7, Nat 3)]));
   ("remove_key",
     (store_remove 7 [(2, Unit); (7, Nat 3)], [(2, Unit)]));
   ("remove_absent_key",
     (store_remove 7 [(2, Nat 3)], [(2, Nat 3)]))].

Lemma store_examples_correct :
  Forall (fun p => fst (snd p) = snd (snd p)) store_examples.
Proof. repeat constructor. Qed.

Definition location_examples : list (string * (list nat * list nat)) :=
  [("closure_self_reference", (locations cyclic_value, [0]));
   ("suspended_addresses",
     (locations (With (Bang (Loc 7)) (Lam TUnit (Loc 2))), [7; 2]))].

Lemma location_examples_correct :
  Forall (fun p => fst (snd p) = snd (snd p)) location_examples.
Proof. repeat constructor. Qed.
End StoreChecks.

(** ** Named source programs and lexical shadowing *)
Section NamedPrograms.
Definition named_id : named_term := NLam "x" TNat (NVar "x").

Definition named_add : named_term :=
  NLam "m" TNat (NLam "n" TNat
    (NIter (NVar "n") (NBang (NLam "acc" TNat (NSucc (NVar "acc")))) (NVar "m"))).

Definition named_counter : named_term :=
  NApp
    (NLam "r" (TRef TNat)
      (NLetPair "old" "r" (NSwap (NVar "r") (NNat 1))
        (NLetPair "last" "r" (NSwap (NVar "r") NUnit)
          (NLetUnit (NFree (NVar "r"))
            (NApp (NApp named_add (NVar "old")) (NVar "last"))))))
    (NNew (NNat 0)).

Definition named_shadow : named_term := NLam "x" TNat (NLam "x" TNat (NVar "x")).

Definition named_bad_iter : named_term :=
  NIter (NNat 2) (NLam "x" TNat (NSucc (NVar "x"))) (NNat 0).

Definition named_double_free : named_term :=
  NLam "r" (TRef TUnit) (NLetUnit (NFree (NVar "r")) (NFree (NVar "r"))).

Definition resolution_examples : list (string * (option term * option term)) :=
  [ ("named_id", (resolve [] named_id, Some (linear_id TNat)));
    ("named_add", (resolve [] named_add, Some add));
    ("named_counter", (resolve [] named_counter, Some counter));
    ("same_zone_shadow", (resolve [] named_shadow, Some shadowed_resource));
    ("independent_zone_indices",
      (resolve [("l0", Resource); ("u0", Shared); ("l1", Resource); ("u1", Shared)]
         (NPair (NVar "l1") (NVar "u1")), Some (Pair (LVar 1) (UVar 1))));
    ("resource_shadows_shared",
      (resolve [] (NLetBang "x" (NBang (NNat 5)) (NLam "x" TBool (NVar "x"))),
       Some (LetBang (Bang (Nat 5)) (Lam TBool (LVar 0)))));
    ("shared_shadows_resource",
      (resolve [] (NLam "x" TNat (NLetBang "x" (NBang (NNat 7)) (NVar "x"))),
       Some (Lam TNat (LetBang (Bang (Nat 7)) (UVar 0)))));
    ("separate_zone_binders",
      (resolve [] (NLetBang "u" (NBang (NNat 5))
         (NLam "x" TNat (NPair (NVar "x") (NVar "u")))),
       Some (LetBang (Bang (Nat 5)) (Lam TNat (Pair (LVar 0) (UVar 0))))));
    ("pair_binding_order",
      (resolve [] (NLam "p" (TTensor TNat TBool)
         (NLetPair "x" "y" (NVar "p") (NPair (NVar "x") (NVar "y")))),
       Some (Lam (TTensor TNat TBool) (LetPair (LVar 0) (Pair (LVar 1) (LVar 0))))));
    ("repeated_pair_binder",
      (resolve [] (NLetPair "x" "x" (NPair (NNat 0) (NBool true)) (NVar "x")),
       Some (LetPair (Pair (Nat 0) (Bool true)) (LVar 0))));
    ("pair_names_not_in_rhs",
      (resolve [] (NLetPair "x" "y" (NPair (NNat 0) (NVar "y")) (NVar "x")), None));
    ("shared_name_not_in_rhs",
      (resolve [] (NLetBang "u" (NBang (NVar "u")) (NVar "u")), None));
    ("binder_does_not_escape",
      (resolve [] (NPair (NLam "x" TNat (NVar "x")) (NVar "x")), None));
    ("unbound_name", (resolve [] (NVar "missing"), None));
    ("unbound_in_thunk", (resolve [] (NBang (NVar "missing")), None));
    ("unbound_in_lazy_pair", (resolve [] (NWith NUnit (NVar "missing")), None));
    ("unbound_in_zero_iterator",
      (resolve [] (NIter (NNat 0) (NBang (NVar "missing")) (NNat 3)), None));
    ("ill_typed_but_resolved", (resolve [] named_bad_iter, Some iter_unboxed_step));
    ("repeated_use_keeps_index", (resolve [] named_double_free, Some double_free)) ].

Lemma resolution_examples_correct :
  Forall (fun p => fst (snd p) = snd (snd p)) resolution_examples.
Proof. repeat constructor. Qed.

(** Typing is checked on the core produced by resolution. *)
Example named_id_typed : forall f,
  Exists_opt (fun t => has_type f [] [] [] t (TLolli TNat TNat)) (resolve [] named_id).
Proof. intros f. exact (linear_id_typed f [] [] TNat). Qed.

Example named_add_typed : forall f,
  Exists_opt (fun t => has_type f [] [] [] t (TLolli TNat (TLolli TNat TNat)))
    (resolve [] named_add).
Proof. intros f. exact (add_typed f). Qed.

Example named_counter_typed : forall f,
  Exists_opt (fun t => has_type f [] [] [] t TNat) (resolve [] named_counter).
Proof. intros f. exact (counter_typed f). Qed.

Example named_shadow_affine :
  Exists_opt (fun t => has_type Affine [] [] [] t (TLolli TNat (TLolli TNat TNat)))
    (resolve [] named_shadow).
Proof. exact shadowed_resource_affine. Qed.

Example named_shadow_linear_rejected : forall t a,
  In_opt t (resolve [] named_shadow) -> ~ has_type Linear [] [] [] t a.
Proof.
  intros t a Hr. apply In_opt_eq_Some in Hr. injection Hr as <-. apply shadowed_resource_linear_rejected.
Qed.

Example named_bad_iter_rejected : forall f t a,
  In_opt t (resolve [] named_bad_iter) -> ~ has_type f [] [] [] t a.
Proof.
  intros f t a Hr. apply In_opt_eq_Some in Hr. injection Hr as <-. apply iter_unboxed_step_rejected.
Qed.

Example named_double_free_rejected : forall f t a,
  In_opt t (resolve [] named_double_free) -> ~ has_type f [] [] [] t a.
Proof.
  intros f t a Hr. apply In_opt_eq_Some in Hr. injection Hr as <-. apply double_free_rejected.
Qed.

(** An unavailable shadowing resource does not reveal the older binding. *)
Example consumed_shadow_stays_hidden : forall f t a,
  In_opt t (resolve [("x", Resource); ("x", Resource)] (NVar "x")) ->
  ~ has_type f [] [TBool; TNat] [false; true] t a.
Proof.
  intros f t a Hr H. apply In_opt_eq_Some in Hr. injection Hr as <-.
  apply typing_lvar_available in H. discriminate.
Qed.

Example alpha_renamed_binders_resolve_equally :
  resolve [] (NLam "x" TNat (NVar "x")) = resolve [] (NLam "y" TNat (NVar "y")).
Proof. reflexivity. Qed.
End NamedPrograms.
