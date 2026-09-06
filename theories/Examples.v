(** * Example programs

    Terms are written directly as core AST until name resolution exists.
    Typing and evaluation of these examples are established in later modules;
    here only the syntactic invariants are checked. *)

From Stdlib Require Import List String.
From DILLref Require Import Ty Syntax.
Import ListNotations.
Open Scope string_scope.

(** [λx:A. x] *)
Definition linear_id (a : ty) : term := Lam a (LVar 0).

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
          (LetUnit (Free (LVar 0)) (Plus (LVar 3) (LVar 1))))))
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

Definition source_examples : list (string * term) :=
  [ ("linear_id", linear_id TNat);
    ("curry", curry TNat TBool TUnit);
    ("uncurry", uncurry TNat TBool TUnit);
    ("sym_ten", sym_ten TNat TBool);
    ("with_fst", with_fst TNat TBool);
    ("tensor_fst", tensor_fst TNat TBool);
    ("counter", counter);
    ("bang_new_twice", bang_new_twice);
    ("bang_captures_ref", bang_captures_ref);
    ("affine_leak", affine_leak) ].

Example source_examples_loc_free :
  forallb (fun p => loc_free (snd p)) source_examples = true.
Proof. reflexivity. Qed.

(** TODO: typing derivations, checker results in both modes, and evaluation
    traces with final stores for every example above. *)
