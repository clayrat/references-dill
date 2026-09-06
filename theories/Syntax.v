(** * Core syntax of DILLref

    The core is an ordinary de Bruijn AST. Resource variables and shared
    variables are indexed independently: [LVar i] refers to position [i] of
    the resource scope, [UVar i] to position [i] of the shared scope. Both
    scopes are lists of types kept separately from the term.

    Binding conventions (innermost binder has index 0):
    - [Lam a e] extends the resource scope with [a];
    - [LetPair e1 e2] on a pair of type [A ⊗ B] extends the resource scope with
      [B] at index 0 and [A] at index 1;
    - [LetBang e1 e2] extends only the shared scope, with the unbanged type
      at index 0;
    - [LetUnit] and [If] bind nothing.

    A consumed resource position is never removed from the scope by the
    checker: the scope stays fixed and a separate availability mask records
    consumption, so the remaining indices keep their meaning.

    [Loc l] is a runtime store address. It is not a binding index, it is
    untouched by renaming and substitution, and it is rejected in source
    programs: [loc_free] is a precondition of the user-facing checker. *)

From Stdlib Require Import Bool.
From DILLref Require Import Ty.

(** Linear mode forbids weakening of resource hypotheses; affine mode allows
    a resource to be left unused. Neither mode admits contraction in the
    resource zone. The flag never affects evaluation. *)
Inductive flag : Type :=
  | Linear : flag
  | Affine : flag.

Inductive term : Type :=
  (** Variables and addresses *)
  | LVar : nat -> term                    (** resource variable *)
  | UVar : nat -> term                    (** shared variable *)
  | Loc : nat -> term                     (** store address, runtime only *)
  (** Linear functions [A ⊸ B] *)
  | Lam : ty -> term -> term              (** [λx:A. e] *)
  | App : term -> term -> term
  (** Multiplicative unit and pair: [unit], [A ⊗ B] *)
  | Unit : term                           (** [()] *)
  | LetUnit : term -> term -> term        (** [let () = e1 in e2] *)
  | Pair : term -> term -> term           (** [(e1, e2)] *)
  | LetPair : term -> term -> term        (** [let (x, y) = e1 in e2] *)
  (** Additive pair [A & B] *)
  | With : term -> term -> term           (** [⟨e1, e2⟩], lazy *)
  | Fst : term -> term
  | Snd : term -> term
  (** Modality [!A] *)
  | Bang : term -> term                   (** [!e], a thunk *)
  | LetBang : term -> term -> term        (** [let !u = e1 in e2] *)
  (** Base types [nat] and [bool] *)
  | Nat : nat -> term
  | Plus : term -> term -> term
  | Bool : bool -> term
  | If : term -> term -> term -> term
  (** References [ref A] *)
  | New : term -> term                    (** [A ⊸ ref A] *)
  | Swap : term -> term -> term           (** [ref A ⊸ B ⊸ A ⊗ ref B] *)
  | Free : term -> term.                  (** [ref unit ⊸ unit] *)

(** Source programs contain no addresses. *)
Fixpoint loc_free (e : term) : bool :=
  match e with
  | LVar _ | UVar _ | Unit | Nat _ | Bool _ => true
  | Loc _ => false
  | Lam _ e | Fst e | Snd e | Bang e | New e | Free e => loc_free e
  | App e1 e2 | LetUnit e1 e2 | Pair e1 e2 | LetPair e1 e2 | With e1 e2
  | LetBang e1 e2 | Plus e1 e2 | Swap e1 e2 => loc_free e1 && loc_free e2
  | If c e1 e2 => loc_free c && loc_free e1 && loc_free e2
  end.

(** TODO: named surface syntax and name resolution into this core, with
    lexical shadowing and a correctness statement relating the named judgment
    to the indexed one. *)
