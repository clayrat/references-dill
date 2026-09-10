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
    - [LetUnit], [If] and [Iter] bind nothing.

    A consumed resource position is never removed from the scope by the
    checker: the scope stays fixed and a separate availability mask records
    consumption, so the remaining indices keep their meaning.

    [Loc l] is a runtime store address. It is not a binding index, it is
    untouched by renaming and substitution, and it is rejected in source
    programs: [loc_free] is a precondition of the user-facing checker.

    Natural numbers use literals [Nat n], a strict successor [Succ e], and
    a fully applied linear iterator [Iter count step seed] with argument
    types [nat], [!(A ⊸ A)] and [A] and result [A]. The three arguments
    divide the resource context; the step thunk is re-evaluated at each
    iteration and only the accumulator carries resources between iterations.
    Addition is a derived program. Operational rules for [Succ] and [Iter]
    use the same store semantics as the other strict constructs. *)

From Stdlib Require Import Bool List.
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
  | Succ : term -> term                   (** strict successor *)
  | Iter : term -> term -> term -> term  (** count, boxed step, seed *)
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
  | Lam _ e | Fst e | Snd e | Bang e | Succ e | New e | Free e => loc_free e
  | App e1 e2 | LetUnit e1 e2 | Pair e1 e2 | LetPair e1 e2 | With e1 e2
  | LetBang e1 e2 | Swap e1 e2 => loc_free e1 && loc_free e2
  | If c e1 e2 | Iter c e1 e2 => loc_free c && loc_free e1 && loc_free e2
  end.

(** Runtime values. Lambda bodies, promotion bodies and additive components
    are suspended; multiplicative pairs evaluate both components. *)
Inductive value : term -> Prop :=
  | ValueLoc : forall l, value (Loc l)
  | ValueLam : forall a e, value (Lam a e)
  | ValueUnit : value Unit
  | ValuePair : forall e1 e2, value e1 -> value e2 -> value (Pair e1 e2)
  | ValueWith : forall e1 e2, value (With e1 e2)
  | ValueBang : forall e, value (Bang e)
  | ValueNat : forall n, value (Nat n)
  | ValueBool : forall b, value (Bool b).

(** Address occurrences include suspended bodies. Membership is used as a
    set of edges: repeated occurrences in additive branches are not distinct
    ownership rights. Multiplicative disjointness is a typing condition. *)
Fixpoint locations (e : term) : list nat :=
  match e with
  | Loc l => cons l nil
  | LVar _ | UVar _ | Unit | Nat _ | Bool _ => nil
  | Lam _ e | Fst e | Snd e | Bang e | Succ e | New e | Free e => locations e
  | App e1 e2 | LetUnit e1 e2 | Pair e1 e2 | LetPair e1 e2 | With e1 e2
  | LetBang e1 e2 | Swap e1 e2 => List.app (locations e1) (locations e2)
  | If c e1 e2 | Iter c e1 e2 =>
      List.app (locations c) (List.app (locations e1) (locations e2))
  end.
