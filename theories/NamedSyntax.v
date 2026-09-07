(** * Named source terms

    A single variable form uses lexical shadowing across both zones. The
    nearest binder determines the zone, whose de Bruijn indices are counted
    independently. [NLam] binds a resource; [NLetBang] binds a shared name.
    [NLetPair x y] binds [x] and then [y], so [y] is innermost, including
    when both names are equal. Binders scope only over their bodies.

    There is no address constructor in the source language. *)

From Stdlib Require Import String List.
From DILLref Require Import Ty.

Inductive zone : Type := Shared | Resource.

Definition name_scope : Type := list (string * zone).

Definition shift_zone (binder variable : zone) (i : nat) : nat :=
  match binder, variable with
  | Shared, Shared | Resource, Resource => S i
  | _, _ => i
  end.

Fixpoint scope_size (z : zone) (E : name_scope) : nat :=
  match E with
  | nil => 0
  | (_, w) :: rest => shift_zone w z (scope_size z rest)
  end.

Inductive named_term : Type :=
  | NVar : string -> named_term
  | NLam : string -> ty -> named_term -> named_term
  | NApp : named_term -> named_term -> named_term
  | NUnit : named_term
  | NLetUnit : named_term -> named_term -> named_term
  | NPair : named_term -> named_term -> named_term
  | NLetPair : string -> string -> named_term -> named_term -> named_term
  | NWith : named_term -> named_term -> named_term
  | NFst : named_term -> named_term
  | NSnd : named_term -> named_term
  | NBang : named_term -> named_term
  | NLetBang : string -> named_term -> named_term -> named_term
  | NNat : nat -> named_term
  | NSucc : named_term -> named_term
  | NIter : named_term -> named_term -> named_term -> named_term
  | NBool : bool -> named_term
  | NIf : named_term -> named_term -> named_term -> named_term
  | NNew : named_term -> named_term
  | NSwap : named_term -> named_term -> named_term
  | NFree : named_term -> named_term.
