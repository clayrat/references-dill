(** * Types of DILLref

    The same grammar of types is used in both context zones. Whether a
    hypothesis may be copied or dropped is a property of the zone it lives in,
    not of its type; [TBang] is the only way to move a value from the resource
    zone into the shared zone. *)

From Stdlib Require Import Bool.

Inductive ty : Type :=
  | TUnit : ty
  | TNat : ty
  | TBool : ty
  | TLolli : ty -> ty -> ty     (** linear function [A ⊸ B] *)
  | TTensor : ty -> ty -> ty    (** multiplicative pair [A ⊗ B] *)
  | TWith : ty -> ty -> ty      (** additive (lazy) pair [A & B] *)
  | TBang : ty -> ty            (** [!A]: shareable thunk *)
  | TRef : ty -> ty.            (** [ref A]: exclusive right to a cell *)

Fixpoint ty_eqb (a b : ty) : bool :=
  match a, b with
  | TUnit, TUnit | TNat, TNat | TBool, TBool => true
  | TLolli a1 b1, TLolli a2 b2
  | TTensor a1 b1, TTensor a2 b2
  | TWith a1 b1, TWith a2 b2 => ty_eqb a1 a2 && ty_eqb b1 b2
  | TBang a1, TBang a2 | TRef a1, TRef a2 => ty_eqb a1 a2
  | _, _ => false
  end.

Lemma ty_eqb_refl : forall a, ty_eqb a a = true.
Proof.
  induction a; simpl; auto; rewrite IHa1, IHa2; reflexivity.
Qed.

Lemma ty_eqb_eq : forall a b, ty_eqb a b = true -> a = b.
Proof.
  induction a; destruct b; simpl; intros H; try discriminate; auto;
    try (apply andb_true_iff in H; destruct H as [H1 H2];
         rewrite (IHa1 _ H1), (IHa2 _ H2); reflexivity);
    rewrite (IHa _ H); reflexivity.
Qed.

Lemma ty_eqb_iff : forall a b, ty_eqb a b = true <-> a = b.
Proof.
  split; [apply ty_eqb_eq | intros ->; apply ty_eqb_refl].
Qed.

Lemma ty_eq_dec : forall a b : ty, {a = b} + {a <> b}.
Proof.
  intros a b. destruct (ty_eqb a b) eqn:E.
  - left. apply ty_eqb_eq, E.
  - right. intros ->. rewrite ty_eqb_refl in E. discriminate.
Qed.
