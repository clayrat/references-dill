(** * Lexical scope for the two independent variable zones

    [scoped g l e] bounds shared indices by [g] and resource indices by [l].
    It does not track consumption: a used position remains in scope.
    Addresses have no lexical scope, so [Loc] is admitted here; source
    validity additionally requires [loc_free e = true]. *)

From Stdlib Require Import Arith Lia.
From DILLref Require Import Ty Syntax.

Inductive scoped : nat -> nat -> term -> Prop :=
  | ScopeLVar : forall g l i, i < l -> scoped g l (LVar i)
  | ScopeUVar : forall g l i, i < g -> scoped g l (UVar i)
  | ScopeLoc : forall g l a, scoped g l (Loc a)
  | ScopeLam : forall g l a e,
      scoped g (S l) e -> scoped g l (Lam a e)
  | ScopeApp : forall g l e1 e2,
      scoped g l e1 -> scoped g l e2 -> scoped g l (App e1 e2)
  | ScopeUnit : forall g l, scoped g l Unit
  | ScopeLetUnit : forall g l e1 e2,
      scoped g l e1 -> scoped g l e2 -> scoped g l (LetUnit e1 e2)
  | ScopePair : forall g l e1 e2,
      scoped g l e1 -> scoped g l e2 -> scoped g l (Pair e1 e2)
  | ScopeLetPair : forall g l e1 e2,
      scoped g l e1 -> scoped g (S (S l)) e2 -> scoped g l (LetPair e1 e2)
  | ScopeWith : forall g l e1 e2,
      scoped g l e1 -> scoped g l e2 -> scoped g l (With e1 e2)
  | ScopeFst : forall g l e, scoped g l e -> scoped g l (Fst e)
  | ScopeSnd : forall g l e, scoped g l e -> scoped g l (Snd e)
  | ScopeBang : forall g l e, scoped g l e -> scoped g l (Bang e)
  | ScopeLetBang : forall g l e1 e2,
      scoped g l e1 -> scoped (S g) l e2 -> scoped g l (LetBang e1 e2)
  | ScopeNat : forall g l n, scoped g l (Nat n)
  | ScopeSucc : forall g l e, scoped g l e -> scoped g l (Succ e)
  | ScopeIter : forall g l c s z,
      scoped g l c -> scoped g l s -> scoped g l z -> scoped g l (Iter c s z)
  | ScopeBool : forall g l b, scoped g l (Bool b)
  | ScopeIf : forall g l c e1 e2,
      scoped g l c -> scoped g l e1 -> scoped g l e2 -> scoped g l (If c e1 e2)
  | ScopeNew : forall g l e, scoped g l e -> scoped g l (New e)
  | ScopeSwap : forall g l e1 e2,
      scoped g l e1 -> scoped g l e2 -> scoped g l (Swap e1 e2)
  | ScopeFree : forall g l e, scoped g l e -> scoped g l (Free e).

(** Enlarging the bounds appends scope positions beyond existing indices;
    inserting a binder at the front instead requires renaming. *)
Lemma scoped_mono : forall g l e,
  scoped g l e -> forall g' l', g <= g' -> l <= l' -> scoped g' l' e.
Proof.
  intros g l e H. induction H; intros g' l' Hg Hl;
    constructor; eauto; try lia.
  - apply IHscoped; lia.
  - apply IHscoped2; lia.
  - apply IHscoped2; lia.
Qed.
