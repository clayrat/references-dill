(** * Lexical name resolution

    Search stops at the nearest binder, regardless of its zone. Passing
    another binder increments only the index for that binder's zone.
    Resolution does not consult resource availability or check types.
    [None] reports an unbound name, including inside suspended code. *)

From Stdlib Require Import String List Arith Lia.
From DILLref Require Import Prelude Ty Syntax NamedSyntax Scoping.
Import ListNotations.

Fixpoint find_name (x : string) (E : name_scope) : option (zone * nat) :=
  match E with
  | [] => None
  | (y, w) :: rest =>
      if String.eqb x y then Some (w, 0)
      else match find_name x rest with
        | Some (z, i) => Some (z, shift_zone w z i)
        | None => None
        end
  end.

(** The inequality prevents skipping a shadowing binder. *)
Inductive name_at : name_scope -> string -> zone -> nat -> Prop :=
  | NameHere : forall E x z, name_at ((x, z) :: E) x z 0
  | NameThere : forall E x y z w i,
      x <> y -> name_at E x z i ->
      name_at ((y, w) :: E) x z (shift_zone w z i).

Lemma find_name_sound : forall E x z i,
  In_opt (z, i) (find_name x E) -> name_at E x z i.
Proof.
  induction E as [| [y w] E IH]; intros x z i H; simpl in H; try contradiction.
  destruct (String.eqb x y) eqn:Heq.
  - apply String.eqb_eq in Heq. subst y. simpl in H. injection H as -> ->.
    constructor.
  - destruct (find_name x E) as [[v j] | ] eqn:Hfind; simpl in H; try contradiction.
    injection H as -> ->. constructor.
    + apply String.eqb_neq. exact Heq.
    + apply IH, In_opt_eq_Some. exact Hfind.
Qed.

Lemma find_name_complete : forall E x z i,
  name_at E x z i -> In_opt (z, i) (find_name x E).
Proof.
  intros E x z i H. induction H; simpl.
  - rewrite String.eqb_refl. reflexivity.
  - apply String.eqb_neq in H. apply In_opt_eq_Some in IHname_at.
    rewrite H, IHname_at. reflexivity.
Qed.

Lemma name_at_bound : forall E x z i,
  name_at E x z i -> i < scope_size z E.
Proof.
  intros E x z i H. induction H; simpl.
  - destruct z; simpl; lia.
  - destruct w, z; simpl in *; lia.
Qed.

Fixpoint resolve (E : name_scope) (e : named_term) : option term :=
  match e with
  | NVar x => match find_name x E with
      | Some (Resource, i) => Some (LVar i)
      | Some (Shared, i) => Some (UVar i)
      | None => None
      end
  | NLam x a body => option_map (Lam a) (resolve ((x, Resource) :: E) body)
  | NApp e1 e2 => match resolve E e1, resolve E e2 with
      | Some t1, Some t2 => Some (App t1 t2) | _, _ => None end
  | NUnit => Some Unit
  | NLetUnit e1 e2 => match resolve E e1, resolve E e2 with
      | Some t1, Some t2 => Some (LetUnit t1 t2) | _, _ => None end
  | NPair e1 e2 => match resolve E e1, resolve E e2 with
      | Some t1, Some t2 => Some (Pair t1 t2) | _, _ => None end
  | NLetPair x y e1 e2 =>
      match resolve E e1, resolve ((y, Resource) :: (x, Resource) :: E) e2 with
      | Some t1, Some t2 => Some (LetPair t1 t2) | _, _ => None end
  | NWith e1 e2 => match resolve E e1, resolve E e2 with
      | Some t1, Some t2 => Some (With t1 t2) | _, _ => None end
  | NFst e => option_map Fst (resolve E e)
  | NSnd e => option_map Snd (resolve E e)
  | NBang e => option_map Bang (resolve E e)
  | NLetBang x e1 e2 => match resolve E e1, resolve ((x, Shared) :: E) e2 with
      | Some t1, Some t2 => Some (LetBang t1 t2) | _, _ => None end
  | NNat n => Some (Nat n)
  | NSucc e => option_map Succ (resolve E e)
  | NIter c s z => match resolve E c, resolve E s, resolve E z with
      | Some tc, Some ts, Some tz => Some (Iter tc ts tz) | _, _, _ => None end
  | NBool b => Some (Bool b)
  | NIf c e1 e2 => match resolve E c, resolve E e1, resolve E e2 with
      | Some tc, Some t1, Some t2 => Some (If tc t1 t2) | _, _, _ => None end
  | NNew e => option_map New (resolve E e)
  | NSwap e1 e2 => match resolve E e1, resolve E e2 with
      | Some t1, Some t2 => Some (Swap t1 t2) | _, _ => None end
  | NFree e => option_map Free (resolve E e)
  end.

(** Declarative correspondence, independent of the resolving function. *)
Inductive resolves : name_scope -> named_term -> term -> Prop :=
  | ResolveLVar : forall E x i, name_at E x Resource i -> resolves E (NVar x) (LVar i)
  | ResolveUVar : forall E x i, name_at E x Shared i -> resolves E (NVar x) (UVar i)
  | ResolveLam : forall E x a e t,
      resolves ((x, Resource) :: E) e t -> resolves E (NLam x a e) (Lam a t)
  | ResolveApp : forall E e1 e2 t1 t2,
      resolves E e1 t1 -> resolves E e2 t2 -> resolves E (NApp e1 e2) (App t1 t2)
  | ResolveUnit : forall E, resolves E NUnit Unit
  | ResolveLetUnit : forall E e1 e2 t1 t2,
      resolves E e1 t1 -> resolves E e2 t2 -> resolves E (NLetUnit e1 e2) (LetUnit t1 t2)
  | ResolvePair : forall E e1 e2 t1 t2,
      resolves E e1 t1 -> resolves E e2 t2 -> resolves E (NPair e1 e2) (Pair t1 t2)
  | ResolveLetPair : forall E x y e1 e2 t1 t2,
      resolves E e1 t1 -> resolves ((y, Resource) :: (x, Resource) :: E) e2 t2 ->
      resolves E (NLetPair x y e1 e2) (LetPair t1 t2)
  | ResolveWith : forall E e1 e2 t1 t2,
      resolves E e1 t1 -> resolves E e2 t2 -> resolves E (NWith e1 e2) (With t1 t2)
  | ResolveFst : forall E e t, resolves E e t -> resolves E (NFst e) (Fst t)
  | ResolveSnd : forall E e t, resolves E e t -> resolves E (NSnd e) (Snd t)
  | ResolveBang : forall E e t, resolves E e t -> resolves E (NBang e) (Bang t)
  | ResolveLetBang : forall E x e1 e2 t1 t2,
      resolves E e1 t1 -> resolves ((x, Shared) :: E) e2 t2 ->
      resolves E (NLetBang x e1 e2) (LetBang t1 t2)
  | ResolveNat : forall E n, resolves E (NNat n) (Nat n)
  | ResolveSucc : forall E e t, resolves E e t -> resolves E (NSucc e) (Succ t)
  | ResolveIter : forall E c s z tc ts tz,
      resolves E c tc -> resolves E s ts -> resolves E z tz ->
      resolves E (NIter c s z) (Iter tc ts tz)
  | ResolveBool : forall E b, resolves E (NBool b) (Bool b)
  | ResolveIf : forall E c e1 e2 tc t1 t2,
      resolves E c tc -> resolves E e1 t1 -> resolves E e2 t2 ->
      resolves E (NIf c e1 e2) (If tc t1 t2)
  | ResolveNew : forall E e t, resolves E e t -> resolves E (NNew e) (New t)
  | ResolveSwap : forall E e1 e2 t1 t2,
      resolves E e1 t1 -> resolves E e2 t2 -> resolves E (NSwap e1 e2) (Swap t1 t2)
  | ResolveFree : forall E e t, resolves E e t -> resolves E (NFree e) (Free t).

Lemma resolve_sound : forall e E t, In_opt t (resolve E e) -> resolves E e t.
Proof.
  induction e; intros E core H; simpl in H;
    repeat match type of H with
    | context [find_name ?x ?E] => destruct (find_name x E) as [[[] i] | ] eqn:?
    | context [resolve ?E ?e] => destruct (resolve E e) eqn:?
    end; simpl in H; try contradiction; subst core;
    repeat match goal with Heq : _ = Some _ |- _ => apply In_opt_eq_Some in Heq end;
    constructor; eauto using find_name_sound.
Qed.

Lemma resolve_complete : forall E e t, resolves E e t -> In_opt t (resolve E e).
Proof.
  intros E e t H. induction H; simpl;
    repeat match goal with IH : In_opt _ _ |- _ => apply In_opt_eq_Some in IH end;
    rewrite ?IHresolves, ?IHresolves1, ?IHresolves2, ?IHresolves3;
    try reflexivity;
    rewrite (proj1 (In_opt_eq_Some _ _) (find_name_complete _ _ _ _ H)); reflexivity.
Qed.

Lemma resolve_iff : forall E e t, In_opt t (resolve E e) <-> resolves E e t.
Proof. split; [apply resolve_sound | apply resolve_complete]. Qed.

Lemma resolves_scoped : forall E e t,
  resolves E e t -> scoped (scope_size Shared E) (scope_size Resource E) t.
Proof.
  intros E e t H. induction H; constructor; simpl in *;
    eauto using name_at_bound.
Qed.

Lemma resolves_loc_free : forall E e t, resolves E e t -> loc_free t = true.
Proof.
  intros E e t H. induction H; simpl;
    rewrite ?IHresolves, ?IHresolves1, ?IHresolves2, ?IHresolves3; reflexivity.
Qed.

Lemma resolve_source : forall E e t, In_opt t (resolve E e) ->
  scoped (scope_size Shared E) (scope_size Resource E) t /\ loc_free t = true.
Proof.
  intros E e t H. apply resolve_sound in H.
  split; eauto using resolves_scoped, resolves_loc_free.
Qed.
