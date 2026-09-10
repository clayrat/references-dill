(** * Finite stores, signatures and reference graphs

    Addresses are natural-number keys, independent of list positions. A
    signature gives each cell's content type; its corresponding address has
    reference type. Uniqueness and matching domains are required by store
    balance, rather than built into the executable representation. *)

From Stdlib Require Import List Arith Bool.
From DILLref Require Import Ty Syntax NatMap Graph.
Import ListNotations.

Definition store : Type := NatMap term.
Definition store_sig : Type := NatMap ty.

(** ** Executable store operations

    Allocation adds a fresh entry at the head. Updating preserves every key
    and position. Removal deletes every matching key; uniqueness makes this a
    single-cell operation on well-formed stores. Signature operations use the
    same list transformations so their domains remain synchronized. *)

Definition fresh (s : store) : nat := natmap_fresh s.

Definition store_insert (l : nat) (v : term) (s : store) : store :=
  natmap_insert l v s.
Definition store_update (l : nat) (v : term) (s : store) : store :=
  natmap_replace l v s.
Definition store_remove (l : nat) (s : store) : store :=
  natmap_remove l s.

Definition store_sig_insert (l : nat) (a : ty) (S : store_sig) : store_sig :=
  natmap_insert l a S.
Definition store_sig_update (l : nat) (a : ty) (S : store_sig) : store_sig :=
  natmap_replace l a S.
Definition store_sig_remove (l : nat) (S : store_sig) : store_sig :=
  natmap_remove l S.

Lemma fresh_empty : fresh [] = 0.
Proof. reflexivity. Qed.

Lemma fresh_nonempty : forall s,
  s <> [] -> fresh s = S (natmap_max_key s).
Proof. apply natmap_fresh_nonempty. Qed.

Lemma fresh_not_allocated : forall s,
  ~ In (fresh s) (natmap_domain s).
Proof. apply natmap_fresh_not_in. Qed.

Lemma fresh_lookup : forall s, natmap_lookup (fresh s) s = None.
Proof. apply natmap_lookup_fresh. Qed.

Lemma store_insert_domain : forall l v s,
  natmap_domain (store_insert l v s) = l :: natmap_domain s.
Proof. apply natmap_insert_domain. Qed.

Lemma store_update_domain : forall l v s,
  natmap_domain (store_update l v s) = natmap_domain s.
Proof. apply natmap_replace_domain. Qed.

Lemma store_remove_domain : forall l s,
  natmap_domain (store_remove l s) =
    filter (fun k => negb (Nat.eqb l k)) (natmap_domain s).
Proof. apply natmap_remove_domain. Qed.

Lemma store_sig_insert_domain : forall l a S,
  natmap_domain (store_sig_insert l a S) = l :: natmap_domain S.
Proof. apply natmap_insert_domain. Qed.

Lemma store_sig_update_domain : forall l a S,
  natmap_domain (store_sig_update l a S) = natmap_domain S.
Proof. apply natmap_replace_domain. Qed.

Lemma store_sig_remove_domain : forall l S,
  natmap_domain (store_sig_remove l S) =
    filter (fun k => negb (Nat.eqb l k)) (natmap_domain S).
Proof. apply natmap_remove_domain. Qed.

Lemma store_insert_fresh_nodup : forall v s,
  NoDup (natmap_domain s) ->
  NoDup (natmap_domain (store_insert (fresh s) v s)).
Proof. apply natmap_insert_fresh_nodup. Qed.

Lemma store_sig_insert_domains : forall s S l v a,
  natmap_domain s = natmap_domain S ->
  natmap_domain (store_insert l v s) =
    natmap_domain (store_sig_insert l a S).
Proof. intros. rewrite store_insert_domain, store_sig_insert_domain, H. reflexivity. Qed.

Lemma store_sig_update_domains : forall s S l v a,
  natmap_domain s = natmap_domain S ->
  natmap_domain (store_update l v s) =
    natmap_domain (store_sig_update l a S).
Proof. intros. rewrite store_update_domain, store_sig_update_domain, H. reflexivity. Qed.

Lemma store_sig_remove_domains : forall s S l,
  natmap_domain s = natmap_domain S ->
  natmap_domain (store_remove l s) = natmap_domain (store_sig_remove l S).
Proof. intros. rewrite store_remove_domain, store_sig_remove_domain, H. reflexivity. Qed.

(** ** Reference graph

    Edges record addresses mentioned in cell contents, including under
    lambdas and in lazy components. Membership collapses repeated occurrences
    into one edge. The graph is defined for arbitrary stores; exclusive
    ownership is established separately by runtime typing and store balance.

    The running term can be viewed as an additional root, whose outgoing
    edges are [locations e]. It has no incoming edges, so cycles in the full
    graph are exactly cycles among cells. *)

Definition store_edge (s : store) : Graph nat :=
  fun x y => exists v, In (x, v) s /\ In y (locations v).

Definition store_acyclic (s : store) : Prop := graph_acyclic (store_edge s).

Lemma store_acyclic_empty : store_acyclic [].
Proof.
  apply graph_acyclic_empty. intros x y [v [Hin _]]. contradiction.
Qed.

Lemma store_insert_edge : forall s l v x y,
  store_edge (store_insert l v s) x y <->
  (x = l /\ In y (locations v)) \/ store_edge s x y.
Proof.
  intros s l v x y. split.
  - intros [w [Hin Hy]]. cbn [store_insert natmap_insert] in Hin.
    destruct Hin as [E | Hin].
    + injection E as -> ->. left. auto.
    + right. exists w. auto.
  - intros [[-> Hy] | [w [Hin Hy]]].
    + exists v. split.
      * unfold store_insert, natmap_insert. left. reflexivity.
      * exact Hy.
    + exists w. split.
      * unfold store_insert, natmap_insert. right. exact Hin.
      * exact Hy.
Qed.

Lemma store_remove_edge : forall s l x y,
  store_edge (store_remove l s) x y -> x <> l /\ store_edge s x y.
Proof.
  intros s l x y [v [Hin Hy]]. unfold store_remove in Hin.
  destruct (natmap_remove_in _ _ _ _ Hin) as [Hne Hold].
  split; [exact Hne | exists v; auto].
Qed.

Lemma store_acyclic_remove : forall s l,
  store_acyclic s -> store_acyclic (store_remove l s).
Proof.
  intros s l Hacy.
  assert (Hmono : forall x y,
    graph_path (store_edge (store_remove l s)) x y ->
    graph_path (store_edge s) x y).
  { intros x y Hpath. induction Hpath.
    - destruct (store_remove_edge _ _ _ _ H) as [_ Hold].
      apply PathOne. exact Hold.
    - destruct (store_remove_edge _ _ _ _ H) as [_ Hold].
      eapply PathStep; eassumption. }
  intros x Hpath. apply (Hacy x), Hmono, Hpath.
Qed.

(** Inserting a cell can add only outgoing edges from its address. If that
    address had no incoming edge and the new value does not mention it, the
    insertion cannot create an ownership cycle. *)
Lemma store_acyclic_insert : forall s l v,
  store_acyclic s -> (forall x, ~ store_edge s x l) ->
  ~ In l (locations v) -> store_acyclic (store_insert l v s).
Proof.
  intros s l v Hacy Hincoming Hself.
  apply graph_acyclic_update with (edge := store_edge s) (v := l).
  - exact Hacy.
  - intros x y Hedge. apply store_insert_edge in Hedge. tauto.
  - exact Hincoming.
  - intros Hedge. apply store_insert_edge in Hedge.
    destruct Hedge as [[_ Hin] | Hold].
    + exact (Hself Hin).
    + apply (Hacy l). apply PathOne. exact Hold.
Qed.

Lemma store_replace_edge : forall s l v x y,
  store_edge (natmap_replace l v s) x y ->
  (x = l /\ In y (locations v)) \/ (x <> l /\ store_edge s x y).
Proof.
  intros s l v x y [w [Hin Hy]]. apply in_map_iff in Hin.
  destruct Hin as [[k old] [E Hin]]. simpl in E.
  injection E as Ekey Evalue. subst x w.
  destruct (Nat.eqb l k) eqn:E.
  - apply Nat.eqb_eq in E. subst. left. auto.
  - apply Nat.eqb_neq in E. right. split; [congruence | ].
    exists old. auto.
Qed.

(** Replacement changes only outgoing edges of the updated cell. This
    specializes the graph update lemma; typing and balance supply its
    side conditions when applying it to a primitive swap. *)
Lemma store_acyclic_replace : forall s l v,
  store_acyclic s -> (forall x, ~ store_edge s x l) ->
  ~ In l (locations v) -> store_acyclic (natmap_replace l v s).
Proof.
  intros s l v Hacy Hincoming Hself.
  apply graph_acyclic_update with (edge := store_edge s) (v := l).
  - exact Hacy.
  - intros x y H. apply store_replace_edge in H. tauto.
  - exact Hincoming.
  - intros H. apply store_replace_edge in H. tauto.
Qed.
