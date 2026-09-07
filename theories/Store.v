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
