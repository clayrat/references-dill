(** * Directed paths and acyclicity

    A graph is given by an edge relation over any vertex type. No finite
    representation or decidable vertex equality is needed for these lemmas. *)

From Stdlib Require Import Arith Lia.

Definition Graph (V : Type) : Type := V -> V -> Prop.

(** Paths have positive length: reflexivity alone is not a cycle. *)
Inductive graph_path {V : Type} (edge : Graph V) : Graph V :=
  | PathOne : forall x y, edge x y -> graph_path edge x y
  | PathStep : forall x y z, edge x y ->
      graph_path edge y z -> graph_path edge x z.

Definition graph_acyclic {V : Type} (edge : Graph V) : Prop :=
  forall x, ~ graph_path edge x x.

Lemma graph_path_last : forall {V : Type} (edge : Graph V) x y,
  graph_path edge x y -> exists k, edge k y.
Proof. intros V edge x y H. induction H; eauto. Qed.

Lemma graph_acyclic_empty : forall {V : Type} (edge : Graph V),
  (forall x y, ~ edge x y) -> graph_acyclic edge.
Proof.
  intros V edge Hempty x H. apply graph_path_last in H.
  destruct H as [k H]. exact (Hempty k x H).
Qed.

Lemma graph_acyclic_rank : forall {V : Type} (edge : Graph V) (rank : V -> nat),
  (forall x y, edge x y -> rank y < rank x) -> graph_acyclic edge.
Proof.
  intros V edge rank Hrank.
  assert (Hpath : forall x y, graph_path edge x y -> rank y < rank x).
  { intros x y H. induction H; specialize (Hrank _ _ H); lia. }
  intros x H. specialize (Hpath _ _ H). lia.
Qed.

(** New edges may originate only at [v]; existing edges may be removed.
    If [v] had no incoming edges and the update adds no self-edge, a cycle
    cannot pass through [v]. Any other cycle would already have existed. *)
Lemma graph_acyclic_update : forall {V : Type} (edge edge' : Graph V) v,
  graph_acyclic edge ->
  (forall x y, edge' x y -> x = v \/ edge x y) ->
  (forall x, ~ edge x v) -> ~ edge' v v -> graph_acyclic edge'.
Proof.
  intros V edge edge' v Hacy Hedges Hincoming Hself.
  assert (Hnone : forall x, ~ edge' x v).
  { intros x H. destruct (Hedges _ _ H) as [-> | Hold];
      [exact (Hself H) | exact (Hincoming x Hold)]. }
  assert (Hold : forall x y, graph_path edge' x y ->
    x <> v -> graph_path edge x y).
  { intros x y H. induction H; intros Hne.
    - apply PathOne. destruct (Hedges _ _ H); [contradiction | assumption].
    - assert (y <> v) by (intros ->; eapply Hnone; eassumption).
      eapply PathStep; [ | apply IHgraph_path; assumption].
      destruct (Hedges _ _ H); [contradiction | assumption]. }
  intros x H.
  assert (Hne : x <> v).
  { intros E. pose proof (graph_path_last _ _ _ H) as [k Hlast].
    subst x. exact (Hnone k Hlast). }
  apply (Hacy x). apply Hold; assumption.
Qed.
