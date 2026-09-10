(** * Directed paths and acyclicity

    A graph is given by an edge relation over any vertex type. Basic path
    lemmas need neither a finite representation nor decidable vertex equality;
    finite root reachability uses only a list containing all vertices. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

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

(** A walk records all of its vertices, including both endpoints. Unlike
    [graph_path], it admits the zero-edge walk; this makes it convenient for
    finite predecessor arguments. *)
Inductive graph_walk {V : Type} (edge : Graph V) :
    V -> V -> list V -> Prop :=
  | WalkRefl : forall x, graph_walk edge x x [x]
  | WalkStep : forall x y z vertices,
      edge x y -> graph_walk edge y z vertices ->
      graph_walk edge x z (x :: vertices).

Lemma graph_walk_reaches_vertex : forall {V : Type} (edge : Graph V)
    x y vertices z,
  graph_walk edge x y vertices -> In z vertices ->
  x = z \/ graph_path edge x z.
Proof.
  intros V edge x y vertices z Hwalk. induction Hwalk; simpl; intros Hin.
  - destruct Hin as [-> | []]. left. reflexivity.
  - destruct Hin as [-> | Hin].
    + left. reflexivity.
    + right. destruct (IHHwalk Hin) as [-> | Hpath].
      * apply PathOne. exact H.
      * eapply PathStep; eassumption.
Qed.

Lemma graph_walk_path_or_eq : forall {V : Type} (edge : Graph V)
    x y vertices,
  graph_walk edge x y vertices -> x = y \/ graph_path edge x y.
Proof.
  intros V edge x y vertices Hwalk. induction Hwalk.
  - left. reflexivity.
  - right. destruct IHHwalk as [-> | Hpath].
    + apply PathOne. exact H.
    + eapply PathStep; eassumption.
Qed.

Lemma graph_acyclic_walk_nodup : forall {V : Type} (edge : Graph V)
    x y vertices,
  graph_acyclic edge -> graph_walk edge x y vertices -> NoDup vertices.
Proof.
  intros V edge x y vertices Hacy Hwalk. induction Hwalk.
  - constructor; [simpl; tauto | constructor].
  - constructor; [ | exact IHHwalk]. intros Hin.
    destruct (graph_walk_reaches_vertex _ _ _ _ _ Hwalk Hin) as
      [-> | Hpath].
    + apply (Hacy x). apply PathOne. exact H.
    + apply (Hacy x). eapply PathStep; eassumption.
Qed.

Lemma graph_walk_vertices_in : forall {V : Type} (edge : Graph V)
    (vertices_set : list V) x y vertices,
  (forall u v, edge u v -> In u vertices_set) ->
  In y vertices_set -> graph_walk edge x y vertices ->
  incl vertices vertices_set.
Proof.
  intros V edge vertices_set x y vertices Hedge Hy Hwalk.
  induction Hwalk; intros vertex Hin; simpl in Hin.
  - destruct Hin as [-> | []]. exact Hy.
  - destruct Hin as [-> | Hin].
    + eapply Hedge. exact H.
    + eapply IHHwalk; eassumption.
Qed.

Definition graph_root_reachable {V : Type} (edge : Graph V)
    (root : V -> Prop) (y : V) : Prop :=
  root y \/ exists x, root x /\ graph_path edge x y.

Lemma graph_root_reachable_or_long_walk : forall {V : Type}
    (edge : Graph V) (vertices_set : list V) (root : V -> Prop),
  (forall x y, edge x y -> In x vertices_set) ->
  (forall y, In y vertices_set -> root y \/ exists x, edge x y) ->
  forall n y, In y vertices_set ->
    graph_root_reachable edge root y \/
    exists x vertices,
      graph_walk edge x y vertices /\ length vertices = S n.
Proof.
  intros V edge vertices_set root Hedge Hcovered n.
  induction n as [| n IH]; intros y Hy.
  - right. exists y, [y]. split; [constructor | reflexivity].
  - destruct (IH y Hy) as [Hreachable | [x [vertices [Hwalk Hlength]]]].
    + left. exact Hreachable.
    + assert (Hx : In x vertices_set).
      { eapply graph_walk_vertices_in with
          (edge := edge) (y := y) (vertices := vertices); eauto.
        destruct Hwalk; simpl; auto. }
      destruct (Hcovered x Hx) as [Hroot | [predecessor Hpredecessor]].
      * left. unfold graph_root_reachable.
        destruct (graph_walk_path_or_eq _ _ _ _ Hwalk) as [-> | Hpath].
        -- left. exact Hroot.
        -- right. exists x. auto.
      * right. exists predecessor, (predecessor :: vertices). split.
        -- econstructor; eassumption.
        -- simpl. rewrite Hlength. reflexivity.
Qed.

(** In a finite acyclic graph, if every vertex is either a root or has an
    incoming edge, every vertex is reachable from a root. It is enough to
    know that edge sources belong to the finite vertex set: targets are
    already supplied by the predecessor argument. *)
Theorem finite_acyclic_root_reachable : forall {V : Type}
    (edge : Graph V) (vertices : list V) (root : V -> Prop),
  (forall x y, edge x y -> In x vertices) ->
  graph_acyclic edge ->
  (forall y, In y vertices -> root y \/ exists x, edge x y) ->
  forall y, In y vertices -> graph_root_reachable edge root y.
Proof.
  intros V edge vertices root Hedge Hacy Hcovered y Hy.
  destruct (graph_root_reachable_or_long_walk edge vertices root Hedge
    Hcovered (length vertices) y Hy) as
    [Hreachable | [x [walk [Hwalk Hlength]]]].
  - exact Hreachable.
  - pose proof (graph_acyclic_walk_nodup edge x y walk Hacy Hwalk) as Hwalk_nd.
    assert (Hincluded : incl walk vertices).
    { eapply graph_walk_vertices_in; eassumption. }
    pose proof (NoDup_incl_length Hwalk_nd Hincluded). rewrite Hlength in H.
    lia.
Qed.
