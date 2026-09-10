(** * Association lists with natural-number keys

    [NatMap A] is a transparent list representation. Positions retain their
    order and are independent of keys. Raw lists may contain duplicate keys;
    callers require [NoDup (natmap_domain m)] when uniqueness is needed. *)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.
From DILLref Require Import Prelude.

Definition NatMap (A : Type) : Type := list (nat * A).

Definition natmap_domain {A : Type} (m : NatMap A) : list nat := map fst m.

(** Lookup returns the first entry with the requested key. *)
Fixpoint natmap_lookup {A : Type} (k : nat) (m : NatMap A) : option A :=
  match m with
  | [] => None
  | (j, v) :: rest => if Nat.eqb k j then Some v else natmap_lookup k rest
  end.

(** Insertion is intentionally at the head. For stores this makes allocation
    extend every existing positional resource mask with one unavailable bit. *)
Definition natmap_insert {A : Type} (k : nat) (v : A) (m : NatMap A) : NatMap A :=
  (k, v) :: m.

(** Remove every entry with the selected key. Well-formed stores have unique
    keys, while removing all matches also gives predictable behavior on raw
    association lists. Relative order of the other entries is preserved. *)
Fixpoint natmap_remove {A : Type} (k : nat) (m : NatMap A) : NatMap A :=
  match m with
  | [] => []
  | (j, v) :: rest =>
      if Nat.eqb k j then natmap_remove k rest
      else (j, v) :: natmap_remove k rest
  end.

Lemma natmap_remove_filter : forall {A : Type} k (m : NatMap A),
  natmap_remove k m =
    filter (fun p => negb (Nat.eqb k (fst p))) m.
Proof.
  intros A k m. induction m as [| [j v] m IH]; simpl; auto.
  destruct (Nat.eqb k j); simpl; rewrite IH; reflexivity.
Qed.

(** The maximum is total, with zero as the empty default. [natmap_fresh]
    treats the empty map separately and otherwise returns its successor. *)
Fixpoint natmap_max_key {A : Type} (m : NatMap A) : nat :=
  match m with
  | [] => 0
  | (k, _) :: rest => Nat.max k (natmap_max_key rest)
  end.

Definition natmap_fresh {A : Type} (m : NatMap A) : nat :=
  match m with
  | [] => 0
  | _ => S (natmap_max_key m)
  end.

(** Replacement preserves keys and order, updating every matching entry.
    An absent key leaves the map unchanged. With unique keys and a successful
    lookup, exactly one entry is replaced. *)
Definition natmap_replace {A : Type} (k : nat) (v : A) (m : NatMap A) : NatMap A :=
  map (fun p => (fst p, if Nat.eqb k (fst p) then v else snd p)) m.

(** ** Insertion *)

Lemma natmap_insert_domain : forall {A : Type} k (v : A) m,
  natmap_domain (natmap_insert k v m) = k :: natmap_domain m.
Proof. reflexivity. Qed.

Lemma natmap_lookup_insert : forall {A : Type} k (v : A) m,
  In_opt v (natmap_lookup k (natmap_insert k v m)).
Proof. intros. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma natmap_lookup_insert_other : forall {A : Type} k j (v : A) m,
  j <> k -> natmap_lookup j (natmap_insert k v m) = natmap_lookup j m.
Proof.
  intros A k j v m Hne. cbn. destruct (Nat.eqb j k) eqn:E; auto.
  apply Nat.eqb_eq in E. contradiction.
Qed.

Lemma natmap_insert_nodup : forall {A : Type} k (v : A) m,
  ~ In k (natmap_domain m) -> NoDup (natmap_domain m) ->
  NoDup (natmap_domain (natmap_insert k v m)).
Proof. intros. rewrite natmap_insert_domain. constructor; assumption. Qed.

(** ** Removal *)

Lemma natmap_remove_domain : forall {A : Type} k (m : NatMap A),
  natmap_domain (natmap_remove k m) =
    filter (fun j => negb (Nat.eqb k j)) (natmap_domain m).
Proof.
  intros A k m. induction m as [| [j v] m IH]; simpl; auto.
  destruct (Nat.eqb k j); simpl; rewrite IH; reflexivity.
Qed.

Lemma natmap_remove_not_in : forall {A : Type} k (m : NatMap A),
  ~ In k (natmap_domain (natmap_remove k m)).
Proof.
  intros A k m. rewrite natmap_remove_domain, filter_In.
  intros [_ Hkeep]. rewrite Nat.eqb_refl in Hkeep. discriminate.
Qed.

Lemma natmap_remove_in : forall {A : Type} k j (v : A) m,
  In (j, v) (natmap_remove k m) -> j <> k /\ In (j, v) m.
Proof.
  intros A k j v m. induction m as [| [l w] m IH]; simpl; intros Hin;
    try contradiction.
  destruct (Nat.eqb k l) eqn:E.
  - destruct (IH Hin) as [Hne Htail]. split; [exact Hne | right; exact Htail].
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + injection Heq as -> ->. apply Nat.eqb_neq in E. split; [congruence | auto].
    + destruct (IH Hin) as [Hne Htail]. split; [exact Hne | right; exact Htail].
Qed.

Lemma natmap_remove_in_other : forall {A : Type} k j (v : A) m,
  j <> k -> In (j, v) m -> In (j, v) (natmap_remove k m).
Proof.
  intros A k j v m Hne. induction m as [| [l w] m IH]; intros Hin.
  - inversion Hin.
  - destruct Hin as [Heq | Hin].
    + inversion Heq; subst l w. cbn. destruct (Nat.eqb k j) eqn:E.
      * apply Nat.eqb_eq in E. congruence.
      * left. reflexivity.
    + cbn. destruct (Nat.eqb k l).
      * apply IH. exact Hin.
      * right. apply IH. exact Hin.
Qed.

Lemma natmap_lookup_remove : forall {A : Type} k (m : NatMap A),
  natmap_lookup k (natmap_remove k m) = None.
Proof.
  intros A k m. induction m as [| [j v] m IH]; simpl; auto.
  destruct (Nat.eqb k j) eqn:E; simpl; rewrite ?E; exact IH.
Qed.

Lemma natmap_lookup_remove_other : forall {A : Type} k j (m : NatMap A),
  j <> k -> natmap_lookup j (natmap_remove k m) = natmap_lookup j m.
Proof.
  intros A k j m Hne. induction m as [| [l v] m IH]; simpl; auto.
  destruct (Nat.eqb k l) eqn:Ekl.
  - apply Nat.eqb_eq in Ekl. subst l.
    destruct (Nat.eqb j k) eqn:Ejk.
    + apply Nat.eqb_eq in Ejk. contradiction.
    + exact IH.
  - destruct (Nat.eqb j l) eqn:Ejl.
    + cbn [natmap_lookup]. rewrite Ejl. reflexivity.
    + cbn [natmap_lookup]. rewrite Ejl. exact IH.
Qed.

Lemma natmap_remove_nodup : forall {A : Type} k (m : NatMap A),
  NoDup (natmap_domain m) -> NoDup (natmap_domain (natmap_remove k m)).
Proof.
  intros A k m H. rewrite natmap_remove_domain. apply NoDup_filter. exact H.
Qed.

Lemma natmap_remove_absent : forall {A : Type} k (m : NatMap A),
  ~ In k (natmap_domain m) -> natmap_remove k m = m.
Proof.
  intros A k m. induction m as [| [j v] m IH]; simpl; intros H; auto.
  apply Decidable.not_or in H. destruct H as [Hhead Htail].
  destruct (Nat.eqb k j) eqn:E.
  - apply Nat.eqb_eq in E. congruence.
  - f_equal. apply IH. exact Htail.
Qed.

Lemma natmap_remove_insert : forall {A : Type} k (v : A) m,
  ~ In k (natmap_domain m) ->
  natmap_remove k (natmap_insert k v m) = m.
Proof.
  intros. cbn. rewrite Nat.eqb_refl. apply natmap_remove_absent. exact H.
Qed.

(** ** Lookup completeness and freshness *)

Lemma natmap_lookup_complete : forall {A : Type} k (m : NatMap A),
  In k (natmap_domain m) -> Is_some (natmap_lookup k m).
Proof.
  intros A k m Hin. apply Is_some_exists.
  induction m as [| [j v] m IH]; simpl in Hin; simpl;
    try contradiction.
  destruct (Nat.eqb k j) eqn:E.
  - exists v. reflexivity.
  - destruct Hin as [Heq | Hin].
    + subst j. rewrite Nat.eqb_refl in E. discriminate.
    + apply IH. exact Hin.
Qed.

Lemma natmap_lookup_member_unique : forall {A : Type} m l (v w : A),
  NoDup (natmap_domain m) -> In (l, v) m ->
  In_opt w (natmap_lookup l m) -> v = w.
Proof.
  intros A m. induction m as [| [k x] m IH]; intros l v w Hnd Hin Hlookup;
    simpl in *; try contradiction.
  inversion Hnd; subst. destruct Hin as [Heq | Hin].
  - injection Heq as -> ->. rewrite Nat.eqb_refl in Hlookup.
    symmetry. exact Hlookup.
  - destruct (Nat.eqb l k) eqn:E.
    + apply Nat.eqb_eq in E. subst k. exfalso. apply H1.
      apply (in_map fst) in Hin. exact Hin.
    + eapply IH; eassumption.
Qed.

Lemma natmap_lookup_absent : forall {A : Type} k (m : NatMap A),
  ~ In k (natmap_domain m) -> natmap_lookup k m = None.
Proof.
  intros A k m. induction m as [| [j v] m IH]; simpl; intros H; auto.
  apply Decidable.not_or in H. destruct H as [Hhead Htail].
  destruct (Nat.eqb k j) eqn:E.
  - apply Nat.eqb_eq in E. congruence.
  - apply IH. exact Htail.
Qed.

Lemma natmap_key_le_max : forall {A : Type} (m : NatMap A) k,
  In k (natmap_domain m) -> k <= natmap_max_key m.
Proof.
  intros A m. induction m as [| [j v] m IH]; simpl; intros k Hin;
    try contradiction.
  destruct Hin as [-> | Hin].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma natmap_fresh_empty : forall A, @natmap_fresh A [] = 0.
Proof. reflexivity. Qed.

Lemma natmap_fresh_nonempty : forall {A : Type} (m : NatMap A),
  m <> [] -> natmap_fresh m = S (natmap_max_key m).
Proof. intros A [| [k v] m] H; [contradiction | reflexivity]. Qed.

Lemma natmap_fresh_gt : forall {A : Type} (m : NatMap A) k,
  In k (natmap_domain m) -> k < natmap_fresh m.
Proof.
  intros A [| [j v] m] k Hin; simpl in Hin; try contradiction.
  unfold natmap_fresh.
  pose proof (natmap_key_le_max ((j, v) :: m) k Hin). lia.
Qed.

Lemma natmap_fresh_not_in : forall {A : Type} (m : NatMap A),
  ~ In (natmap_fresh m) (natmap_domain m).
Proof.
  intros A m Hin. pose proof (natmap_fresh_gt _ _ Hin). lia.
Qed.

Lemma natmap_lookup_fresh : forall {A : Type} (m : NatMap A),
  natmap_lookup (natmap_fresh m) m = None.
Proof. intros. apply natmap_lookup_absent, natmap_fresh_not_in. Qed.

Lemma natmap_insert_fresh_nodup : forall {A : Type} (v : A) m,
  NoDup (natmap_domain m) ->
  NoDup (natmap_domain (natmap_insert (natmap_fresh m) v m)).
Proof. intros. apply natmap_insert_nodup; [apply natmap_fresh_not_in | exact H]. Qed.

(** ** Replacement *)

Lemma natmap_replace_domain : forall {A : Type} k (v : A) m,
  natmap_domain (natmap_replace k v m) = natmap_domain m.
Proof. intros A k v m. induction m as [| [j w] m IH]; simpl; f_equal; auto. Qed.

Lemma natmap_lookup_in : forall {A : Type} k (v : A) m,
  In_opt v (natmap_lookup k m) -> In (k, v) m.
Proof.
  intros A k v m. induction m as [| [j w] m IH]; simpl; intros H; try contradiction.
  destruct (Nat.eqb k j) eqn:E; simpl in H.
  - apply Nat.eqb_eq in E. subst. left. reflexivity.
  - right. auto.
Qed.

Lemma natmap_lookup_replace : forall {A : Type} k (v : A) m,
  Is_some (natmap_lookup k m) ->
  In_opt v (natmap_lookup k (natmap_replace k v m)).
Proof.
  intros A k v m. induction m as [| [j w] m IH]; simpl; intros H; try contradiction.
  destruct (Nat.eqb k j); simpl in *; auto.
Qed.

Lemma natmap_lookup_replace_other : forall {A : Type} k j (v : A) m,
  j <> k -> natmap_lookup j (natmap_replace k v m) = natmap_lookup j m.
Proof.
  intros A k j v m Hne. induction m as [| [l w] m IH]; simpl; auto.
  destruct (Nat.eqb j l) eqn:E; simpl; auto.
  destruct (Nat.eqb k l) eqn:F; auto.
  apply Nat.eqb_eq in E, F. congruence.
Qed.

Lemma natmap_replace_absent : forall {A : Type} k (v : A) m,
  ~ In k (natmap_domain m) -> natmap_replace k v m = m.
Proof.
  intros A k v m. induction m as [| [j old] m IH]; simpl; intros Hnot; auto.
  apply Decidable.not_or in Hnot. destruct Hnot as [Hhead Htail].
  destruct (Nat.eqb k j) eqn:E.
  - apply Nat.eqb_eq in E. congruence.
  - f_equal. apply IH, Htail.
Qed.

Lemma natmap_replace_nth_same : forall {A : Type} k (v old : A) m i,
  In_opt (k, old) (nth_error m i) ->
  In_opt (k, v) (nth_error (natmap_replace k v m) i).
Proof.
  intros A k v old m. induction m as [| [j w] m IH]; intros [| i] H;
    simpl in *; try contradiction.
  - injection H as -> ->. rewrite Nat.eqb_refl. reflexivity.
  - apply IH. exact H.
Qed.

Lemma natmap_replace_nth_other : forall {A : Type} k j (v old : A) m i,
  j <> k -> In_opt (j, old) (nth_error m i) ->
  In_opt (j, old) (nth_error (natmap_replace k v m) i).
Proof.
  intros A k j v old m. induction m as [| [l w] m IH]; intros [| i] Hne H;
    simpl in *; try contradiction.
  - injection H as Hkey Hvalue. subst l w. destruct (Nat.eqb k j) eqn:E.
    + apply Nat.eqb_eq in E. congruence.
    + reflexivity.
  - apply IH; assumption.
Qed.

(** A unique key identifies its list position regardless of the entry type. *)
Lemma natmap_key_index : forall {A : Type} (m : NatMap A) i j k a b,
  NoDup (natmap_domain m) -> In_opt (k, a) (nth_error m i) ->
  In_opt (k, b) (nth_error m j) -> i = j.
Proof.
  intros A m. induction m as [| [l c] m IH]; intros i j k a b Hnd Hi Hj;
    destruct i, j; simpl in *; try contradiction; auto.
  - inversion Hnd; subst. injection Hi as Hk Ha; subst.
    exfalso. apply H1. apply In_opt_eq_Some, nth_error_In, (in_map fst) in Hj.
    exact Hj.
  - inversion Hnd; subst. injection Hj as Hk Hb; subst.
    exfalso. apply H1. apply In_opt_eq_Some, nth_error_In, (in_map fst) in Hi.
    exact Hi.
  - inversion Hnd; subst. f_equal. eauto.
Qed.
