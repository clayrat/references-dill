(** * Order-preserving context splitting

    [Split l ls rs] says that [l] is an interleaving of [ls] and [rs]: every
    element of [l] goes to exactly one side and both sides keep the order of
    [l]. This is the multiplicative division of the resource zone used by
    application, tensor pairs and the other two-premise constructs.

    It is deliberately not a permutation: [Split [x; y] [y; x] []] fails while
    [Permutation [x; y] ([y; x] ++ [])] holds. Exchange is a separate lemma;
    with de Bruijn indices it also renames the term.

    A split is the same thing as an availability mask together with its
    complement, interpreted as embeddings by [OPE.v]. Pointwise mask
    splitting ([SplitM] from [Mask.v]) corresponds to splitting the positioned
    views of the scope. *)

From Stdlib Require Import List Permutation Arith Lia.
Import ListNotations.
From DILLref Require Import Mask OPE.

Section Split.
  Context {A : Type}.

  Inductive Split : list A -> list A -> list A -> Prop :=
    | SplitNil : Split [] [] []
    | SplitL : forall x l ls rs, Split l ls rs -> Split (x :: l) (x :: ls) rs
    | SplitR : forall x l ls rs, Split l ls rs -> Split (x :: l) ls (x :: rs).

  (** ** Units *)

  Lemma split_left : forall l, Split l l [].
  Proof. induction l; constructor; assumption. Qed.

  Lemma split_right : forall l, Split l [] l.
  Proof. induction l; constructor; assumption. Qed.

  Lemma split_nil_inv : forall ls rs, Split [] ls rs -> ls = [] /\ rs = [].
  Proof. intros ls rs H. inversion H. auto. Qed.

  Lemma split_left_inv : forall l ls, Split l ls [] -> ls = l.
  Proof.
    intros l ls H. remember [] as rs. induction H; subst.
    - reflexivity.
    - f_equal. auto.
    - discriminate.
  Qed.

  Lemma split_right_inv : forall l rs, Split l [] rs -> rs = l.
  Proof.
    intros l rs H. remember [] as ls. induction H; subst.
    - reflexivity.
    - discriminate.
    - f_equal. auto.
  Qed.

  Lemma split_cons_inv : forall x l ls rs,
    Split (x :: l) ls rs ->
    (exists ls', ls = x :: ls' /\ Split l ls' rs) \/
    (exists rs', rs = x :: rs' /\ Split l ls rs').
  Proof.
    intros x l ls rs H. inversion H; subst; [left | right]; eexists; eauto.
  Qed.

  (** ** Commutativity *)

  Lemma split_comm : forall l ls rs, Split l ls rs -> Split l rs ls.
  Proof. intros l ls rs H. induction H; constructor; assumption. Qed.

  (** ** Associativity

      Regrouping a three-way division produces the intermediate part as a
      witness. With repeated elements, different witnesses may satisfy the
      conclusion; only existence is asserted. *)

  Lemma split_assoc : forall l ab c a b,
    Split l ab c -> Split ab a b ->
    exists bc, Split l a bc /\ Split bc b c.
  Proof.
    intros l ab c a b H. revert a b.
    induction H as [| x l ls rs H IH | x l ls rs H IH]; intros a b Hab.
    - inversion Hab; subst. exists []. split; constructor.
    - inversion Hab as [| ? ? ? ? Hab' | ? ? ? ? Hab']; subst.
      + destruct (IH _ _ Hab') as [bc [H1 H2]].
        exists bc. split; [constructor | ]; assumption.
      + destruct (IH _ _ Hab') as [bc [H1 H2]].
        exists (x :: bc). split; constructor; assumption.
    - destruct (IH _ _ Hab) as [bc [H1 H2]].
      exists (x :: bc). split; constructor; assumption.
  Qed.

  Lemma split_unassoc : forall l a bc b c,
    Split l a bc -> Split bc b c ->
    exists ab, Split l ab c /\ Split ab a b.
  Proof.
    intros l a bc b c H1 H2.
    apply split_comm in H1. apply split_comm in H2.
    destruct (split_assoc _ _ _ _ _ H1 H2) as [ab [H3 H4]].
    exists ab. split; apply split_comm; assumption.
  Qed.

  (** ** Relation to lists *)

  Lemma split_length : forall l ls rs,
    Split l ls rs -> length l = length ls + length rs.
  Proof.
    intros l ls rs H. induction H; simpl; auto.
    rewrite IHSplit. symmetry. apply PeanoNat.Nat.add_succ_r.
  Qed.

  Lemma split_same_left_inv : forall l rs,
    Split l l rs -> rs = [].
  Proof.
    intros l rs H. apply split_length in H.
    assert (length rs = 0) by lia. destruct rs; auto; discriminate.
  Qed.

  Lemma split_in : forall l ls rs,
    Split l ls rs -> forall x, In x l <-> In x ls \/ In x rs.
  Proof.
    intros l ls rs H x. induction H; simpl; tauto.
  Qed.

  Lemma split_nodup_left : forall l ls rs,
    Split l ls rs -> NoDup l -> NoDup ls.
  Proof.
    intros l ls rs H. induction H; intros Hnd; inversion Hnd; subst; simpl.
    - constructor.
    - constructor.
      + intros Hin. apply H2. eapply split_in; [exact H | left; exact Hin].
      + apply IHSplit. exact H3.
    - apply IHSplit. exact H3.
  Qed.

  Lemma split_nodup_right : forall l ls rs,
    Split l ls rs -> NoDup l -> NoDup rs.
  Proof.
    intros l ls rs Hsplit Hnd.
    apply split_comm in Hsplit. eapply split_nodup_left; eassumption.
  Qed.

  Lemma split_disjoint : forall l ls rs,
    Split l ls rs -> NoDup l -> forall x, In x ls -> ~ In x rs.
  Proof.
    intros l ls rs H. induction H; intros Hnd y Hleft Hright; simpl in *;
      inversion Hnd; subst.
    - contradiction.
    - destruct Hleft as [-> | Hleft].
      + apply H2. eapply split_in; [exact H | right; exact Hright].
      + eapply IHSplit; eassumption.
    - destruct Hright as [-> | Hright].
      + apply H2. eapply split_in; [exact H | left; exact Hleft].
      + eapply IHSplit; eassumption.
  Qed.

  (** Divide two already separated owners in parallel. *)
  Lemma split_interchange : forall l a b a1 a2 b1 b2,
    Split l a b -> Split a a1 a2 -> Split b b1 b2 ->
    exists l1 l2,
      Split l l1 l2 /\ Split l1 a1 b1 /\ Split l2 a2 b2.
  Proof.
    intros l a b a1 a2 b1 b2 Hab. revert a1 a2 b1 b2.
    induction Hab; intros a1 a2 b1 b2 Ha Hb.
    - inversion Ha; inversion Hb; subst. exists [], []. repeat constructor.
    - inversion Ha as [| ? ? ? ? Ha' | ? ? ? ? Ha']; subst.
      + destruct (IHHab _ _ _ _ Ha' Hb) as [l1 [l2 [Hl [H1 H2]]]].
        exists (x :: l1), l2. repeat split.
        * apply SplitL. exact Hl.
        * apply SplitL. exact H1.
        * exact H2.
      + destruct (IHHab _ _ _ _ Ha' Hb) as [l1 [l2 [Hl [H1 H2]]]].
        exists l1, (x :: l2). repeat split.
        * apply SplitR. exact Hl.
        * exact H1.
        * apply SplitL. exact H2.
    - inversion Hb as [| ? ? ? ? Hb' | ? ? ? ? Hb']; subst.
      + destruct (IHHab _ _ _ _ Ha Hb') as [l1 [l2 [Hl [H1 H2]]]].
        exists (x :: l1), l2. repeat split.
        * apply SplitL. exact Hl.
        * apply SplitR. exact H1.
        * exact H2.
      + destruct (IHHab _ _ _ _ Ha Hb') as [l1 [l2 [Hl [H1 H2]]]].
        exists l1, (x :: l2). repeat split.
        * apply SplitR. exact Hl.
        * exact H1.
        * apply SplitR. exact H2.
  Qed.

  Lemma split_filter : forall (keep : A -> bool) l ls rs,
    Split l ls rs ->
    Split (filter keep l) (filter keep ls) (filter keep rs).
  Proof.
    intros keep l ls rs H. induction H; simpl; try constructor.
    - destruct (keep x); simpl; [constructor | ]; exact IHSplit.
    - destruct (keep x); simpl; [constructor | ]; exact IHSplit.
  Qed.

  Lemma split_permutation : forall l ls rs,
    Split l ls rs -> Permutation l (ls ++ rs).
  Proof.
    intros l ls rs H. induction H; simpl.
    - constructor.
    - constructor. assumption.
    - eapply Permutation_trans; [apply perm_skip; exact IHSplit | ].
      apply Permutation_middle.
  Qed.

  Lemma split_app : forall ls rs, Split (ls ++ rs) ls rs.
  Proof.
    induction ls; simpl; intros.
    - apply split_right.
    - constructor. apply IHls.
  Qed.

  (** ** Transport through permutations

      Reordering the whole list may reorder each part. Membership of the
      parts is preserved with multiplicity; no uniqueness or decidable
      equality assumption is needed. *)
  Lemma split_permutation_transport : forall l l',
    Permutation l l' -> forall ls rs, Split l ls rs ->
    exists ls' rs', Split l' ls' rs' /\
      Permutation ls ls' /\ Permutation rs rs'.
  Proof.
    intros l l' Hp. induction Hp as
      [ | x l l' Hp IH | x y l | l m n Hlm IHlm Hmn IHmn ]; intros ls rs Hs.
    - apply split_nil_inv in Hs. destruct Hs as [-> ->].
      exists [], []. repeat constructor.
    - apply split_cons_inv in Hs.
      destruct Hs as [[xs [-> Hs]] | [ys [-> Hs]]];
        destruct (IH _ _ Hs) as [xs' [ys' [Ht [Hl Hr]]]].
      + exists (x :: xs'), ys'. split; [constructor; exact Ht | ].
        split; [constructor; exact Hl | exact Hr].
      + exists xs', (x :: ys'). split; [constructor; exact Ht | ].
        split; [exact Hl | constructor; exact Hr].
    - apply split_cons_inv in Hs.
      destruct Hs as [[xs [-> Hs]] | [ys [-> Hs]]];
        apply split_cons_inv in Hs;
        destruct Hs as [[xs' [-> Hs]] | [ys' [-> Hs]]].
      + exists (x :: y :: xs'), rs.
        split; [constructor; constructor; exact Hs | ].
        split; [apply perm_swap | apply Permutation_refl].
      + exists (y :: xs), (x :: ys').
        split; [apply SplitR, SplitL; exact Hs | ].
        split; apply Permutation_refl.
      + exists (x :: xs'), (y :: ys).
        split; [apply SplitL, SplitR; exact Hs | ].
        split; apply Permutation_refl.
      + exists ls, (x :: y :: ys').
        split; [apply SplitR, SplitR; exact Hs | ].
        split; [apply Permutation_refl | apply perm_swap].
    - destruct (IHlm _ _ Hs) as [xs [ys [Hm [Hl Hr]]]].
      destruct (IHmn _ _ Hm) as [xs' [ys' [Hn [Hl' Hr']]]].
      exists xs', ys'. split; [exact Hn | ].
      split; eapply Permutation_trans; eassumption.
  Qed.

  Lemma split_permutation_iff : forall l ls rs,
    Permutation l (ls ++ rs) <->
    exists ls' rs', Split l ls' rs' /\
      Permutation ls ls' /\ Permutation rs rs'.
  Proof.
    intros l ls rs. split.
    - intros Hp. eapply split_permutation_transport.
      + apply Permutation_sym. exact Hp.
      + apply split_app.
    - intros [ls' [rs' [Hs [Hl Hr]]]].
      eapply Permutation_trans; [apply split_permutation; exact Hs | ].
      apply Permutation_app; apply Permutation_sym; assumption.
  Qed.

  (** Keys identify resources independently of the payload. Uniqueness of
      projected keys is transported along the whole-list permutation. *)
  Lemma split_keyed_permutation_iff : forall {K : Type} (key : A -> K) l ls rs,
    (Permutation l (ls ++ rs) /\ NoDup (map key (ls ++ rs))) <->
    (NoDup (map key l) /\
      exists ls' rs', Split l ls' rs' /\
        Permutation ls ls' /\ Permutation rs rs').
  Proof.
    intros K key l ls rs. split.
    - intros [Hp Hnd]. split.
      + eapply Permutation_NoDup; [ | exact Hnd].
        apply Permutation_map, Permutation_sym. exact Hp.
      + apply split_permutation_iff. exact Hp.
    - intros [Hnd Hs]. apply split_permutation_iff in Hs. split; [exact Hs | ].
      eapply Permutation_NoDup; [ | exact Hnd].
      apply Permutation_map. exact Hs.
  Qed.

  (** ** Complementary masks are a [Split] *)

  Lemma ope_compl_split : forall L U G G',
    ope L U G -> ope L (mask_compl U) G' -> Split L G G'.
  Proof.
    intros L U G G' H. revert G'.
    induction H as [| x L U G H IH | x L U G H IH]; intros G' H'; simpl in H'.
    - inversion H'; subst. constructor.
    - inversion H'; subst. constructor. apply IH. assumption.
    - inversion H'; subst. constructor. apply IH. assumption.
  Qed.

  Lemma split_ope_compl : forall L G G',
    Split L G G' -> exists U, ope L U G /\ ope L (mask_compl U) G'.
  Proof.
    intros L G G' H.
    induction H as [| x l ls rs H [U [HU HU']] | x l ls rs H [U [HU HU']]].
    - exists []. split; constructor.
    - exists (true :: U). split; simpl; constructor; assumption.
    - exists (false :: U). split; simpl; constructor; assumption.
  Qed.

End Split.

Lemma split_map : forall {A B : Type} (f : A -> B) l ls rs,
  Split l ls rs -> Split (map f l) (map f ls) (map f rs).
Proof. intros A B f l ls rs H. induction H; simpl; constructor; assumption. Qed.

(** Order-preserving inclusion, presented through the unused complement. *)
Definition split_incl {A : Type} (small whole : list A) : Prop :=
  exists frame, Split whole small frame.

Lemma split_incl_refl : forall {A : Type} (l : list A), split_incl l l.
Proof. intros. exists []. apply split_left. Qed.

Lemma split_incl_left : forall {A : Type} (l a b : list A),
  Split l a b -> split_incl a l.
Proof. intros. exists b. exact H. Qed.

Lemma split_incl_right : forall {A : Type} (l a b : list A),
  Split l a b -> split_incl b l.
Proof. intros. exists a. apply split_comm. exact H. Qed.

Lemma split_incl_trans : forall {A : Type} (a b c : list A),
  split_incl a b -> split_incl b c -> split_incl a c.
Proof.
  intros A a b c [ab Hab] [bc Hbc].
  destruct (split_assoc _ _ _ _ _ Hbc Hab) as [frame [H _]].
  exists frame. exact H.
Qed.

Lemma split_incl_left_trans : forall {A : Type} (whole left right outer : list A),
  Split whole left right -> split_incl whole outer -> split_incl left outer.
Proof.
  intros A whole left right outer Hsplit Hincl.
  eapply split_incl_trans; [eapply split_incl_left | exact Hincl].
  exact Hsplit.
Qed.

Lemma split_incl_right_trans : forall {A : Type} (whole left right outer : list A),
  Split whole left right -> split_incl whole outer -> split_incl right outer.
Proof.
  intros A whole left right outer Hsplit Hincl.
  eapply split_incl_trans; [eapply split_incl_right | exact Hincl].
  exact Hsplit.
Qed.

Lemma split_incl_in : forall {A : Type} (small whole : list A) x,
  split_incl small whole -> In x small -> In x whole.
Proof.
  intros A small whole x [frame Hsplit] Hin.
  apply (proj2 (split_in _ _ _ Hsplit x)). left. exact Hin.
Qed.

(** ** Mask splitting and positioned views *)

Lemma splitM_view : forall I U F,
  SplitM I U F ->
  forall {A : Type} n (L : list A),
    Split (view_from n L I) (view_from n L U) (view_from n L F).
Proof.
  intros I U F H. induction H; intros A n [| x L]; simpl; try constructor;
    try apply IHSplitM; constructor.
Qed.

(** The converse relies on positions: with types alone two resources of the
    same type could not be told apart. *)
Lemma view_splitM : forall {A : Type} (L : list A) I U F n,
  wf_mask L I -> wf_mask L U -> wf_mask L F ->
  Split (view_from n L I) (view_from n L U) (view_from n L F) ->
  SplitM I U F.
Proof.
  unfold wf_mask. intros A L.
  induction L as [| x L IH]; intros [| i I] [| u U] [| f F] n HI HU HF H;
    simpl in *; try discriminate.
  - constructor.
  - injection HI as HI. injection HU as HU. injection HF as HF.
    assert (Hpos : forall U', ~ In (n, x) (view_from (S n) L U')).
    { intros U' Hin. apply view_from_pos in Hin. lia. }
    destruct i.
    + (* the position is available: it goes to exactly one side *)
      apply split_cons_inv in H.
      destruct H as [[ls' [Hls H]] | [rs' [Hrs H]]].
      * destruct u; simpl in Hls.
        2: { exfalso. eapply Hpos. rewrite Hls. left. reflexivity. }
        injection Hls as Hls; subst ls'. destruct f; simpl in H.
        { exfalso. eapply Hpos. eapply split_in; [exact H | right].
          left. reflexivity. }
        constructor. eapply IH; eassumption.
      * destruct f; simpl in Hrs.
        2: { exfalso. eapply Hpos. rewrite Hrs. left. reflexivity. }
        injection Hrs as Hrs; subst rs'. destruct u; simpl in H.
        { exfalso. eapply Hpos. eapply split_in; [exact H | left].
          left. reflexivity. }
        constructor. eapply IH; eassumption.
    + (* the position is unavailable in [I], hence in both parts *)
      destruct u; simpl in H.
      { exfalso. eapply Hpos. eapply split_in; [exact H | left].
        left. reflexivity. }
      destruct f; simpl in H.
      { exfalso. eapply Hpos. eapply split_in; [exact H | right].
        left. reflexivity. }
      constructor. eapply IH; eassumption.
Qed.
