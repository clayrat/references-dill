(** * Progress of typed configurations

    A term in a typed balanced configuration is either a value or can take a
    relational step.  Canonical forms and typed cell lookup rule out failures
    of the dynamic checks performed by [swap] and [free]. *)

From Stdlib Require Import List Arith Lia.
From DILLref Require Import Prelude Ty Syntax Mask Split Substitution.
From DILLref Require Import NatMap Store Semantics StoreTyping StoreTypingInversion.
Import ListNotations.
Local Opaque split_incl.

Lemma has_type_with_loc_progress : forall f S s C R e a,
  NoDup (natmap_domain S) ->
  cells_typed f S s C ->
  split_incl R S ->
  has_type_with_loc f [] [] [] R e a ->
  value e \/ exists s' e', small_step (s, e) (s', e').
Proof.
  intros f S s C R e. revert R. induction e;
    intros R a Hnd Hcells HRS Htype.
  all: destruct (has_type_with_loc_generation_closed _ _ _ _ _ Htype)
    as [Q [_ [HQ Hhead]]].
  all: pose proof (split_incl_trans _ _ _ HQ HRS) as HQS.
  all: cbn [has_type_with_loc_head] in Hhead.

  - destruct Hhead as [Hnone _]. destruct n;
      cbn [In_opt Exists_opt] in Hnone; contradiction.
  - destruct Hhead as [Hnone _]. destruct n;
      cbn [In_opt Exists_opt] in Hnone; contradiction.
  - left. constructor.
  - left. constructor.
  - destruct Hhead as [U1 [U2 [R1 [R2 [b
      [HU [HR [Hfun Harg]]]]]]]].
    apply splitM_nil_inv in HU as [-> ->].
    assert (HRS1 : split_incl R1 S).
    { eapply split_incl_left_trans; eassumption. }
    assert (HRS2 : split_incl R2 S).
    { eapply split_incl_right_trans; eassumption. }
    destruct (IHe1 R1 (TLolli b a) Hnd Hcells HRS1 Hfun)
      as [Hvalue1 | [s' [e1' Hstep1]]].
    + destruct (IHe2 R2 b Hnd Hcells HRS2 Harg)
        as [Hvalue2 | [s' [e2' Hstep2]]].
      * destruct (canonical_lolli _ _ _ _ _ Hvalue1 Hfun) as [body ->].
        right. exists s, (subst_l e2 body).
        apply StepAppBeta. exact Hvalue2.
      * right. exists s', (App e1 e2'). apply StepAppArg; assumption.
    + right. exists s', (App e1' e2). apply StepAppFun. exact Hstep1.
  - left. constructor.
  - destruct Hhead as [U1 [U2 [R1 [R2
      [HU [HR [Hscrutinee Hbody]]]]]]].
    apply splitM_nil_inv in HU as [-> ->].
    assert (HRS1 : split_incl R1 S).
    { eapply split_incl_left_trans; eassumption. }
    destruct (IHe1 R1 TUnit Hnd Hcells HRS1 Hscrutinee)
      as [Hvalue | [s' [e1' Hstep]]].
    + pose proof (canonical_unit _ _ _ Hvalue Hscrutinee) as Heq. subst e1.
      right. exists s, e2. constructor.
    + right. exists s', (LetUnit e1' e2). constructor. exact Hstep.
  - destruct Hhead as [U1 [U2 [R1 [R2 [b [c
      [Heq [HU [HR [Hleft Hright]]]]]]]]]].
    subst a. apply splitM_nil_inv in HU as [-> ->].
    assert (HRS1 : split_incl R1 S).
    { eapply split_incl_left_trans; eassumption. }
    assert (HRS2 : split_incl R2 S).
    { eapply split_incl_right_trans; eassumption. }
    destruct (IHe1 R1 b Hnd Hcells HRS1 Hleft)
      as [Hvalue1 | [s' [e1' Hstep1]]].
    + destruct (IHe2 R2 c Hnd Hcells HRS2 Hright)
        as [Hvalue2 | [s' [e2' Hstep2]]].
      * left. constructor; assumption.
      * right. exists s', (Pair e1 e2'). apply StepPairRight; assumption.
    + right. exists s', (Pair e1' e2). apply StepPairLeft. exact Hstep1.
  - destruct Hhead as [U1 [U2 [R1 [R2 [b [c
      [HU [HR [Hscrutinee Hbody]]]]]]]]].
    apply splitM_nil_inv in HU as [-> ->].
    assert (HRS1 : split_incl R1 S).
    { eapply split_incl_left_trans; eassumption. }
    destruct (IHe1 R1 (TTensor b c) Hnd Hcells HRS1 Hscrutinee)
      as [Hvalue | [s' [e1' Hstep]]].
    + destruct (canonical_tensor _ _ _ _ _ Hvalue Hscrutinee)
        as [v1 [v2 [Heq [Hvalue1 Hvalue2]]]]. subst e1.
      right. exists s, (subst_l v1 (subst_l v2 e2)).
      apply StepLetPairBeta; assumption.
    + right. exists s', (LetPair e1' e2). constructor. exact Hstep.
  - left. constructor.
  - destruct Hhead as [b Hscrutinee].
    destruct (IHe Q (TWith a b) Hnd Hcells HQS Hscrutinee)
      as [Hvalue | [s' [e' Hstep]]].
    + destruct (canonical_with _ _ _ _ _ Hvalue Hscrutinee)
        as [e1 [e2 Heq]]. subst e.
      right. exists s, e1. constructor.
    + right. exists s', (Fst e'). constructor. exact Hstep.
  - destruct Hhead as [b Hscrutinee].
    destruct (IHe Q (TWith b a) Hnd Hcells HQS Hscrutinee)
      as [Hvalue | [s' [e' Hstep]]].
    + destruct (canonical_with _ _ _ _ _ Hvalue Hscrutinee)
        as [e1 [e2 Heq]]. subst e.
      right. exists s, e2. constructor.
    + right. exists s', (Snd e'). constructor. exact Hstep.
  - left. constructor.
  - destruct Hhead as [U1 [U2 [R1 [R2 [b
      [HU [HR [Hscrutinee Hbody]]]]]]]].
    apply splitM_nil_inv in HU as [-> ->].
    assert (HRS1 : split_incl R1 S).
    { eapply split_incl_left_trans; eassumption. }
    destruct (IHe1 R1 (TBang b) Hnd Hcells HRS1 Hscrutinee)
      as [Hvalue | [s' [e1' Hstep]]].
    + destruct (canonical_bang _ _ _ _ Hvalue Hscrutinee) as [body Heq].
      subst e1. right. exists s, (subst_u body e2). constructor.
    + right. exists s', (LetBang e1' e2). constructor. exact Hstep.
  - left. constructor.
  - destruct Hhead as [Heq Harg]. subst a.
    destruct (IHe Q TNat Hnd Hcells HQS Harg)
      as [Hvalue | [s' [e' Hstep]]].
    + destruct (canonical_nat _ _ _ Hvalue Harg) as [n Heq]. subst e.
      right. exists s, (Nat (Nat.succ n)). constructor.
    + right. exists s', (Succ e'). constructor. exact Hstep.
  - destruct Hhead as [Uc [Ur [Us [Uz [Rc [Rr [Rs [Rz
      [HUc [HUr [HRc [HRr [Hcount [Hstep_term Hseed]]]]]]]]]]]]]].
    apply splitM_nil_inv in HUc as [-> HUr0]. subst Ur.
    apply splitM_nil_inv in HUr as [-> ->].
    assert (HRcS : split_incl Rc S).
    { eapply split_incl_left_trans; eassumption. }
    assert (HRrS : split_incl Rr S).
    { eapply split_incl_right_trans; eassumption. }
    assert (HRsS : split_incl Rs S).
    { eapply split_incl_left_trans; eassumption. }
    assert (HRzS : split_incl Rz S).
    { eapply split_incl_right_trans; eassumption. }
    destruct (IHe1 Rc TNat Hnd Hcells HRcS Hcount)
      as [Hcount_value | [s' [count' Hcount_step]]].
    + destruct (IHe2 Rs (TBang (TLolli a a)) Hnd Hcells HRsS Hstep_term)
        as [Hstep_value | [s' [step_term' Hstep_step]]].
      * destruct (IHe3 Rz a Hnd Hcells HRzS Hseed)
          as [Hseed_value | [s' [seed' Hseed_step]]].
        -- destruct (canonical_nat _ _ _ Hcount_value Hcount) as [n Hn].
           destruct (canonical_bang _ _ _ _ Hstep_value Hstep_term)
             as [body Hbody]. subst e1. subst e2.
           destruct n.
           ++ right. exists s, e3. apply StepIterZero. exact Hseed_value.
           ++ right. exists s,
                (Iter (Nat n) (Bang body) (App body e3)).
              apply StepIterSucc. exact Hseed_value.
        -- right. exists s', (Iter e1 e2 seed').
           apply StepIterSeed; assumption.
      * right. exists s', (Iter e1 step_term' e3).
        apply StepIterStep; assumption.
    + right. exists s', (Iter count' e2 e3).
      apply StepIterCount. exact Hcount_step.
  - left. constructor.
  - destruct Hhead as [Uc [Ub [Rc [Rb
      [HU [HR [Hcondition [Hthen Helse]]]]]]]].
    apply splitM_nil_inv in HU as [-> ->].
    assert (HRcS : split_incl Rc S).
    { eapply split_incl_left_trans; eassumption. }
    destruct (IHe1 Rc TBool Hnd Hcells HRcS Hcondition)
      as [Hvalue | [s' [condition' Hstep]]].
    + destruct (canonical_bool _ _ _ Hvalue Hcondition) as [b Heq]. subst e1.
      destruct b.
      * right. exists s, e2. constructor.
      * right. exists s, e3. constructor.
    + right. exists s', (If condition' e2 e3). constructor. exact Hstep.
  - destruct Hhead as [b [Heq Harg]]. subst a.
    destruct (IHe Q b Hnd Hcells HQS Harg)
      as [Hvalue | [s' [e' Hstep]]].
    + right. exists (store_insert (fresh s) e s), (Loc (fresh s)).
      apply StepNewValue. exact Hvalue.
    + right. exists s', (New e'). constructor. exact Hstep.
  - destruct Hhead as [U1 [U2 [R1 [R2 [b [c
      [Heq [HU [HR [Hleft Hright]]]]]]]]]].
    subst a. apply splitM_nil_inv in HU as [-> ->].
    assert (HRS1 : split_incl R1 S).
    { eapply split_incl_left_trans; eassumption. }
    assert (HRS2 : split_incl R2 S).
    { eapply split_incl_right_trans; eassumption. }
    destruct (IHe1 R1 (TRef b) Hnd Hcells HRS1 Hleft)
      as [Hvalue1 | [s' [e1' Hstep1]]].
    + destruct (IHe2 R2 c Hnd Hcells HRS2 Hright)
        as [Hvalue2 | [s' [e2' Hstep2]]].
      * destruct (canonical_ref _ _ _ _ Hvalue1 Hleft) as [l Heq]. subst e1.
        assert (HinR1 : In (l, b) R1).
        { eapply typed_location_member. exact Hleft. }
        assert (HinS : In (l, b) S).
        { exact (split_incl_in R1 S (l, b) HRS1 HinR1). }
        destruct (cells_typed_lookup _ _ _ _ _ _ Hnd Hcells HinS)
          as [old [Rold [Hlookup [Hold_value Hold_type]]]].
        right. exists (store_update l e2 s), (Pair old (Loc l)).
        apply StepSwapValue; assumption.
      * right. exists s', (Swap e1 e2'). apply StepSwapRight; assumption.
    + right. exists s', (Swap e1' e2). apply StepSwapLeft. exact Hstep1.
  - destruct Hhead as [Heq Harg]. subst a.
    destruct (IHe Q (TRef TUnit) Hnd Hcells HQS Harg)
      as [Hvalue | [s' [e' Hstep]]].
    + destruct (canonical_ref _ _ _ _ Hvalue Harg) as [l Heq]. subst e.
      assert (HinR : In (l, TUnit) Q).
      { eapply typed_location_member. exact Harg. }
      assert (HinS : In (l, TUnit) S).
      { exact (split_incl_in Q S (l, TUnit) HQS HinR). }
      destruct (cells_typed_lookup _ _ _ _ _ _ Hnd Hcells HinS)
        as [v [Rv [Hlookup [Hcell_value Hcell_type]]]].
      pose proof (canonical_unit _ _ _ Hcell_value Hcell_type) as Heq.
      subst v. right. exists (store_remove l s), Unit.
      apply StepFreeLoc. exact Hlookup.
    + right. exists s', (Free e'). constructor. exact Hstep.
Qed.

Theorem progress : forall f s e a,
  configuration_typed f s e a ->
  value e \/ exists s' e', small_step (s, e) (s', e').
Proof.
  intros f s e a [Hbalance _].
  destruct Hbalance as
    [S Rterm Rrest Rcells Rfree
      Hnd Hcells Hterm Hterm_rest Hcells_free Hmode].
  eapply has_type_with_loc_progress with (S := S) (C := Rcells) (R := Rterm).
  - exact Hnd.
  - exact Hcells.
  - eapply split_incl_left. exact Hterm_rest.
  - exact Hterm.
Qed.

Corollary typed_configuration_not_stuck : forall f s e a,
  configuration_typed f s e a -> step (s, e) <> SStuck.
Proof.
  intros f s e a Htyped Hstuck.
  apply step_stuck_iff in Hstuck. destruct Hstuck as [Hnot_value Hnormal].
  destruct (progress _ _ _ _ Htyped) as [Hvalue | [s' [e' Hstep]]].
  - contradiction.
  - exact (Hnormal (s', e') Hstep).
Qed.
