(** * Call-by-value evaluation contexts *)

From Stdlib Require Import List.
From DILLref Require Import Prelude Ty Syntax Mask Split Substitution NatMap.
From DILLref Require Import Store StoreTyping StoreTypingInversion Semantics.
Import ListNotations.

(** A typed context transforms a hole with lexical demand [Uh], location
    context [Rh] and type [ah] into a complete term. *)
Inductive typed_eval_context (f : flag) (G L : list ty) :
    eval_context -> mask -> store_sig -> ty ->
    mask -> store_sig -> ty -> Prop :=
  | TCtxHole : forall U R a,
      typed_eval_context f G L ECHole U R a U R a
  | TCtxAppFun : forall K e2 Uh Rh ah U U1 U2 R R1 R2 a b,
      typed_eval_context f G L K Uh Rh ah U1 R1 (TLolli a b) ->
      has_type_with_loc f G L U2 R2 e2 a ->
      SplitM U U1 U2 -> Split R R1 R2 ->
      typed_eval_context f G L (ECAppFun K e2) Uh Rh ah U R b
  | TCtxAppArg : forall v1 K Uh Rh ah U U1 U2 R R1 R2 a b,
      value v1 -> has_type_with_loc f G L U1 R1 v1 (TLolli a b) ->
      typed_eval_context f G L K Uh Rh ah U2 R2 a ->
      SplitM U U1 U2 -> Split R R1 R2 ->
      typed_eval_context f G L (ECAppArg v1 K) Uh Rh ah U R b
  | TCtxLetUnit : forall K body Uh Rh ah U U1 U2 R R1 R2 a,
      typed_eval_context f G L K Uh Rh ah U1 R1 TUnit ->
      has_type_with_loc f G L U2 R2 body a ->
      SplitM U U1 U2 -> Split R R1 R2 ->
      typed_eval_context f G L (ECLetUnit K body) Uh Rh ah U R a
  | TCtxPairLeft : forall K e2 Uh Rh ah U U1 U2 R R1 R2 a b,
      typed_eval_context f G L K Uh Rh ah U1 R1 a ->
      has_type_with_loc f G L U2 R2 e2 b ->
      SplitM U U1 U2 -> Split R R1 R2 ->
      typed_eval_context f G L (ECPairLeft K e2) Uh Rh ah U R (TTensor a b)
  | TCtxPairRight : forall v1 K Uh Rh ah U U1 U2 R R1 R2 a b,
      value v1 -> has_type_with_loc f G L U1 R1 v1 a ->
      typed_eval_context f G L K Uh Rh ah U2 R2 b ->
      SplitM U U1 U2 -> Split R R1 R2 ->
      typed_eval_context f G L (ECPairRight v1 K) Uh Rh ah U R (TTensor a b)
  | TCtxLetPair : forall K body Uh Rh ah U U1 U2 R R1 R2 a b c,
      typed_eval_context f G L K Uh Rh ah U1 R1 (TTensor a b) ->
      has_type_with_loc f G (b :: a :: L) (true :: true :: U2) R2 body c ->
      SplitM U U1 U2 -> Split R R1 R2 ->
      typed_eval_context f G L (ECLetPair K body) Uh Rh ah U R c
  | TCtxFst : forall K Uh Rh ah U R a b,
      typed_eval_context f G L K Uh Rh ah U R (TWith a b) ->
      typed_eval_context f G L (ECFst K) Uh Rh ah U R a
  | TCtxSnd : forall K Uh Rh ah U R a b,
      typed_eval_context f G L K Uh Rh ah U R (TWith a b) ->
      typed_eval_context f G L (ECSnd K) Uh Rh ah U R b
  | TCtxLetBang : forall K body Uh Rh ah U U1 U2 R R1 R2 a b,
      typed_eval_context f G L K Uh Rh ah U1 R1 (TBang a) ->
      has_type_with_loc f (a :: G) L U2 R2 body b ->
      SplitM U U1 U2 -> Split R R1 R2 ->
      typed_eval_context f G L (ECLetBang K body) Uh Rh ah U R b
  | TCtxSucc : forall K Uh Rh ah U R,
      typed_eval_context f G L K Uh Rh ah U R TNat ->
      typed_eval_context f G L (ECSucc K) Uh Rh ah U R TNat
  | TCtxIterCount : forall K step_term seed Uh Rh ah U Uc Ur Us Uz
      R Rc Rr Rs Rz a,
      typed_eval_context f G L K Uh Rh ah Uc Rc TNat ->
      has_type_with_loc f G L Us Rs step_term (TBang (TLolli a a)) ->
      has_type_with_loc f G L Uz Rz seed a ->
      SplitM U Uc Ur -> SplitM Ur Us Uz ->
      Split R Rc Rr -> Split Rr Rs Rz ->
      typed_eval_context f G L (ECIterCount K step_term seed) Uh Rh ah U R a
  | TCtxIterStep : forall count K seed Uh Rh ah U Uc Ur Us Uz
      R Rc Rr Rs Rz a,
      value count -> has_type_with_loc f G L Uc Rc count TNat ->
      typed_eval_context f G L K Uh Rh ah Us Rs (TBang (TLolli a a)) ->
      has_type_with_loc f G L Uz Rz seed a ->
      SplitM U Uc Ur -> SplitM Ur Us Uz ->
      Split R Rc Rr -> Split Rr Rs Rz ->
      typed_eval_context f G L (ECIterStep count K seed) Uh Rh ah U R a
  | TCtxIterSeed : forall count step_term K Uh Rh ah U Uc Ur Us Uz
      R Rc Rr Rs Rz a,
      value count -> value step_term ->
      has_type_with_loc f G L Uc Rc count TNat ->
      has_type_with_loc f G L Us Rs step_term (TBang (TLolli a a)) ->
      typed_eval_context f G L K Uh Rh ah Uz Rz a ->
      SplitM U Uc Ur -> SplitM Ur Us Uz ->
      Split R Rc Rr -> Split Rr Rs Rz ->
      typed_eval_context f G L (ECIterSeed count step_term K) Uh Rh ah U R a
  | TCtxIf : forall K e1 e2 Uh Rh ah U Uc Ub R Rc Rb a,
      typed_eval_context f G L K Uh Rh ah Uc Rc TBool ->
      has_type_with_loc f G L Ub Rb e1 a ->
      has_type_with_loc f G L Ub Rb e2 a ->
      SplitM U Uc Ub -> Split R Rc Rb ->
      typed_eval_context f G L (ECIf K e1 e2) Uh Rh ah U R a
  | TCtxNew : forall K Uh Rh ah U R a,
      typed_eval_context f G L K Uh Rh ah U R a ->
      typed_eval_context f G L (ECNew K) Uh Rh ah U R (TRef a)
  | TCtxSwapLeft : forall K e2 Uh Rh ah U U1 U2 R R1 R2 a b,
      typed_eval_context f G L K Uh Rh ah U1 R1 (TRef a) ->
      has_type_with_loc f G L U2 R2 e2 b ->
      SplitM U U1 U2 -> Split R R1 R2 ->
      typed_eval_context f G L (ECSwapLeft K e2)
        Uh Rh ah U R (TTensor a (TRef b))
  | TCtxSwapRight : forall v1 K Uh Rh ah U U1 U2 R R1 R2 a b,
      value v1 -> has_type_with_loc f G L U1 R1 v1 (TRef a) ->
      typed_eval_context f G L K Uh Rh ah U2 R2 b ->
      SplitM U U1 U2 -> Split R R1 R2 ->
      typed_eval_context f G L (ECSwapRight v1 K)
        Uh Rh ah U R (TTensor a (TRef b))
  | TCtxFree : forall K Uh Rh ah U R,
      typed_eval_context f G L K Uh Rh ah U R (TRef TUnit) ->
      typed_eval_context f G L (ECFree K) Uh Rh ah U R TUnit
  | TCtxWeak : forall K Uh Rh ah V Q U R a,
      f = Affine ->
      typed_eval_context f G L K Uh Rh ah V Q a ->
      mask_le V U -> split_incl Q R ->
      typed_eval_context f G L K Uh Rh ah U R a.

Lemma typed_eval_context_cbv : forall f G L K Uh Rh ah U R a,
  typed_eval_context f G L K Uh Rh ah U R a -> cbv_context K.
Proof.
  intros f G L K Uh Rh ah U R a H. induction H;
    eauto using cbv_context.
Qed.

Lemma typed_eval_context_adjust : forall f G L K Uh Rh ah V Q U R a,
  typed_eval_context f G L K Uh Rh ah V Q a ->
  (f = Linear -> V = U /\ Q = R) ->
  mask_le V U -> split_incl Q R ->
  typed_eval_context f G L K Uh Rh ah U R a.
Proof.
  intros f G L K Uh Rh ah V Q U R a Hcontext Hlinear HU HR.
  destruct f.
  - destruct (Hlinear eq_refl) as [-> ->]. exact Hcontext.
  - eapply TCtxWeak; [reflexivity | exact Hcontext | exact HU | exact HR].
Qed.

(** Inversion of [typed_eval_context_fill]. Any typing of a filled CBV
    context determines a type and resource demand for its hole. *)
Theorem typed_eval_context_decompose : forall f G L K,
  cbv_context K -> forall e U R a,
  has_type_with_loc f G L U R (plug K e) a ->
  exists Uh Rh ah,
    typed_eval_context f G L K Uh Rh ah U R a /\
    has_type_with_loc f G L Uh Rh e ah.
Proof.
  intros f G L K Hcontext. induction Hcontext;
    intros e Uout Rout result Htype; simpl in Htype.
  - exists Uout, Rout, result. split; [constructor | exact Htype].
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead.
    destruct Hhead as [U1 [U2 [R1 [R2 [arg [HU [HR [Hfun Harg]]]]]]]].
    destruct (IHHcontext _ _ _ _ Hfun) as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxAppFun; eassumption.
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead.
    destruct Hhead as [U1 [U2 [R1 [R2 [arg [HU [HR [Hfun Harg]]]]]]]].
    destruct (IHHcontext _ _ _ _ Harg) as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxAppArg; eassumption.
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead.
    destruct Hhead as [U1 [U2 [R1 [R2 [HU [HR [Hscrutinee Hbody]]]]]]].
    destruct (IHHcontext _ _ _ _ Hscrutinee)
      as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxLetUnit; eassumption.
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead.
    destruct Hhead as [U1 [U2 [R1 [R2 [a [b
      [Heq [HU [HR [Hleft Hright]]]]]]]]]].
    subst result.
    destruct (IHHcontext _ _ _ _ Hleft) as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxPairLeft; eassumption.
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead.
    destruct Hhead as [U1 [U2 [R1 [R2 [a [b
      [Heq [HU [HR [Hleft Hright]]]]]]]]]].
    subst result.
    destruct (IHHcontext _ _ _ _ Hright) as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxPairRight; eassumption.
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead.
    destruct Hhead as [U1 [U2 [R1 [R2 [a [b
      [HU [HR [Hscrutinee Hbody]]]]]]]]].
    destruct (IHHcontext _ _ _ _ Hscrutinee)
      as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxLetPair; eassumption.
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead. destruct Hhead as [b Hchild].
    destruct (IHHcontext _ _ _ _ Hchild) as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxFst. exact Hctx.
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead. destruct Hhead as [a Hchild].
    destruct (IHHcontext _ _ _ _ Hchild) as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxSnd. exact Hctx.
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead.
    destruct Hhead as [U1 [U2 [R1 [R2 [a [HU [HR
      [Hscrutinee Hbody]]]]]]]].
    destruct (IHHcontext _ _ _ _ Hscrutinee)
      as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxLetBang; eassumption.
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead. destruct Hhead as [-> Hchild].
    destruct (IHHcontext _ _ _ _ Hchild) as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxSucc. exact Hctx.
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead.
    destruct Hhead as [Uc [Ur [Us [Uz [Rc [Rr [Rs [Rz
      [HU1 [HU2 [HR1 [HR2 [Hcount [Hstep Hseed]]]]]]]]]]]]]].
    destruct (IHHcontext _ _ _ _ Hcount) as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxIterCount; eassumption.
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead.
    destruct Hhead as [Uc [Ur [Us [Uz [Rc [Rr [Rs [Rz
      [HU1 [HU2 [HR1 [HR2 [Hcount [Hstep Hseed]]]]]]]]]]]]]].
    destruct (IHHcontext _ _ _ _ Hstep) as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxIterStep; eassumption.
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead.
    destruct Hhead as [Uc [Ur [Us [Uz [Rc [Rr [Rs [Rz
      [HU1 [HU2 [HR1 [HR2 [Hcount [Hstep Hseed]]]]]]]]]]]]]].
    destruct (IHHcontext _ _ _ _ Hseed) as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxIterSeed; eassumption.
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead.
    destruct Hhead as [Uc [Ub [Rc [Rb
      [HU [HR [Hcondition [Hthen Helse]]]]]]]].
    destruct (IHHcontext _ _ _ _ Hcondition)
      as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxIf; eassumption.
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead.
    destruct Hhead as [a [Heq Hchild]]. inversion Heq; subst.
    destruct (IHHcontext _ _ _ _ Hchild) as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxNew. exact Hctx.
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead.
    destruct Hhead as [U1 [U2 [R1 [R2 [a [b
      [Heq [HU [HR [Hleft Hright]]]]]]]]]].
    inversion Heq; subst.
    destruct (IHHcontext _ _ _ _ Hleft) as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxSwapLeft; eassumption.
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead.
    destruct Hhead as [U1 [U2 [R1 [R2 [a [b
      [Heq [HU [HR [Hleft Hright]]]]]]]]]].
    inversion Heq; subst.
    destruct (IHHcontext _ _ _ _ Hright) as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxSwapRight; eassumption.
  - destruct (has_type_with_loc_generation _ _ _ _ _ _ _ Htype)
      as [V [Q [Hlinear [HV [HQ Hhead]]]]].
    cbn [has_type_with_loc_head] in Hhead. destruct Hhead as [-> Hchild].
    destruct (IHHcontext _ _ _ _ Hchild) as [Uh [Rh [ah [Hctx Hhole]]]].
    exists Uh, Rh, ah. split; [| exact Hhole].
    eapply typed_eval_context_adjust; [| exact Hlinear | exact HV | exact HQ].
    eapply TCtxFree. exact Hctx.
Qed.

(** A closed resource scope also forces the hole exposed by a context
    decomposition to have an empty lexical mask. *)
Corollary typed_eval_context_decompose_closed : forall f G K,
  cbv_context K -> forall e R a,
  has_type_with_loc f G [] [] R (plug K e) a ->
  exists Rh ah,
    typed_eval_context f G [] K [] Rh ah [] R a /\
    has_type_with_loc f G [] [] Rh e ah.
Proof.
  intros f G K Hcontext e R a Htype.
  destruct (typed_eval_context_decompose
      f G [] K Hcontext e [] R a Htype)
    as [Uh [Rh [ah [Htyped Hhole]]]].
  assert (Uh = []) as ->.
  { eapply closed_mask_nil.
    - eapply has_type_with_loc_mask. exact Hhole.
    - reflexivity. }
  exists Rh, ah. split; assumption.
Qed.

Theorem typed_eval_context_fill : forall f G L K Uh Rh ah U R a,
  typed_eval_context f G L K Uh Rh ah U R a -> forall e,
  has_type_with_loc f G L Uh Rh e ah ->
  has_type_with_loc f G L U R (plug K e) a.
Proof.
  intros f G L K Uh Rh ah U R a Hcontext.
  induction Hcontext; intros e Hhole; simpl; try exact Hhole.
  all: try solve [econstructor; eauto].
  subst f. eapply TyLocWeak; eauto.
Qed.

(** The locations used by the hole form one side of a [Split]; the other
    side is the stable store frame owned by the surrounding context. *)
Theorem typed_eval_context_store_frame : forall f G L K Uh Rh ah U R a,
  typed_eval_context f G L K Uh Rh ah U R a ->
  exists Frame,
    Split R Rh Frame /\
    forall Rh' R' e,
      Split R' Rh' Frame ->
      has_type_with_loc f G L Uh Rh' e ah ->
      has_type_with_loc f G L U R' (plug K e) a.
Proof.
  intros f G L K Uh Rh ah U R a Hcontext.
  induction Hcontext as
    [U R a
    | K e2 Uh Rh ah U U1 U2 R R1 R2 a b Hctx IH Harg HU HR
    | v1 K Uh Rh ah U U1 U2 R R1 R2 a b Hvalue Hfun Hctx IH HU HR
    | K body Uh Rh ah U U1 U2 R R1 R2 a Hctx IH Hbody HU HR
    | K e2 Uh Rh ah U U1 U2 R R1 R2 a b Hctx IH Hright HU HR
    | v1 K Uh Rh ah U U1 U2 R R1 R2 a b Hvalue Hleft Hctx IH HU HR
    | K body Uh Rh ah U U1 U2 R R1 R2 a b c Hctx IH Hbody HU HR
    | K Uh Rh ah U R a b Hctx IH
    | K Uh Rh ah U R a b Hctx IH
    | K body Uh Rh ah U U1 U2 R R1 R2 a b Hctx IH Hbody HU HR
    | K Uh Rh ah U R Hctx IH
    | K step_term seed Uh Rh ah U Uc Ur Us Uz R Rc Rr Rs Rz a
        Hctx IH Hstep Hseed HU1 HU2 HR1 HR2
    | count K seed Uh Rh ah U Uc Ur Us Uz R Rc Rr Rs Rz a
        Hvalue Hcount Hctx IH Hseed HU1 HU2 HR1 HR2
    | count step_term K Uh Rh ah U Uc Ur Us Uz R Rc Rr Rs Rz a
        Hcount_value Hstep_value Hcount Hstep Hctx IH HU1 HU2 HR1 HR2
    | K e1 e2 Uh Rh ah U Uc Ub R Rc Rb a
        Hctx IH Hthen Helse HU HR
    | K Uh Rh ah U R a Hctx IH
    | K e2 Uh Rh ah U U1 U2 R R1 R2 a b Hctx IH Hright HU HR
    | v1 K Uh Rh ah U U1 U2 R R1 R2 a b Hvalue Hleft Hctx IH HU HR
    | K Uh Rh ah U R Hctx IH
    | K Uh Rh ah V Q U R a Haffine Hctx IH HV HQ].
  - exists []. split.
    + apply split_left.
    + intros Rh' R' e Hsplit Hhole.
      apply split_left_inv in Hsplit. subst Rh'. exact Hhole.
  - destruct IH as [Inner [Hinner Hfill]].
    destruct (split_assoc _ _ _ _ _ HR Hinner)
      as [Frame [Hframe Hrest]].
    exists Frame. split; [exact Hframe | ].
    intros Rh' R' e Hnew Hhole.
    destruct (split_unassoc _ _ _ _ _ Hnew Hrest)
      as [R1' [Houter Hactive]].
    eapply TyLocApp; [exact HU | exact Houter | | exact Harg].
    eapply Hfill; eassumption.
  - destruct IH as [Inner [Hinner Hfill]].
    destruct (split_assoc _ _ _ _ _ (split_comm _ _ _ HR) Hinner)
      as [Frame [Hframe Hrest]].
    exists Frame. split; [exact Hframe | ].
    intros Rh' R' e Hnew Hhole.
    destruct (split_unassoc _ _ _ _ _ Hnew Hrest)
      as [R2' [Houter Hactive]].
    eapply TyLocApp; [exact HU | apply split_comm; exact Houter | exact Hfun | ].
    eapply Hfill; eassumption.
  - destruct IH as [Inner [Hinner Hfill]].
    destruct (split_assoc _ _ _ _ _ HR Hinner)
      as [Frame [Hframe Hrest]].
    exists Frame. split; [exact Hframe | ].
    intros Rh' R' e Hnew Hhole.
    destruct (split_unassoc _ _ _ _ _ Hnew Hrest)
      as [R1' [Houter Hactive]].
    eapply TyLocLetUnit; [exact HU | exact Houter | | exact Hbody].
    eapply Hfill; eassumption.
  - destruct IH as [Inner [Hinner Hfill]].
    destruct (split_assoc _ _ _ _ _ HR Hinner)
      as [Frame [Hframe Hrest]].
    exists Frame. split; [exact Hframe | ].
    intros Rh' R' e Hnew Hhole.
    destruct (split_unassoc _ _ _ _ _ Hnew Hrest)
      as [R1' [Houter Hactive]].
    eapply TyLocPair; [exact HU | exact Houter | | exact Hright].
    eapply Hfill; eassumption.
  - destruct IH as [Inner [Hinner Hfill]].
    destruct (split_assoc _ _ _ _ _ (split_comm _ _ _ HR) Hinner)
      as [Frame [Hframe Hrest]].
    exists Frame. split; [exact Hframe | ].
    intros Rh' R' e Hnew Hhole.
    destruct (split_unassoc _ _ _ _ _ Hnew Hrest)
      as [R2' [Houter Hactive]].
    eapply TyLocPair; [exact HU | apply split_comm; exact Houter | exact Hleft | ].
    eapply Hfill; eassumption.
  - destruct IH as [Inner [Hinner Hfill]].
    destruct (split_assoc _ _ _ _ _ HR Hinner)
      as [Frame [Hframe Hrest]].
    exists Frame. split; [exact Hframe | ].
    intros Rh' R' e Hnew Hhole.
    destruct (split_unassoc _ _ _ _ _ Hnew Hrest)
      as [R1' [Houter Hactive]].
    eapply TyLocLetPair; [exact HU | exact Houter | | exact Hbody].
    eapply Hfill; eassumption.
  - destruct IH as [Frame [Hframe Hfill]]. exists Frame.
    split; [exact Hframe | ]. intros Rh' R' e Hnew Hhole.
    eapply TyLocFst. eapply Hfill; eassumption.
  - destruct IH as [Frame [Hframe Hfill]]. exists Frame.
    split; [exact Hframe | ]. intros Rh' R' e Hnew Hhole.
    eapply TyLocSnd. eapply Hfill; eassumption.
  - destruct IH as [Inner [Hinner Hfill]].
    destruct (split_assoc _ _ _ _ _ HR Hinner)
      as [Frame [Hframe Hrest]].
    exists Frame. split; [exact Hframe | ].
    intros Rh' R' e Hnew Hhole.
    destruct (split_unassoc _ _ _ _ _ Hnew Hrest)
      as [R1' [Houter Hactive]].
    eapply TyLocLetBang; [exact HU | exact Houter | | exact Hbody].
    eapply Hfill; eassumption.
  - destruct IH as [Frame [Hframe Hfill]]. exists Frame.
    split; [exact Hframe | ]. intros Rh' R' e Hnew Hhole.
    eapply TyLocSucc. eapply Hfill; eassumption.
  - destruct IH as [Inner [Hinner Hfill]].
    destruct (split_assoc _ _ _ _ _ HR1 Hinner)
      as [Frame [Hframe Hrest]].
    exists Frame. split; [exact Hframe | ].
    intros Rh' R' e Hnew Hhole.
    destruct (split_unassoc _ _ _ _ _ Hnew Hrest)
      as [Rc' [Houter Hactive]].
    eapply TyLocIter; [exact HU1 | exact HU2 | exact Houter | exact HR2 | | | ].
    + eapply Hfill; eassumption.
    + exact Hstep.
    + exact Hseed.
  - destruct IH as [Inner [Hinner Hfill]].
    destruct (split_assoc _ _ _ _ _ HR2 Hinner)
      as [InnerFrame [Hinner_frame Hseed_frame]].
    destruct (split_assoc _ _ _ _ _ (split_comm _ _ _ HR1) Hinner_frame)
      as [Frame [Hframe Hcount_frame]].
    exists Frame. split; [exact Hframe | ].
    intros Rh' R' e Hnew Hhole.
    destruct (split_unassoc _ _ _ _ _ Hnew Hcount_frame)
      as [Rr' [Houter Hinside]].
    destruct (split_unassoc _ _ _ _ _ Hinside Hseed_frame)
      as [Rs' [Hright Hactive]].
    eapply TyLocIter; [exact HU1 | exact HU2 |
      apply split_comm; exact Houter | exact Hright | exact Hcount | | exact Hseed].
    eapply Hfill; eassumption.
  - destruct IH as [Inner [Hinner Hfill]].
    destruct (split_assoc _ _ _ _ _ (split_comm _ _ _ HR2) Hinner)
      as [InnerFrame [Hinner_frame Hstep_frame]].
    destruct (split_assoc _ _ _ _ _ (split_comm _ _ _ HR1) Hinner_frame)
      as [Frame [Hframe Hcount_frame]].
    exists Frame. split; [exact Hframe | ].
    intros Rh' R' e Hnew Hhole.
    destruct (split_unassoc _ _ _ _ _ Hnew Hcount_frame)
      as [Rr' [Houter Hinside]].
    destruct (split_unassoc _ _ _ _ _ Hinside Hstep_frame)
      as [Rz' [Hright Hactive]].
    eapply TyLocIter; [exact HU1 | exact HU2 |
      apply split_comm; exact Houter | apply split_comm; exact Hright |
      exact Hcount | exact Hstep | ].
    eapply Hfill; eassumption.
  - destruct IH as [Inner [Hinner Hfill]].
    destruct (split_assoc _ _ _ _ _ HR Hinner)
      as [Frame [Hframe Hrest]].
    exists Frame. split; [exact Hframe | ].
    intros Rh' R' e Hnew Hhole.
    destruct (split_unassoc _ _ _ _ _ Hnew Hrest)
      as [Rc' [Houter Hactive]].
    eapply TyLocIf; [exact HU | exact Houter | | exact Hthen | exact Helse].
    eapply Hfill; eassumption.
  - destruct IH as [Frame [Hframe Hfill]]. exists Frame.
    split; [exact Hframe | ]. intros Rh' R' e Hnew Hhole.
    eapply TyLocNew. eapply Hfill; eassumption.
  - destruct IH as [Inner [Hinner Hfill]].
    destruct (split_assoc _ _ _ _ _ HR Hinner)
      as [Frame [Hframe Hrest]].
    exists Frame. split; [exact Hframe | ].
    intros Rh' R' e Hnew Hhole.
    destruct (split_unassoc _ _ _ _ _ Hnew Hrest)
      as [R1' [Houter Hactive]].
    eapply TyLocSwap; [exact HU | exact Houter | | exact Hright].
    eapply Hfill; eassumption.
  - destruct IH as [Inner [Hinner Hfill]].
    destruct (split_assoc _ _ _ _ _ (split_comm _ _ _ HR) Hinner)
      as [Frame [Hframe Hrest]].
    exists Frame. split; [exact Hframe | ].
    intros Rh' R' e Hnew Hhole.
    destruct (split_unassoc _ _ _ _ _ Hnew Hrest)
      as [R2' [Houter Hactive]].
    eapply TyLocSwap; [exact HU | apply split_comm; exact Houter | exact Hleft | ].
    eapply Hfill; eassumption.
  - destruct IH as [Frame [Hframe Hfill]]. exists Frame.
    split; [exact Hframe | ]. intros Rh' R' e Hnew Hhole.
    eapply TyLocFree. eapply Hfill; eassumption.
  - destruct IH as [Inner [Hinner Hfill]].
    destruct HQ as [unused HDrop].
    destruct (split_assoc _ _ _ _ _ HDrop Hinner)
      as [Frame [Hframe Hrest]].
    exists Frame. split; [exact Hframe | ].
    intros Rh' R' e Hnew Hhole.
    destruct (split_unassoc _ _ _ _ _ Hnew Hrest)
      as [Q' [Houter Hactive]].
    subst f. eapply TyLocWeak.
    + eapply Hfill; eassumption.
    + exact HV.
    + exists unused. exact Houter.
Qed.

Corollary typed_eval_context_replace : forall f G L K Uh Rh ah U R a e e',
  typed_eval_context f G L K Uh Rh ah U R a ->
  has_type_with_loc f G L Uh Rh e ah ->
  has_type_with_loc f G L Uh Rh e' ah ->
  has_type_with_loc f G L U R (plug K e) a /\
  has_type_with_loc f G L U R (plug K e') a.
Proof. intros. split; eapply typed_eval_context_fill; eassumption. Qed.
