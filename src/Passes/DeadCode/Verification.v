Require Import 
  Equality
  List
.
Import ListNotations.
From Methodology Require Import
  Syntax
  Scoping
  Typing
  DeadCode.Specification
  DeadCode.Automation
  Evaluation
  ObservationalEquivalence
.

Lemma dead_code__typing : forall Γ t t' T,
  dead_code t t' ->
  has_type Γ t T ->
  has_type Γ t' T
.
Proof.
Admitted.


Lemma dead_code__subst { s t s' t' } x :
  closed s' ->
  dead_code s s' ->
  dead_code t t' ->
  dead_code (subst x s t) (subst x s' t').
Proof.
  intros H_nfi Hdc_s Hdc_t.
  dependent induction Hdc_t.
  - (* Var *)
    setoid_rewrite subst_equation.
    destruct (String.eqb x x0) eqn:H_eq_x;
      auto using dead_code.
  - (* Let *)
    setoid_rewrite subst_equation.
    destruct (String.eqb x x0) eqn:H_eq_x;
      eauto using dead_code.
  - (* let elim *)
    rewrite subst_equation. (* only rewrite the first subst occurrence *)
    destruct (String.eqb x x0) eqn:H_eq_x.
    + (* x = x0 *)
      rewrite String.eqb_eq in H_eq_x. subst x0.
      apply DC_Let_elim.
      * auto using subst_preserves_nfi.
      * assert (H_subst : subst x s' e2' = e2') by auto using not_free_in__subst.
        rewrite H_subst.
        assumption.
    + (* x ≠ x0 *)
      unfold closed in *.
      constructor.
      * specialize (H_nfi x0).
        auto using subst_preserves_nfi.
      * assumption.
  - (* app *)
    setoid_rewrite subst_equation.
    auto using dead_code.
  - (* lam *)
    setoid_rewrite subst_equation.
    destruct (String.eqb x x0);
      auto using dead_code.
  - (* plus *)
    setoid_rewrite subst_equation.
    auto using dead_code.
  - (* const *)
    setoid_rewrite subst_equation.
    auto using dead_code.
Qed.

Lemma forward {s v t T} :
  has_type [] s T ->
  dead_code s t ->
  eval s v ->
  exists w,
    eval t w /\ dead_code v w.
Proof.
  intros H_ty Hdc Heval.
  generalize dependent t.
  generalize dependent T.
  (* Induction on the evaluation derivation *)
  induction Heval; intros T H_ty t H_dc; inversion H_dc; subst; clear H_dc.
  - (* const *)
    eexists.
    split; eauto using eval, dead_code.
  - (* lam *)
    eexists.
    split; eauto using eval, dead_code.
  - (* app *)
    inversion H_ty.
    specialize (IHHeval1 _ H4 _ H1) as [e1_v [H_eval_e1' H_DC_LamAbs]].
    inversion H_DC_LamAbs; subst. (* Get dc over the bodies *)
    rename e' into body'.

    assert (H_closed : closed e2'). {
      eapply has_type__closed.
      eapply dead_code__typing; try eassumption.
    }
    rename H10 into H_dc_body.
    specialize (dead_code__subst x H_closed H3 H_dc_body) as H_dc_subst.

    assert (H_ty_lam : has_type [] (LamAbs x body) (ty_fun T1 T))
      by apply (preservation Heval1 H4).
    assert (H_ty_body : has_type [] (subst x e2 body) T). {
     inversion H_ty_lam; subst.
     eapply subst_preserves_typing; eauto using has_type.
     }
    specialize (IHHeval2 _ H_ty_body _ H_dc_subst) as [w [H_eval_w H_dc_e3]].

    exists w; eauto using eval.
  - (* plus *)
    inversion H_ty; subst.
      specialize (IHHeval1 _ H4 _ H1) as [v [H_ev_e1 H_dc_v]].
      specialize (IHHeval2 _ H6 _ H3) as [w [H_ev_e2 H_dc_w]].
      inversion H_dc_v; subst.
      inversion H_dc_w; subst.
      eexists.
      split; eauto using eval, dead_code.
  - (* let *)
    assert (H_closed : closed e1'). {
      inversion H_ty.
      eapply has_type__closed.
      eapply dead_code__typing; try eassumption.
    }
    specialize (dead_code__subst x H_closed H3 H4) as H_dc_subst.
    assert (H_ty_subst : has_type [] (subst x e1 e2) T).
     { inversion H_ty; eapply subst_preserves_typing; eauto using has_type. }
    specialize (IHHeval _ H_ty_subst _ H_dc_subst) as [w [H_eval_w H_dc_e3]].
    exists w; eauto using eval.
  - (* let elim *)

    specialize (dead_code_refl e1) as H_dc_e1.
    assert (H_closed : closed e1). {
      inversion H_ty.
      eauto using has_type__closed.
    }
    specialize (dead_code__subst x H_closed H_dc_e1 H4) as H_dc_subst.
    assert (H_ty_subst : has_type [] (subst x e1 e2) T).
     { inversion H_ty; eapply subst_preserves_typing; eauto using has_type. }
    specialize (IHHeval _ H_ty_subst _ H_dc_subst) as [w [ H_eval H_dc]].
    rewrite not_free_in__subst in H_eval; auto.
    exists w; eauto using eval.
Qed.

Lemma backward {s w t T} :
  has_type [] s T ->
  dead_code s t ->
  eval t w ->
  exists v,
    eval s v /\ dead_code v w.
Proof.
(* similar to forward *)
Admitted.

Lemma dead_code__const {n m} :
  dead_code (Const n) (Const m) <-> n = m.
Proof.
  split.
  - inversion 1; reflexivity.
  - intros; subst. constructor.
Qed.



Lemma dead_code_correct : forall p q,
  dead_code p q ->
  p ≃ q.
Proof.
  intros p q H_dc H_ty_p H_ty_q n m.
  assert (H_DC_Apply : dead_code (Apply p (Const n)) (Apply q (Const n))).
    { apply DC_Apply; eauto using dead_code_refl. }
  split.
    - intros H_eval_app.
      assert (H_ty_app : has_type [] (Apply p (Const n)) ty_nat).
        { eauto using has_type. }
      specialize (forward H_ty_app H_DC_Apply H_eval_app) as [r [H_eval_app' H_dc_r]].
      inversion H_dc_r; subst.
      assumption.

    - intros H_eval_app.
      assert (H_ty_app : has_type [] (Apply p (Const n)) ty_nat).
        { eauto using has_type. }
      specialize (backward H_ty_app H_DC_Apply H_eval_app) as [r [H_eval_app' H_dc_r]].
      assert (exists c, r = Const c).
      {
        apply value__nat.
        - eauto using eval__value.
        - eauto using preservation.
      }
      destruct H as [c H_eq_c].
      subst r.
      inversion H_dc_r; subst.
      assumption.
Qed.
