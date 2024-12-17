Require Import
  Program.Equality
  String
  List
.
Import ListNotations.


From Methodology Require Import
  Scoping
  Syntax
  Typing
  Inline.Specification
  Evaluation
  ObservationalEquivalence
.

  Lemma inlining_weaken Γ x s t t' :
    not_in_env x Γ ->
    inlining Γ t t' ->
    inlining ((x, s) :: Γ) t t'.
  Proof.
  Admitted.

  Lemma inlining_strengthen Γ x s t t' :
    not_free_in x t ->
    inlining ((x, s) :: Γ) t t' ->
    inlining Γ t t'
  .
    Proof.
  Admitted.

  Lemma nfi__subst x s t :
    not_free_in x (subst x s t)
  .
    Proof.
  Admitted.


  (* substitutes in every let-bound term *)
  Function subst_ctx (x : string) (e : expr) (Γ : ctx) : ctx :=
  match Γ with
  | (x, bind_let t) :: Γ => (x, bind_let (subst x e t)) :: subst_ctx x e Γ
  | (x, bind_lam) :: Γ => (x, bind_lam) :: subst_ctx x e Γ
  | [] => []
  end
  .

  Lemma inlining_subst_lam Γ_pre Γ x s s' t t' :
    not_in_env x Γ ->
    inlining Γ s s' ->
    inlining (Γ_pre ++ (x, bind_lam) :: Γ) t t' ->
    inlining (subst_ctx x s Γ_pre ++ Γ) (subst x s t) (subst x s' t')
  .
  Proof.
    intros.
    apply inlining_strengthen with (x := x) (s := bind_lam).
    - apply nfi__subst.
    -
      (* Make explicit equalities to get the right IH *)
      remember (subst x s t) as t_subst.
      remember (subst x s' t') as t'_subst.
      generalize dependent t'.
      generalize dependent Heqt_subst.
      revert t_subst t'_subst.
      induction t; intros t_subst t'_subst H_eqt_subst t' H_inl_t H_eqt_substt'.
      + (* var y *)
        rename s0 into y.

        (* undo equalities *)
        inversion H_inl_t; subst.
        * (* inl_var_1, y has been inlined *)
          rewrite subst_equation.
          destruct (String.eqb x y) eqn:H_eq_x.
          ** (* x = y, impossible because x is bound to a lambda *)
            rewrite String.eqb_eq in H_eq_x; subst y.
            autorewrite with lookup_tail in H2.
  Admitted.


  Lemma inlining_subst_let Γ x s s' t t' :
    not_in_env x Γ ->
    inlining Γ s s' ->
    inlining ((x, bind_let s) :: Γ) t t' ->
    inlining Γ (subst x s t) (subst x s' t')
  .
    Proof.
  Admitted.



  Lemma eval__inliner Γ s t v :
    eval s v ->
    inlining Γ s t ->
    exists w,
      eval t w /\ inlining Γ v w.
  Proof.
    intros H_eval.
    revert t.
    dependent induction H_eval; intros t H_inl.
    - (* E_Const *)
      inversion H_inl; subst.
      exists (Const n).
      split; eauto using eval, inlining.
    - (* E_Lam*)
      inversion H_inl; subst.
      exists (LamAbs x t').
      split; eauto using eval, inlining;
      admit.
    - (* Apply *)
      inversion H_inl; subst.
      admit.
Admitted.

