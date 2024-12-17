Require Import
  String
  List
  Program.Equality
.
Import ListNotations.
From Methodology Require Import
  Syntax
  Scoping
  Typing
.
Require Import FunInd.

#[local]
Open Scope string_scope.

Function subst (x : string) (v : expr) (e : expr) : expr :=
  match e with
  | Var y => if String.eqb x y then v else Var y
  | Let y e1 e2 =>
      Let y (subst x v e1) (if String.eqb x y then e2 else subst x v e2)
  | Apply e1 e2 => Apply (subst x v e1) (subst x v e2)
  | LamAbs y body => LamAbs y (if String.eqb x y then body else subst x v body)
  | Plus e1 e2 => Plus (subst x v e1) (subst x v e2)
  | Const n => Const n
  end.


Inductive eval : expr -> expr -> Prop :=
| E_Const : forall n,
    eval (Const n) (Const n)
| E_Lam : forall x body,
    eval (LamAbs x body) (LamAbs x body)
| E_App : forall e1 e2 e3 x body,
    eval e1 (LamAbs x body) ->
    eval (subst x e2 body) e3 -> (* Call-by-name *)
    eval (Apply e1 e2) e3
| E_Plus : forall e1 e2 n1 n2,
    eval e1 (Const n1) ->
    eval e2 (Const n2) ->
    eval (Plus e1 e2) (Const (n1 + n2))
| E_Let : forall x e1 e2 e3,
    eval (subst x e1 e2) e3 ->
    eval (Let x e1 e2) e3
.

Inductive value : expr -> Prop :=
  | val_lam x t : value (LamAbs x t)
  | val_const n : value (Const n)
.

Lemma eval__value t v :
  eval t v -> value v.
Proof. Admitted.

Lemma value__nat v :
  value v ->
  has_type [] v ty_nat ->
  exists n, v = Const n.
Proof. Admitted.

Lemma not_free_in__subst x s t :
  not_free_in x t ->
  subst x s t = t.
Proof.
  induction t; intros H_nfi; setoid_rewrite subst_equation.
  - destruct (x =? s0) eqn:H_eq; [rewrite String.eqb_eq in H_eq; subst s0 | rewrite String.eqb_neq in H_eq ].
    + inversion H_nfi. contradiction.
    + reflexivity.
  - destruct (x =? s0) eqn:H_eq; [rewrite String.eqb_eq in H_eq; subst s0 | rewrite String.eqb_neq in H_eq ].
    + (* x = s0 *)
      inversion H_nfi; subst.
      * contradiction.
      * rewrite IHt1; auto.
    + (* x ≠ s0 *)
      inversion H_nfi;subst.
      * 
      rewrite IHt1; auto;
      rewrite IHt2; auto.
      * contradiction.
  - inversion H_nfi.
    rewrite IHt1; auto.
    rewrite IHt2; auto.
  - (* lam *)
    destruct (x =? s0) eqn:H_eq.
    + rewrite String.eqb_eq in H_eq.
      subst s0.
      reflexivity.
    + rewrite String.eqb_neq in H_eq.
      rewrite IHt; try reflexivity.
      inversion H_nfi; subst.
      * contradiction.
      * assumption.
   - (* plus *)
     inversion H_nfi.
     rewrite IHt1; auto.
     rewrite IHt2; auto.
   - (* const *)
     reflexivity.
Qed.

Lemma subst_preserves_nfi x y s t :
  not_free_in x s ->
  not_free_in x t ->
  not_free_in x (subst y s t).
Proof.
  induction t; intros H_nfi_s H_nfi_t; setoid_rewrite subst_equation.
  - (* var *)
    destruct (y =? s0); assumption.
  - (* let *)
    destruct (y =? s0) eqn:H_eq.
    + rewrite String.eqb_eq in H_eq. subst s0.
      inversion H_nfi_t; subst;
        auto using not_free_in.
    + inversion H_nfi_t; subst;
        auto using not_free_in.
  - inversion H_nfi_t. auto using not_free_in.
  - destruct (y =? s0);
    inversion H_nfi_t; auto using not_free_in.
  - inversion H_nfi_t. auto using not_free_in.
  - auto using not_free_in.
Qed.



Lemma subst_preserves_typing : forall x e1 T1 Γ e2 T2,
  has_type [] e1 T1 ->
  has_type ((x, T1) :: Γ) e2 T2 ->
  has_type Γ (subst x e1 e2) T2.
Proof.
Admitted.

Lemma preservation {t T v} :
  eval t v ->
  has_type [] t T ->
  has_type [] v T.
Proof.
  intros H_eval.
  revert T.
  induction H_eval; intros T; try solve [inversion 1; eauto using has_type].
  - (* Apply *)
    inversion 1; subst.
    apply IHH_eval2.
    eapply subst_preserves_typing.
    + eassumption.
    + assert (H_ty_lam : has_type [] (LamAbs x body) (ty_fun T1 T)) by auto.
      inversion H_ty_lam.
      auto.
  - (* Let *)
    inversion 1.
    eauto using subst_preserves_typing, has_type.
Qed.



Theorem subject_reduction : forall e e' T,
  has_type [] e T ->
  eval e e' ->
  has_type [] e' T.
Proof.
  intros e e' T Htype Heval.
  revert T Htype.
  dependent induction Heval; intros T Htype.
  - assumption.
  - assumption.
  - (* E_App *)
    inversion Htype. subst.
    specialize (IHHeval1 _ H2). clear H2.
    inversion IHHeval1. subst.
    eauto using subst_preserves_typing.
  - (* E_Plus *)
    inversion Htype. subst.
    eauto using has_type.
  - (* E_Let *)
  inversion Htype. subst.
  eauto using subst_preserves_typing.
Qed.
