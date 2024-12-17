Require Import String.
From Methodology Require Import Syntax.

Inductive not_free_in : string -> expr -> Prop :=
  | nfi_var { x y } :
      x <> y ->
      not_free_in x (Var y)
  | nfi_let_neq : forall x y e1 e2,
      x <> y ->
      not_free_in x e1 ->
      not_free_in x e2 ->
      not_free_in x (Let y e1 e2)
  | nfi_let_eq : forall x e1 e2,
      not_free_in x e1 ->
      not_free_in x (Let x e1 e2)
  | nfi_app : forall x e1 e2,
      not_free_in x e1 ->
      not_free_in x e2 ->
      not_free_in x (Apply e1 e2)
  | nfi_lam_eq : forall x e,
      not_free_in x (LamAbs x e)
  | nfi_lam_neq : forall x y e,
      x <> y ->
      not_free_in x e ->
      not_free_in x (LamAbs y e)
  | nfi_plus {x e1 e2} :
      not_free_in x e1 ->
      not_free_in x e2 ->
      not_free_in x (Plus e1 e2)
  | nfi_const {x n} :
      not_free_in x (Const n).


Fixpoint not_free_inb (x : string) (e : expr) : bool :=
  match e with
  | Var y => negb (String.eqb x y)
  | Let y e1 e2 =>
      if String.eqb x y then
        not_free_inb x e1
      else
        not_free_inb x e1 && not_free_inb x e2
  | Apply e1 e2 =>
      not_free_inb x e1 && not_free_inb x e2
  | LamAbs y e' =>
      if String.eqb x y then
        true
      else
        not_free_inb x e'
  | Plus e1 e2 =>
      not_free_inb x e1 && not_free_inb x e2
  | Const _ => true
  end.


Lemma not_free_inb_correct : forall x e,
  not_free_in x e <-> not_free_inb x e = true.
Proof.
  intros x e. 
  split.
  - (* -> Direction *)
    intros H.
    induction H; simpl.
    + (* nfi_var *)
      rewrite Bool.negb_true_iff.
      rewrite String.eqb_neq. assumption.
    + (* nfi_let_neq *)
      rewrite <- String.eqb_neq in H.
      rewrite H. rewrite IHnot_free_in1, IHnot_free_in2. reflexivity.
    + (* nfi_let_eq *)
      rewrite String.eqb_refl. assumption.
    + (* nfi_app *)
      rewrite IHnot_free_in1, IHnot_free_in2. reflexivity.
    + (* nfi_lam_eq *)
      rewrite String.eqb_refl. reflexivity.
    + (* nfi_lam_neq *)
      rewrite <- String.eqb_neq in H.
      rewrite H. assumption.
    + (* nfi_plus *)
      rewrite IHnot_free_in1, IHnot_free_in2. reflexivity.
    + (* nfi_const *)
      reflexivity.
  - (* <- Direction *)
    generalize dependent x.
    induction e; intros x H; simpl in H.
    + (* Var *)
      constructor.
      rewrite <- String.eqb_neq. 
      rewrite <- Bool.negb_true_iff.
      assumption.
    + (* Let *)
      destruct (String.eqb x s) eqn:Heq.
      * (* x = s *)
        rewrite String.eqb_eq in Heq. subst s.
        apply nfi_let_eq.
        auto.
      * (* x <> s *)
        apply Bool.andb_true_iff in H as [H1 H2].
        constructor.
        -- rewrite String.eqb_neq in Heq. assumption.
        -- apply IHe1. assumption.
        -- apply IHe2. assumption.
    + (* Apply *)
      apply Bool.andb_true_iff in H as [H1 H2].
      constructor; [apply IHe1 | apply IHe2]; assumption.
    + (* LamAbs *)
      destruct (String.eqb x s) eqn:Heq.
      * (* x = s *)
        rewrite eqb_eq in Heq.
          subst x.
        apply nfi_lam_eq.
      * (* x <> s *)
        rewrite String.eqb_neq in Heq.
        constructor.
        -- assumption.
        -- apply IHe. assumption.
    + (* Plus *)
      apply Bool.andb_true_iff in H as [H1 H2].
      constructor; [apply IHe1 | apply IHe2]; assumption.
    + (* Const *)
      constructor.
Qed.

Definition closed t := forall x, not_free_in x t.
