Require Import
  String
  Bool
  FunInd
  PeanoNat
.

From Methodology Require Import
  DeadCode.Specification
.

Function dead_codeb (e e' : expr) : bool :=
  match e, e' with
  | Var x, Var x' =>
      String.eqb x x'
  | Let x e1 e2, e2' =>
      (not_free_inb x e2' && dead_codeb e2 e2') ||
      (match e2' with
       | Let x' e1' e2'' =>
           String.eqb x x' &&
           dead_codeb e1 e1' &&
           dead_codeb e2 e2''
       | _ => false
       end)
  | Apply e1 e2, Apply e1' e2' =>
      dead_codeb e1 e1' &&
      dead_codeb e2 e2'
  | LamAbs x e, LamAbs x' e' =>
      String.eqb x x' &&
      dead_codeb e e'
  | Plus e1 e2, Plus e1' e2' =>
      dead_codeb e1 e1' &&
      dead_codeb e2 e2'
  | Const n, Const n' =>
      Nat.eqb n n'
  | _, _ =>
      false
  end.

Ltac impossible_cases H e :=
  destruct e; simpl in H; try discriminate.

Theorem dead_codeb_sound :
  forall e e', dead_codeb e e' = true -> dead_code e e'.
Proof.
  induction e; intros e' H.
  - (* Var *)
    impossible_cases H e'.
    apply String.eqb_eq in H. subst. constructor.
  - (* Let *)
    rewrite dead_codeb_equation in H.
    apply orb_true_iff in H as [H_elim | H_compat].
    + (* elim *)
      apply andb_true_iff in H_elim as [H_nfi H_dc_e2].
      rewrite <- not_free_inb_correct in H_nfi.
      specialize (IHe2 _ H_dc_e2); clear H_dc_e2.
      constructor; assumption.
    + (* compat *)
      impossible_cases H_compat e'.
      apply andb_true_iff in H_compat as [H H_dc_e2].
      apply andb_true_iff in H as [H_var_eq H_dc_e1].
      apply String.eqb_eq in H_var_eq. subst.
      constructor; [apply IHe1 | apply IHe2]; assumption.
  - (* Apply *)
    impossible_cases H e'.
    apply andb_true_iff in H as [H1 H2].
    constructor; [apply IHe1 | apply IHe2]; assumption.
  - (* LamAbs *)
    impossible_cases H e'.
    apply andb_true_iff in H as [H1 H2].
    apply String.eqb_eq in H1. subst.
    constructor. apply IHe. assumption.
  - (* Plus *)
    impossible_cases H e'.
    apply andb_true_iff in H as [H1 H2].
    constructor; [apply IHe1 | apply IHe2]; assumption.
  - (* Const *)
    impossible_cases H e'.
    apply Nat.eqb_eq in H. subst. constructor.
Qed.


Theorem dead_codeb_complete :
  forall e e', dead_code e e' -> dead_codeb e e' = true.
Proof.
  induction 1; simpl.
  - (* DC_Var *)
    apply String.eqb_refl.
  - (* DC_Let *)
    rewrite IHdead_code1, IHdead_code2. apply Bool.orb_true_iff. right.
    apply Bool.andb_true_iff. split.
    + apply andb_true_iff. split.
      * apply String.eqb_refl.
      * reflexivity.
    + reflexivity.
  - (* DC_Let_elim *)
    apply Bool.orb_true_iff. left.
    apply Bool.andb_true_iff. split.
    + apply not_free_inb_correct. assumption.
    + assumption.
  - (* DC_Apply *)
    apply Bool.andb_true_iff. split; assumption.
  - (* DC_LamAbs *)
    apply Bool.andb_true_iff. split.
    + apply String.eqb_refl.
    + assumption.
  - (* DC_Plus *)
    apply Bool.andb_true_iff. split; assumption.
  - (* DC_Const *)
    apply Nat.eqb_eq. reflexivity.
Qed.

Theorem dead_code_equiv : forall e1 e2,
  dead_codeb e1 e2 = true <-> dead_code e1 e2.
Proof.
  intros e1 e2.
  split.
  - apply dead_codeb_sound.
  - apply dead_codeb_complete.
Qed.
