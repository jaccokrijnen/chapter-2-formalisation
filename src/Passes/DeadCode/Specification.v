Require Import String.
From Methodology Require Export
  Syntax
  Scoping
.
Inductive dead_code : expr -> expr -> Prop :=
| DC_Var {x} :
    dead_code (Var x) (Var x)
| DC_Let {x} {e1 e2 e1' e2'} :
    dead_code e1 e1' ->
    dead_code e2 e2' ->
    dead_code (Let x e1 e2) (Let x e1' e2')
| DC_Let_elim {x} {e1 e2 e2'} :
    not_free_in x e2' ->
    dead_code e2 e2' ->
    dead_code (Let x e1 e2) e2'
| DC_Apply {e1 e2 e1' e2'} :
    dead_code e1 e1' ->
    dead_code e2 e2' ->
    dead_code (Apply e1 e2) (Apply e1' e2')
| DC_LamAbs {x} {e e'} :
    dead_code e e' ->
    dead_code (LamAbs x e) (LamAbs x e')
| DC_Plus {e1 e2 e1' e2'} :
    dead_code e1 e1' ->
    dead_code e2 e2' ->
    dead_code (Plus e1 e2) (Plus e1' e2')
| DC_Const {n} :
    dead_code (Const n) (Const n)
.

Lemma dead_code_refl : forall t, dead_code t t.
Proof.
  intros t.
  induction t; eauto using dead_code.
Qed.

