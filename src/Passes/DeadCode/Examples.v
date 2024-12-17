Require Import
  String
.
From Methodology Require Import
  DeadCode.Specification
.

Open Scope string_scope.

Definition t :=
  Let "x" (Const 3)
    (Plus (Var "y") (Var "y")).

Definition t' :=
  Plus (Var "y") (Var "y").

Lemma x_y : "x" <> "y".
Proof. inversion 1. Qed.

Lemma dc_t_t' : dead_code t t'.
Proof.
  unfold t, t'.
  auto using not_free_in, dead_code, x_y.
Qed.


From Methodology Require Import
  DeadCode.Automation.

Lemma dc_t_t'__reflection : dead_code t t'.
Proof.
  apply dead_code_equiv.
  reflexivity.
Qed.
