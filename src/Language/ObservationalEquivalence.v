Require Import List.
Import ListNotations.
From Methodology Require Import
  Syntax
  Typing
  Evaluation
.

Definition eq_obs p q :=
  has_type [] p program_ty ->
  has_type [] q program_ty ->
  (forall n m,
    eval (Apply p (Const n)) (Const m) <->
    eval (Apply q (Const n)) (Const m)
  )
.

Notation "p '≃' q" := (eq_obs p q) (at level 10).
