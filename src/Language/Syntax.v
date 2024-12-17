Require Import String.

Inductive expr :=
  | Var : string -> expr
  | Let : string -> expr -> expr -> expr
  | Apply : expr -> expr -> expr
  | LamAbs : string -> expr -> expr
  | Plus : expr -> expr -> expr
  | Const : nat -> expr
.
