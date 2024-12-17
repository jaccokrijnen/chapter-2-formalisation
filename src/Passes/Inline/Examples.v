Require Import
  String
  List
.
Import ListNotations.

From Methodology Require Import
  Syntax
  Inline.Specification
  Inline.Automation
.


  Section Examples.
    Definition t :=
      Let "x" (Const 3)
        (Plus (Var "x") (Var "x")).

    Definition t' :=
      Let "x" (Const 3)
        (Plus (Var "x") (Const 3))
    .

    Eval cbv in (Structural.dec [] t t').

    Eval cbv in (WellFounded.dec [] t t').
    Eval vm_compute in (WellFounded.dec [] t t').
  End Examples.


