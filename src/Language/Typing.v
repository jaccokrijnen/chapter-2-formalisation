Require Import String.
Require Import List.
Import ListNotations.
From Methodology Require Import
  Util
  Syntax
  Scoping.

Inductive ty :=
  | ty_nat : ty
  | ty_fun : ty -> ty -> ty.

Inductive has_type : list (string * ty) -> expr -> ty -> Prop :=
| T_Var : forall Γ x T,
    lookup x Γ = Some T ->
    has_type Γ (Var x) T
| T_Const : forall Γ n,
    has_type Γ (Const n) ty_nat
| T_Lam : forall Γ x T1 T2 body,
    has_type ((x, T1) :: Γ) body T2 ->
    has_type Γ (LamAbs x body) (ty_fun T1 T2)
| T_App : forall Γ e1 e2 T1 T2,
    has_type Γ e1 (ty_fun T1 T2) ->
    has_type Γ e2 T1 ->
    has_type Γ (Apply e1 e2) T2
| T_Plus : forall Γ e1 e2,
    has_type Γ e1 ty_nat ->
    has_type Γ e2 ty_nat ->
    has_type Γ (Plus e1 e2) ty_nat
| T_Let : forall Γ x e1 e2 T1 T2,
    has_type Γ e1 T1 ->
    has_type ((x, T1) :: Γ) e2 T2 ->
    has_type Γ (Let x e1 e2) T2.

Definition program_ty : ty := ty_fun ty_nat ty_nat.

Lemma has_type__closed {t T} : has_type [] t T -> closed t.
Proof.
Admitted.
