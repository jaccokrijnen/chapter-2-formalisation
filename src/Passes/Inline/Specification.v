Require Import
  String
  List
.
Import ListNotations.

From Equations Require Import
  Equations.

From Methodology Require Import
  Util
  Syntax
  Scoping
.


Inductive binder_info :=
  | bind_lam : binder_info
  | bind_let : expr -> binder_info
.

Definition ctx := list (string * binder_info).

Equations lookup_tail : string -> ctx -> option (ctx * binder_info) :=
  lookup_tail k nil := None;
  lookup_tail k ((j, x) :: B) := if String.eqb j k
      then Datatypes.Some (B, x)
      else lookup_tail k B
  .


Inductive not_in_env : string -> list (string * binder_info) -> Prop :=
  | nie_nil x : not_in_env x []
  | nie_cons_let x y t B :
      x <> y ->
      not_free_in x t ->
      not_in_env x B ->
      not_in_env x ((y, bind_let t) :: B)
  | nie_cons_lam x y B :
      x <> y ->
      not_in_env x B ->
      not_in_env x ((y, bind_lam) :: B)
  .


Lemma not_in_env__lookup_tail x Γ :
  not_in_env x Γ ->
  lookup_tail x Γ = None.
Proof.
Admitted.


Fixpoint not_in_envb (x : string) (env : list (string * binder_info)) : bool :=
  match env with
  | [] => true
  | (y, bind_lam) :: env' =>
      if String.eqb x y then
        false
      else
        not_in_envb x env'
  | (y, bind_let t) :: env' =>
      if String.eqb x y then
        false
      else
        not_free_inb x t && not_in_envb x env'
  end.



Lemma not_in_envb_correct : forall x env,
  not_in_env x env <-> not_in_envb x env = true.
Proof.
  intros x env.
  split.
  - (* -> direction *)
    intros H.
    induction H.
    + (* nie_nil *)
      simpl. reflexivity.
    + (* nie_cons_let *)
      simpl.
      rewrite <- String.eqb_neq in H.
      rewrite H. rewrite not_free_inb_correct in H0.
      rewrite H0, IHnot_in_env. reflexivity.
    + (* nie_cons_lam *)
      simpl.
      rewrite <- String.eqb_neq in H.
      rewrite H, IHnot_in_env. reflexivity.
  - (* <- direction *)
    generalize dependent x.
    induction env as [| [y b] env' IH].
    + intros x H.
      constructor.
    + intros x H.
      simpl in H.
      destruct b.
      * (* Case: bind_lam *)
        destruct (String.eqb x y) eqn:Heq.
        -- (* x = y *)
           rewrite String.eqb_eq in Heq. subst. discriminate H.
        -- (* x <> y *)
           rewrite String.eqb_neq in Heq.
           constructor; try assumption.
           apply IH. assumption.
      * (* Case: bind_let t *)
        destruct (String.eqb x y) eqn:Heq.
        -- (* x = y *)
           rewrite String.eqb_eq in Heq. subst. discriminate H.
        -- (* x <> y *)
           rewrite String.eqb_neq in Heq.
           apply Bool.andb_true_iff in H as [H1 H2].
           constructor; try assumption.
           ++ apply not_free_inb_correct. assumption.
           ++ apply IH. assumption.
Qed.


Inductive inlining :
  ctx -> expr -> expr -> Prop :=
  | inl_var_1 {B B_t x t t'} :
      lookup_tail x B = Some (B_t, bind_let t) ->
      inlining B_t t t' ->
      inlining B (Var x) t'
  | inl_var_2 {env x b} :
      lookup x env = Some b ->     (* For enforcing well-scopedness of term *)
      inlining env (Var x) (Var x)
  | inl_let {env x s s' t t'} :
      not_in_env x env ->
      inlining env s s' ->
      inlining ((x, bind_let s) :: env) t t' ->
      inlining env (Let x  s t) (Let x s' t')
  | inl_app {env s s' t t'} :
      inlining env s s' ->
      inlining env t t' ->
      inlining env (Apply s t) (Apply s' t')
  | inl_lam {env x t t'} :
      not_in_env x env -> 
      inlining ((x, bind_lam) :: env) t t' ->
      inlining env (LamAbs x t) (LamAbs x t')

  | inl_plus {env s s' t t'} :
      inlining env s s' ->
      inlining env t t' ->
      inlining env (Plus s t) (Plus s' t')
  | inl_const {env n} :
      inlining env (Const n) (Const n)
 .

  Lemma not_in_env__inlining_1 x Γ t t' :
    not_in_env x Γ ->
    inlining Γ t t' ->
    not_free_in x t.
    Proof.
  Admitted.

  Lemma not_in_env__inlining_2 x Γ t t' :
    not_in_env x Γ ->
    inlining Γ t t' ->
    not_free_in x t'.
  Proof. 
  Admitted.
