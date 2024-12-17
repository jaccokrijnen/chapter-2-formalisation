Require Import
  String
  List
  Bool
  FunInd
  Lia
.
Import ListNotations.

From Equations Require Import
  Equations
.

From Methodology Require Import
  Util
  Syntax
  Scoping
  Inline.Specification
.

Module Sound.

  Axiom eqb : expr -> expr -> bool.
  Axiom eqb_eq : forall e1 e2, eqb e1 e2 = true <-> e1 = e2.

  Axiom lookup__lookup_tail: forall s env b,
    lookup s env = Some b <->
    (exists env',
      lookup_tail s env = Some (env', b)).

  Axiom inlining_refl : forall env e,
    inlining env e e.

  (* decision procedure that is sound, but does not check for inlining in
     inlined terms *)
  Function semi (env : list (string * binder_info)) (e1 e2 : expr) {struct e1} : bool :=
    match e1, e2 with
    | Var x, _ =>
        match lookup x env with
        | Some (bind_let t_x) => eqb t_x e2
        | _ => false
        end
        ||
        match e2 with
          | Var y => 
            match lookup x env with
            | Some b => String.eqb x y
            | None => false
            end
          | _ => false
        end
    | Let x s t, Let x' s' t' =>
        if not_in_envb x env then
          if String.eqb x x' then
            semi env s s' &&
            semi ((x, bind_let s) :: env) t t'
          else false
        else false
    | Apply s t, Apply s' t' =>
        semi env s s' && semi env t t'
    | LamAbs x t, LamAbs x' t' =>
        if not_in_envb x env then
          if String.eqb x x' then semi ((x, bind_lam) :: env) t t' else false
        else
          false
    | Plus s t, Plus s' t' =>
        semi env s s' && semi env t t'
    | Const n, Const n' => Nat.eqb n n'
    | _, _ => false
    end.

  Lemma semi_sound env e1 e2 : semi env e1 e2 = true -> inlining env e1 e2.
  Proof.
    revert env e2.
    induction e1; intros env e2 H_semi; rewrite semi_equation in H_semi.
    - rewrite orb_true_iff in H_semi.
      destruct H_semi as [H_var1 | H_var2].

      + (* inl_var_1 *)
        destruct (lookup s env) eqn:H_eq; try solve [inversion H_var1].
        destruct b eqn:H_eq_b; try solve [inversion H_var1].
        subst b.
        rewrite lookup__lookup_tail in H_eq.
        destruct H_eq as [env' H_eq].
        rewrite eqb_eq in H_var1.

        (* don't do recursive inlining *)
        assert (H_inl_e := inlining_refl env' e).

        (* equalities *)
        subst e2.
        eauto using inlining.

      + (* inl_var_2 *)
        destruct e2; try solve [inversion H_var2].
        destruct (lookup s env) eqn:H_lookup; try solve [inversion H_var2].
        rewrite String.eqb_eq in H_var2.
        subst s0.
        eauto using inlining.

    - destruct e2; try solve [inversion H_semi].
      destruct (not_in_envb s env) eqn:H_nie; try solve [inversion H_semi].
      destruct (s =? s0)%string eqn:H_eq; try solve [inversion H_semi].

      rewrite String.eqb_eq in H_eq.
      rewrite andb_true_iff in H_semi; destruct H_semi as [H_e1 H_e2].
      rewrite <- not_in_envb_correct in H_nie.

      (* equalities for inlining constructor *)
      subst s0.

      eauto using inlining.

    - (* Apply *)
      destruct e2; try solve [inversion H_semi].
      rewrite andb_true_iff in H_semi; destruct H_semi as [H_e1 H_e2].
      eauto using inlining.

    - (* lam *)
      admit.

    - (* plus *)
      admit.

    - (* const *)
      admit.
  Admitted.

End Sound.

Module Structural.
  (* Structural recursion, but with different environment shape: partial application
  * of the RHS with its env
  *)
  Fixpoint dec (env : list (string * (expr -> bool))) (e1 e2 : expr) : bool :=
    match e1, e2 with
    | Var x, _ =>
        match lookup x env with
        | Some dec_t => dec_t e2
        | None => false
        end
        ||
        match e2 with
          | Var y => String.eqb x y
          | _ => false
        end
    | Let x s t, Let x' s' t' =>
        if String.eqb x x' then
          dec env s s' &&
          dec ((x, dec env s) :: env) t t'
        else false
    | Apply s t, Apply s' t' =>
        dec env s s' && dec env t t'
    | LamAbs x t, LamAbs x' t' =>
        if String.eqb x x' then dec env t t' else false
    | Plus s t, Plus s' t' =>
        dec env s s' && dec env t t'
    | Const n, Const n' => Nat.eqb n n'
    | _, _ => false
    end.

End Structural.

Module WellFounded.
  (* Use equations, with the termination argument that
     the size of ctx + size of first expression decreases.

    pro: the definition is closer to the translation relation, with the exact same environment
    con: it does not reduce with cbv, only vm_compute. Presumably because it gets
         stuck on some opaque proof? Reflexivity reduces it, so that may be fine.
  *)

  Fixpoint size (e : expr) : nat :=
    match e with
    | Var _ => 1
    | Let _ e1 e2 => 1 + size e1 + size e2
    | Apply e1 e2 => 1 + size e1 + size e2
    | LamAbs _ e1 => 1 + size e1
    | Plus e1 e2 => 1 + size e1 + size e2
    | Const _ => 1
    end.

  Equations size_ctx (B : ctx) : nat :=
    size_ctx nil := 0;
    size_ctx ((_, bind_let t) :: B) := size t + size_ctx B;
    size_ctx ((_, bind_lam) :: B) := size_ctx B
  .

  Lemma lookup_tail__le x B B' e :
    lookup_tail x B = Some (B', bind_let e) -> size e + size_ctx B' <= size_ctx B
  .
  Proof.
    funelim (lookup_tail x B).
    - autorewrite with lookup_tail.
      inversion 1.
    - intros H_eq.
      autorewrite with lookup_tail in H_eq.
      destruct (String.eqb j k) eqn:H_eqb.
      + inversion H_eq; subst.
        autorewrite with size_ctx.
        auto.
      + specialize (H _ _ H_eq).
        destruct x;
        autorewrite with size_ctx;
        lia.
  Defined.

  Equations? dec (B : ctx) (e1 e2 : expr) : bool
    by wf (size_ctx B + size e1) lt :=
    dec B (Var x) e2 :=
        match lookup_tail x B
          as r return lookup_tail x B = r -> _ with
        | Some (B', bind_let t) => fun H_eq => dec B' t e2
        | _         => fun _ => false
        end eq_refl ||
        match e2 with
          | Var y => String.eqb x y
          | _ => false
        end
    ;
    dec B (Let x s t) (Let x' s' t') :=
      if not_in_envb x B then
        if String.eqb x x' then
          dec B s s' &&
          dec ((x, bind_let s) :: B) t t'
        else false
      else
        false;
    dec B (Apply s t) (Apply s' t') :=
        dec B s s' && dec B t t';
    dec B (LamAbs x t) (LamAbs x' t') :=
      if not_in_envb x B then
        if String.eqb x x' then dec ((x, bind_lam) :: B) t t' else false
      else
        false;
    dec B (Plus s t) (Plus s' t') :=
        dec B s s' && dec B t t';
    dec B (Const n) (Const n') := Nat.eqb n n';
    dec B _ _ := false
  .
  Proof.
  all: try lia.
  - apply lookup_tail__le in H_eq.
    lia.
  - autorewrite with size_ctx. 
    lia.
  - autorewrite with size_ctx.
    lia.
  Defined.


  Import Bool.

  Lemma sound B e1 e2 : dec B e1 e2 = true -> inlining B e1 e2.
  Proof.
    funelim (dec B e1 e2).
    {
    intros H. rewrite H in Heqcall. clear H.
    apply orb_prop in Heqcall.
    destruct Heqcall.
    all: admit.
    }
  Admitted.

End WellFounded.


