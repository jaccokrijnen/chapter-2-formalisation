Require Import Lists.List.
Require Import Strings.String.

Fixpoint lookup {X:Type} (k : string) (l : list (string * X)) : option X :=
  match l with
  | nil => None
  | (j,x) :: l' => if String.eqb j k then Datatypes.Some x else lookup k l'
  end.
