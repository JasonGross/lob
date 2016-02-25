Require Import Coq.Strings.String Coq.Strings.Ascii.
Open Scope char_scope.
Open Scope string_scope.

Eval compute in Ascii.ascii_of_nat 10.

Fixpoint repr' (s : string) : string
  := match s with
     | "" => ""
     | String "010"%char s' => "\n" ++ repr' s'
     | String "034"%char s' => """""" ++ repr' s'
     | String ch s' => String ch (repr' s')
     end.
Definition repr s := """" ++ repr' s ++ """".

Eval compute in repr ("a" ++ (String "010"%char "") ++ "b""""").

Notation "\n" := (String "010"%char "") (only parsing).

Definition quine :=
let rest := "in ""let rest := "" ++ repr rest ++ \n ++ rest."
in "let rest := " ++ repr rest ++ \n ++ rest.
Eval compute in quine.
