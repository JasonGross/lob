(* -*- coq-prog-args: ("-emacs" "-top" "Wtype") -*- *)
Require Export Template.Template.
Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.

Local Open Scope string_scope.
Local Open Scope positive_scope.

Inductive W (A : Type) (B : A -> Type) : Type :=
  sup { w_label : A ; w_arg : B w_label -> W A B }.

Arguments sup {A B} _ _.
Arguments w_label {A B} _.
Arguments w_arg {A B} _ _.

Quote Recursively Definition qW_ctx' := W.
Quote Definition qW := W.
Quote Definition qsup := @sup.
Quote Definition qw_label := @w_label.
Quote Definition qw_arg := @w_arg.

Fixpoint get_ind_name (P : Ast.program)
  := match P with
       | Ast.PIn (Ast.tInd (Ast.mkInd name n)) => Some (name, n)
       | Ast.PIn _ => None
       | Ast.PType _ _ P' => get_ind_name P'
       | Ast.PConstr _ _ P' => get_ind_name P'
       | Ast.PAxiom _ _ P' => get_ind_name P'
     end.

Fixpoint lookup_PType_body' (name : string) (P : Ast.program)
  := match P with
       | Ast.PIn _ => None
       | Ast.PType name' bodies rest => if string_dec name name'
                                        then Some bodies
                                        else lookup_PType_body' name rest
       | Ast.PConstr _ _ P' => lookup_PType_body' name P'
       | Ast.PAxiom _ _ P' => lookup_PType_body' name P'
     end.

Definition lookup_PType_body0 (P : Ast.program)
  := match get_ind_name P with
       | Some (name, n) => match lookup_PType_body' name P with
                             | Some bodies => List.nth_error bodies n
                             | None => None
                           end
       | None => None
     end.

Definition lookup_PType_body (P : Ast.program)
  := match lookup_PType_body0 P as x return
           match x with
             | Some _ => _
             | None => unit
           end
     with
       | Some (name, body) => body
       | None => tt
     end.

Quote Recursively Definition prod' := prod.
Quote Recursively Definition sigT' := sigT.
Print W.
Definition Wnat
  := W (unit + unit) (fun x => match x with
                                 | inl _ => False
                                 | inr _ => unit
                               end).
Definition to : nat -> Wnat.
Proof.
  intro n.
  induction n.
  { exact (sup (inl tt) (fun x => match x : False with end)). }
  { exact (sup
Print prod'.


Definition qW_body : Ast.inductive_body
  := Eval hnf in
      match qW_ctx' as ls return
            match ls with
              | Ast.PType _ (_::_) _ => Ast.inductive_body
              | _ => unit
            end
      with
        | Ast.PType _ ((_, body)::_) _ => body
        | _ => tt
      end.
Print qW_body.
       |

Notation "‘∀’  ( x : T ) , P" := (Ast.tProd x T P)
  (at level 200, right associativity) : preterm_scope.
Notation "‘‘ x ’’" := (Ast.nNamed x)
  (at level 0, right associativity) : preterm_scope.

Local Open Scope preterm_scope.
Print qW_ctx.

Notation "‘λ’ ( x : T ) , t" := (
  (at level 200, x binder, y binder, right associativity).

Print Ast.term.
