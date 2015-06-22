(* Runs on top of https://github.com/gmalecha/template-coq *)
Require Import Template.Template.

Require Import Coq.Strings.String.
Require Import Coq.Program.Program.
Require Import Coq.PArith.BinPos.
Local Open Scope string_scope.
Local Open Scope positive_scope.

Require Export quote_term.
Require Export quote_has_type.

Definition Preterm := Ast.term.
Quote Definition Preterm' := Ast.term.
Definition Context := Ast.program.

Notation "‘Preterm’" := Preterm'.

Fixpoint contextLookupConstr (name : string) (ctx : Context)
: option Ast.term
  := match ctx with
       | Ast.PConstr name' term ctx'
         => if string_dec name name'
            then Some term
            else contextLookupConstr name ctx'
       | Ast.PType _ _ ctx'
         => contextLookupConstr name ctx'
       | Ast.PAxiom _ ctx'
         => contextLookupConstr name ctx'
       | Ast.PIn _
         => None
     end.

Fixpoint contextLookupType (name : string) (ctx : Context)
: option (list (Ast.ident * Ast.inductive_body))
  := match ctx with
       | Ast.PConstr _ _ ctx'
         => contextLookupType name ctx'
       | Ast.PType name' body ctx'
         => if string_dec name name'
            then Some body
            else contextLookupType name ctx'
       | Ast.PAxiom _ ctx'
         => contextLookupType name ctx'
       | Ast.PIn _
         => None
     end.

Fixpoint contextLookupAxiom (name : string) (ctx : Context)
: option unit
  := match ctx with
       | Ast.PConstr _ _ ctx'
         => contextLookupAxiom name ctx'
       | Ast.PType _ _ ctx'
         => contextLookupAxiom name ctx'
       | Ast.PAxiom name' ctx'
         => if string_dec name name'
            then Some tt
            else contextLookupAxiom name ctx'
       | Ast.PIn _
         => None
     end.

Fixpoint contextGetPIn (ctx : Context)
: Ast.term
  := match ctx with
       | Ast.PConstr _ _ ctx'
         => contextGetPIn ctx'
       | Ast.PType _ _ ctx'
         => contextGetPIn ctx'
       | Ast.PAxiom _ ctx'
         => contextGetPIn ctx'
       | Ast.PIn body
         => body
     end.

Notation "x ‘→’ y" := (Ast.tProd Ast.nAnon x y) (at level 99, right associativity, y at level 200).
Notation "x ‘’ y" := (Ast.tApp x (cons y nil )) (at level 15, left associativity).

Axiom X : Type.
Quote Definition qX := X.
Check qX : Preterm.
Notation "‘X’" := qX.

Definition box (T : Preterm) : Type
  := { t : Preterm & has_type t T }.

Notation "□" := box.

Axiom f : □ ‘X’ -> X.
Quote Definition qf := f.
Check qf : Preterm.
Notation "‘f’" := qf.

(*Quote Recursively Definition Γ :=
  (let dummy_sigma := sigT in
   let dummy_X := X in
   has_type : Preterm -> Preterm -> Type).*)

Notation get_unfold_one qrterm
  := (let x := match contextGetPIn qrterm as p
                     return match p with
                              | Ast.tConst _ => option Ast.term
                              | _ => unit
                            end
               with
                 | Ast.tConst name
                   => contextLookupConstr name qrterm
                 | _ => tt
               end in
      match x as x' return match x' with
                             | Some _ => _
                             | None => unit
                           end
      with
        | Some k => k
        | None => tt
      end).

Definition box' : Preterm.
Proof.
  let term := (eval cbv delta in box) in
  quote_term term (fun x => exact x).
Defined.
(*Quote Recursively Definition box'' := box'.
Definition box''' := Eval simpl in get_unfold_one box''.*)
