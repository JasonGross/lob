(* Runs on top of https://github.com/gmalecha/template-coq *)
Require Import Coq.Setoids.Setoid Coq.Classes.CMorphisms.
Require Template.Ast.

Set Asymmetric Patterns.

Require Import Coq.Strings.String.
Require Import Coq.Program.Program.
Require Import Coq.PArith.BinPos.
Local Open Scope string_scope.
Local Open Scope positive_scope.
Local Open Scope list_scope.

(*Require Export Lob.quote_term.*)
Require Import Lob.Notations.

Print Ast.term.
(*Require Import Template.Template.
Quote Definition foo := let x := 1 in x.
Print foo.
Quote Definition J := (fun {A : Type} {x} (P : forall y : A, x = y -> Type) (k : P x eq_refl) {y} (p : x = y)
                       => match p as p' in (_ = y') return P y' p' with
                            | eq_refl => k
                          end).
Print J.
Quote Definition negb := (fun b : bool => match b with true => false | false => true end).
Require Import JMeq.
Quote Definition JMeq_J := (fun {A : Type} {x : A} (P : forall B (y : B), JMeq x y -> Type) (k : P A x JMeq_refl) {B} {y} (p : @JMeq A x B y)
                       => match p as p' in (@JMeq _ _ B' y') return P B' y' p' with
                            | JMeq_refl => k
                          end).
Print JMeq_J.*)
Print Ast.mfixpoint.
Print Ast.def.

Inductive preinductive_body : Set :=
| mkpreinductive_body (ctors : list (Ast.ident * pretype))
with precontext_element : Set :=
| pconstr (name : Ast.name) (T : pretype) (body : preterm)
| ptype (name : Ast.ident) (bodies : list (Ast.ident * pretype * preinductive_body))
| paxiom (name : Ast.ident) (T : pretype)
| pbinder (name : Ast.name) (T : pretype)
with precontext : Set :=
| empty_precontext : precontext
| precontext_extend (Γ : precontext) (T : precontext_element)
with pretype : Set :=
| pretype_of_term (term : preterm)
with preterm : Set :=
| ptRel : nat -> preterm
| ptSort (univ_level : Ast.sort)
| ptProd (name : Ast.name) (A : pretype) (B : pretype)
| ptLambda (name : Ast.name) (A : pretype) (B : pretype) (body : preterm)
| ptLetIn (name : Ast.name) (A : pretype) (a : preterm) (B : pretype) (body : preterm)
| ptApp (A : pretype) (B : pretype) (f : preterm) (x : preterm)
| ptConst : string -> preterm
| ptInd  (T : pretype) (ind_name : string) (mut_ind_idx : nat)
| ptConstruct (T : pretype) (ind_name : string) (mut_ind_idx : nat) (ctor_idx : nat)
| ptCase (num_params : nat) (return_type : preterm) (indtype : pretype) (discriminee : preterm) (bodies : list (pretype * preterm))
| ptFix (type : pretype) (bodies : Ast.mfixpoint preterm) (fix_idx : nat).

Coercion pretype_of_term : preterm >-> pretype.
Coercion preterm_of_pretype (x : pretype)
  := match x with
       | pretype_of_term x' => x'
     end.

Definition subst_n_name_def
           (subst_n_name : preterm -> option nat -> preterm)
           (var_n : option nat)
           (in_term : Ast.def preterm)
: Ast.def preterm
  := match in_term with
       | {| Ast.dname := dname ; Ast.dtype := dtype ; Ast.dbody := dbody ; Ast.rarg := rarg |}
         => {| Ast.dname := dname;
               Ast.dtype := subst_n_name dtype var_n;
               Ast.dbody := subst_n_name dbody (option_map S var_n);
               Ast.rarg := rarg |}
     end.

Fixpoint subst_n_name (in_term : preterm) (subst_term : preterm) (var_n : option nat) (name : Ast.name) {struct in_term} : preterm
  := match in_term with
       | ptRel v => match var_n with
                      | Some var_n'
                        => match Compare_dec.lt_eq_lt_dec v var_n' with
                             | inleft (left _) => in_term
                             | inleft (right _) => subst_term
                             | inright _ => ptRel (pred v)
                           end
                      | None => in_term
                    end
       (*| ptVar name0 => match name with
                `             | pnNamed name1
                               => if String.string_dec name0 name1
                                  then subst_term
                                  else in_term
                             | pnAnon => in_term
                           end
       | ptMeta _ => in_term
       | ptEvar _ => in_term*)
       | ptSort _ => in_term
       (*| ptCast term0' kind term1'
         => Ast.tCast (subst_n_name term0' subst_term var_n name)
                      kind
                      (subst_n_name term1' subst_term var_n name)*)
       | ptProd name' term0' term1'
         => let new_name := match name, name' with
                              | Ast.nNamed n0, Ast.nNamed n1
                                => if String.string_dec n0 n1
                                   then Ast.nAnon
                                   else name
                              | _, _ => name
                            end in
            ptProd name'
                      (subst_n_name term0' subst_term var_n new_name)
                      (subst_n_name term1' subst_term (option_map S var_n) new_name)
       | ptLambda name' A' B' body'
         => let new_name := match name, name' with
                              | Ast.nNamed n0, Ast.nNamed n1
                                => if String.string_dec n0 n1
                                   then Ast.nAnon
                                   else name
                              | _, _ => name
                            end in
            ptLambda name'
                     (subst_n_name A' subst_term var_n name)
                     (subst_n_name B' subst_term (option_map S var_n) new_name)
                     (subst_n_name body' subst_term (option_map S var_n) new_name)
       | ptLetIn name' A' a' B' body'
         => let new_name := match name, name' with
                              | Ast.nNamed n0, Ast.nNamed n1
                                => if String.string_dec n0 n1
                                   then Ast.nAnon
                                   else name
                              | _, _ => name
                            end in
            ptLetIn name'
                       (subst_n_name A' subst_term var_n name)
                       (subst_n_name a' subst_term var_n name)
                       (subst_n_name B' subst_term var_n name)
                       (subst_n_name body' subst_term (option_map S var_n) new_name)
       | ptApp A B f arg
         => ptApp (subst_n_name A subst_term var_n name)
                  (subst_n_name B subst_term var_n name)
                  (subst_n_name f subst_term var_n name)
                  (subst_n_name arg subst_term var_n name)
       | ptConst _ => in_term
       | ptInd _ _ _ => in_term
       | ptConstruct _ _ _ _ => in_term
       | ptCase n term0' term1' term2' branches
         => ptCase n
                      (subst_n_name term0' subst_term var_n name)
                      (subst_n_name term1' subst_term var_n name)
                      (subst_n_name term2' subst_term var_n name)
                      (@List.map
                         (pretype * preterm) (pretype * preterm)
                         (fun type'_term' =>
                            (subst_n_name (fst type'_term') subst_term var_n name : pretype,
                             subst_n_name (snd type'_term') subst_term var_n name))
                         branches)
       | ptFix type0' term0' n
         => ptFix
              (subst_n_name type0' subst_term var_n name)
              (List.map (subst_n_name_def (fun term' var_n => subst_n_name term' subst_term var_n name) var_n) term0')
                     n
       (*| ptUnknown _ => in_term*)
     end.




Delimit Scope precontext_scope with pctx.
Bind Scope precontext_scope with precontext.

Delimit Scope precontext_element_scope with pctxe.
Bind Scope precontext_element_scope with precontext_element.

Notation ε₀ := empty_precontext.
Infix "▻" := precontext_extend : precontext_scope.
Notation "( x ; T )" := (pbinder x T) : precontext_element_scope.

Delimit Scope sort_scope with sort.
Bind Scope sort_scope with Ast.sort.

Definition umax (U1 U2 : Ast.sort) : Ast.sort
  := match U1, U2 with
       | Ast.sProp, _ => U2
       | _, Ast.sProp => U1
       | Ast.sSet, _ => U2
       | _, Ast.sSet => U1
       | Ast.sType U1', Ast.sType U2' => Ast.sType (Pos.max U1' U2')
     end.

Definition usucc (U : Ast.sort) : Ast.sort
  := match U with
       | Ast.sProp => Ast.sType 1
       | Ast.sSet => Ast.sType 1
       | Ast.sType i => Ast.sType (i + 1)
     end.

Notation "x .+1" := (usucc x) : sort_scope.

Definition ule (x y : Ast.sort) : Prop
  := match x, y with
       | Ast.sProp, _ => True
       | Ast.sSet, Ast.sProp => False
       | Ast.sSet, _ => True
       | Ast.sType _, Ast.sProp => False
       | Ast.sType _, Ast.sSet => False
       | Ast.sType i, Ast.sType j => i <= j
     end.

Infix "<=" := ule : sort_scope.

Definition ult x y := (x.+1 <= y)%sort.

Infix "<" := ult : sort_scope.

(*Set Printing Universes.
Check forall x: Type@{i}, (_ : Type@{j}).*)
Check ((let k := Prop : Type@{i} in forall x : Type@{i}, (_ : Prop)) : Prop).
Definition tProd_level (i j : Ast.sort) : Ast.sort
  := match j with
       | Ast.sProp => Ast.sProp
       | _ => umax (usucc i) j
     end.

Fixpoint precontext_app (Γ0 Γ1 : precontext) : precontext
  := match Γ1 with
       | ε₀ => Γ0
       | precontext_extend Γ1' T => precontext_app (Γ0 ▻ T) Γ1'
     end.

Infix "▻▻" := precontext_app : precontext_scope.

Inductive preinductive_body_good : preinductive_body -> Set :=
(*| mkpreinductive_body_good
  : forall (Γ : precontext) (ctors : list (Ast.ident * pretype))
  *)
with precontext_element_good : precontext -> precontext_element -> Set :=
| pconstr_good {Γ} {Γ_g : precontext_good Γ}
               (name : Ast.name)
               {T}
               {body} (body_good : preterm_good Γ body T)
  : precontext_element_good Γ (pconstr name T body)
(*| ptype_good {Γ} {Γ_g : precontext_good Γ}
             (name : Ast.ident)
             (bodies : list (Ast.ident * pretype * preinductive_body))*)
| paxiom_good {Γ} {Γ_g : precontext_good Γ}
              (name : Ast.ident)
              {T} (T_g : pretype_good Γ T)
  : precontext_element_good Γ (paxiom name T)
| pbinder_good {Γ} {Γ_g : precontext_good Γ}
               (name : Ast.name)
               {T} (T_g : pretype_good Γ T)
  : precontext_element_good Γ (pbinder name T)
with precontext_good : precontext -> Set :=
| empty_precontext_good : precontext_good empty_precontext
| precontext_extend_good {Γ} (Γ_g : precontext_good Γ) {T} (T_g : precontext_element_good Γ T) : precontext_good (Γ ▻ T)
with pretype_good : precontext -> pretype -> Set :=
(*| TYPE_good {Γ} (Γ_g : precontext_good Γ) (i : nat) : pretype_good Γ (TYPE i)
| ptProd_good {Γ} (Γ_g : precontext_good Γ)
              (x : Ast.name)
              {A} (A_g : pretype_good Γ A)
              {B} (B_g : pretype_good (Γ ▻ (x; A)) B)
  : pretype_good Γ (ptProd x A B)*)
with preterm_good : precontext -> preterm -> pretype -> Set :=
| ptRel_0_good {Γ} (Γ_g : precontext_good Γ)
               (x : Ast.name)
               {A} (A_g : pretype_good Γ A)
  : preterm_good (Γ ▻ (x; A)) (ptRel 0) A
| ptRel_S_good {Γ} (Γ_g : precontext_good Γ)
               {A n}
               {B} (B_g : precontext_element_good Γ B)
  : preterm_good Γ (ptRel n) A
    -> preterm_good (Γ ▻ B) (ptRel (S n)) A
| ptSort_good  {Γ} (Γ_g : precontext_good Γ) i j
  : (i < j)%sort -> preterm_good Γ (ptSort i) (ptSort j)
| ptProd_good {Γ} (Γ_g : precontext_good Γ)
              (x : Ast.name)
              i j
              {A} (A_g : preterm_good Γ A (ptSort i))
              {B} (B_g : preterm_good (Γ ▻ (x; A)) B (ptSort j))
  : preterm_good Γ (ptProd x A B) (ptSort (tProd_level i j))
| ptLambda_good {Γ} (Γ_g : precontext_good Γ)
                (x : Ast.name)
                {A}
                {B}
                {body} (b_g : preterm_good (Γ ▻ (x; A)) body B)
  : preterm_good Γ (ptLambda x A B body) (ptProd x A B)
| ptLetIn_good {Γ} (Γ_g : precontext_good Γ)
               (x : Ast.name)
               {A B}
               {a} (a_g : preterm_good Γ a A)
               {b} (b_g : preterm_good (Γ ▻ pconstr x a A) b B)
  : preterm_good Γ (ptLetIn x A a B b) (subst_n_name B a (Some 0%nat) x)
| ptApp_good {Γ} (Γ_g : precontext_good Γ)
             (name : Ast.name)
             {A B}
             {f} (f_g : preterm_good Γ f (ptProd name A B))
             {x} (x_g : preterm_good Γ x A)
  : preterm_good Γ (ptApp A B f x) (subst_n_name B x (Some 0%nat) name)
| ptConst_good_0 {Γ} (Γ_g : precontext_good Γ)
                 (name : string)
                 {T body} (body_good : preterm_good Γ body T)
  : preterm_good (Γ ▻ pconstr (Ast.nNamed name) T body) (ptConst name) T
| ptConst_good_S {Γ} (Γ_g : precontext_good Γ)
                 {B} (B_g : precontext_element_good Γ B)
                 {name} {T}
  : preterm_good Γ (ptConst name) T
    -> preterm_good (Γ ▻ B) (ptConst name) T.

Fixpoint type_of_term_good {Γ} (T : pretype) (t : preterm) (H : preterm_good Γ t T) : pretype_good Γ T.
Proof.
  refine (match H in (preterm_good Γ t T) return pretype_good Γ T with
            | ptRel_0_good _ _ _ _ A_g => A_g
            | _ => _
          end).
 {Γ} (Γ_g : precontext_good Γ)
               (x : Ast.name)
               {A} (A_g : pretype_good Γ A)
  : preterm_good (Γ ▻ (x; A)) (ptRel 0) A
| ptRel_S_good {Γ} (Γ_g : precontext_good Γ)
               {A n}
               {B} (B_g : precontext_element_good Γ B)
  : preterm_good Γ (ptRel n) A
    -> preterm_good (Γ ▻ B) (ptRel (S n)) A
| ptSort_good  {Γ} (Γ_g : precontext_good Γ) i j
  : (i < j)%sort -> preterm_good Γ (ptSort i) (ptSort j)
| ptProd_good {Γ} (Γ_g : precontext_good Γ)
              (x : Ast.name)
              i j
              {A} (A_g : preterm_good Γ A (ptSort i))
              {B} (B_g : preterm_good (Γ ▻ (x; A)) B (ptSort j))
  : preterm_good Γ (ptProd x A B) (ptSort (tProd_level i j))
| ptLambda_good {Γ} (Γ_g : precontext_good Γ)
                (x : Ast.name)
                {A}
                {B}
                {body} (b_g : preterm_good (Γ ▻ (x; A)) body B)
  : preterm_good Γ (ptLambda x A B body) (ptProd x A B)
| ptLetIn_good {Γ} (Γ_g : precontext_good Γ)
               (x : Ast.name)
               {A B}
               {a} (a_g : preterm_good Γ a A)
               {b} (b_g : preterm_good (Γ ▻ pconstr x a A) b B)
  : preterm_good Γ (ptLetIn x A a B b) (subst_n_name B a (Some 0%nat) x)
| ptApp_good {Γ} (Γ_g : precontext_good Γ)
             (name : Ast.name)
             {A B}
             {f} (f_g : preterm_good Γ f (ptProd name A B))
             {x} (x_g : preterm_good Γ x A)
  : preterm_good Γ (ptApp A B f x) (subst_n_name B x (Some 0%nat) name)
| ptConst_good_0 {Γ} (Γ_g : precontext_good Γ)
                 (name : string)
                 {T body} (body_good : preterm_good Γ body T)
  : preterm_good (Γ ▻ pconstr (Ast.nNamed name) T body) (ptConst name) T
| ptConst_good_S {Γ} (Γ_g : precontext_good Γ)
                 {B} (B_g : precontext_element_good Γ B)
                 {name} {T}
  : preterm_good Γ (ptConst name) T
    -> preterm_good (Γ ▻ B) (ptConst name) T.

Definition Context : Set := { Γ : precontext & precontext_good Γ }.
Coercion precontext_of_Context (Γ : Context) := Γ.1.

Definition Typ : Context -> Set := fun Γ => { T : pretype & pretype_good Γ T }.
Coercion pretype_of_Typ {Γ} (T : Typ Γ) := T.1.

Definition Term : forall {Γ}, Typ Γ -> Set := fun Γ T => { t : preterm & preterm_good Γ t T }.
Coercion preterm_of_Term {Γ} {T : Typ Γ} (t : Term T) := t.1.

Definition ContextElement : Context -> Set := fun Γ => { T : precontext_element & precontext_element_good Γ T }.
Coercion precontext_element_of_ContextElement {Γ} (T : ContextElement Γ)
  := T.1.

Definition empty_context : Context
  := (empty_precontext; empty_precontext_good).

Definition Context_extend : forall Γ, ContextElement Γ -> Context
  := fun Γ T => ((Γ ▻ T)%pctx; precontext_extend_good Γ.2 T.2).

Definition PConstr {Γ : Context} (name : Ast.name) (T : Typ Γ) (body : Term T)
: ContextElement Γ
  := (pconstr name T body; @pconstr_good Γ.1 Γ.2 name T.1 body.1 body.2).

| ptype (name : Ast.ident) (bodies : list (Ast.ident * pretype * preinductive_body))
| paxiom (name : Ast.ident) (T : pretype)
| pbinder (name : Ast.name) (T : pretype)


Delimit Scope context_scope with ctx.
Bind Scope context_scope with Context.
Notation ε₁ := empty_context.
Infix "▻" := Context_extend : context_scope.
(*Notation "( x ; T )" := (pbinder x T) : precontext_element_scope.*)

Require Import Template.Template.

Definition bar := (forall x : Type, x).
Quote Recursively Definition foo := bar.

Print foo.

Goal Context.
  pose foo as x.
  unfold foo in x.
  Ltac refine_Context_of_program x :=
    idtac;
    (lazymatch eval hnf in x with
    | Ast.PIn _ => refine empty_context
    | Ast.PConstr ?name ?body ?rest
      => let Γ := fresh "Γ" in
         refine (let Γ := _ in
                 @Context_extend Γ _);
     [ refine_Context_of_program rest
     | refine (_; @pconstr_good Γ.1 Γ.2 (Ast.nNamed name) _ _ _); pose (name, body) ]
    | ?x' => fail 0 "unsupported constructor of program" x'
     end).
  Ltac Context_of_program x :=
    constr:($(refine_Context_of_program x)$).

  refine_Context_of_program x.
pose (@pconstr_good Γ.1 Γ.2 _ _ _).
  Ltac refine_ContextElement_of_PConstr name type :=
    idtac;
    (lazymatch eval hnf in type with
    | Ast.PIn _ => refine empty_context
    | Ast.PConstr ?name ?type ?rest
      => let Γ := fresh "Γ" in
         refine (let Γ := _ in
                 @Context_extend Γ _);
     [ refine_Context_of_program rest
     | pose (name, type) ]
    | ?x' => fail 0 "unsupported constructor of program" x'
     end).
  Ltac Context_of_program x :=
    constr:($(refine_Context_of_program x)$).

  let k := Context_of_program x in idtac k.


| ptConstruct_good_0 {Γ} (Γ_g : precontext_good Γ)
ptype (Γ : precontext) (name : Ast.ident) (bodies : list (Ast.ident * pretype * preinductive_body))
 (T : pretype) (ind_name : string) (mut_ind_idx : nat) (ctor_idx : nat)
| ptCase (num_params : nat) (return_type : preterm) (indtype : pretype) (discriminee : preterm) (bodies : list (pretype * preterm))
| ptInd_good  (T : pretype) (ind_name : string) (mut_ind_idx : nat)
| ptFix (type : pretype) (bodies : Ast.mfixpoint preterm) (fix_idx : nat).

  (*
| ptLambda (Γ : precontext) (n : Ast.name) (A : pretype) (B : pretype) (body : preterm).*)
.


| tMeta : nat -> Ast.term
| tEvar : nat -> Ast.term
| tCast : Ast.term -> Ast.cast_kind -> Ast.term -> Ast.term
| tProd : Ast.name -> Ast.term -> Ast.term -> Ast.term
| tLambda : Ast.name -> Ast.term -> Ast.term -> Ast.term
| tLetIn : Ast.name -> Ast.term -> Ast.term -> Ast.term -> Ast.term
| tApp : Ast.term -> list Ast.term -> Ast.term
| tConst : string -> Ast.term
| tInd : Ast.inductive -> Ast.term
| tConstruct : Ast.inductive -> nat -> Ast.term
| tCase : nat -> Ast.term -> Ast.term -> list Ast.term -> Ast.term
| tFix : Ast.mfixpoint Ast.term -> nat -> Ast.term
| tUnknown : string -> Ast.term.
Inductive precontext :=
| precontext_extend


Inductive term : Type :=
    tRel : nat -> Ast.term
  | tVar : Ast.ident -> Ast.term
  | tMeta : nat -> Ast.term
  | tEvar : nat -> Ast.term
  | tSort : Ast.sort -> Ast.term
  | tCast : Ast.term -> Ast.cast_kind -> Ast.term -> Ast.term
  | tProd : Ast.name -> Ast.term -> Ast.term -> Ast.term
  | tLambda : Ast.name -> Ast.term -> Ast.term -> Ast.term
  | tLetIn : Ast.name -> Ast.term -> Ast.term -> Ast.term -> Ast.term
  | tApp : Ast.term -> list Ast.term -> Ast.term
  | tConst : string -> Ast.term
  | tInd : Ast.inductive -> Ast.term
  | tConstruct : Ast.inductive -> nat -> Ast.term
  | tCase : nat -> Ast.term -> Ast.term -> list Ast.term -> Ast.term
  | tFix : Ast.mfixpoint Ast.term -> nat -> Ast.term
  | tUnknown : string -> Ast.term

Notation AstType := Ast.term (only parsing).
Inductive ContextElement :=
| CConstr (name : Ast.name) (type : AstType) (body : Ast.term)
| CType (name : Ast.ident) (bodies : list (AstType * Ast.ident * Ast.inductive_body))
| CBinder (name : Ast.name) (type : AstType).
Definition Context := list ContextElement.
Delimit Scope context_scope with ctx.
Bind Scope context_scope with Context.
Notation ε := (@nil ContextElement : Context).
Definition context_extend (Γ : Context) (nx : ContextElement) := cons nx Γ.
Definition context_app (Γ Γ' : Context) := List.app Γ' Γ.
Notation "Γ ▻ x" := (context_extend Γ x).
Notation "Γ ▻▻ Γ'" := (context_app Γ Γ').
Local Notation "x ‘→’ y" := (Ast.tProd Ast.nAnon x y).

Definition umax (U1 U2 : Ast.sort) : Ast.sort
  := match U1, U2 with
       | Ast.sProp, _ => U2
       | _, Ast.sProp => U1
       | Ast.sSet, _ => U2
       | _, Ast.sSet => U1
       | Ast.sType U1', Ast.sType U2' => Ast.sType (Pos.max U1' U2')
     end.

Definition subst_n_name_def
           (subst_n_name : Ast.term -> option nat -> Ast.term)
           (var_n : option nat)
           (in_term : Ast.def Ast.term)
: Ast.def Ast.term
  := match in_term with
       | {| Ast.dname := dname ; Ast.dtype := dtype ; Ast.dbody := dbody ; Ast.rarg := rarg |}
         => {| Ast.dname := dname;
               Ast.dtype := subst_n_name dtype var_n;
               Ast.dbody := subst_n_name dbody (option_map S var_n);
               Ast.rarg := rarg |}
     end.

Fixpoint subst_n_name (in_term : Ast.term) (subst_term : Ast.term) (var_n : option nat) (name : Ast.name) {struct in_term} : Ast.term
  := match in_term with
       | Ast.tRel v => match var_n with
                         | Some var_n'
                           => match Compare_dec.lt_eq_lt_dec v var_n' with
                                | inleft (left _) => in_term
                                | inleft (right _) => subst_term
                                | inright _ => Ast.tRel (pred v)
                              end
                         | None => in_term
                       end
       | Ast.tVar name0 => match name with
                             | Ast.nNamed name1
                               => if String.string_dec name0 name1
                                  then subst_term
                                  else in_term
                             | Ast.nAnon => in_term
                           end
       | Ast.tMeta _ => in_term
       | Ast.tEvar _ => in_term
       | Ast.tSort _ => in_term
       | Ast.tCast term0' kind term1'
         => Ast.tCast (subst_n_name term0' subst_term var_n name)
                      kind
                      (subst_n_name term1' subst_term var_n name)
       | Ast.tProd name' term0' term1'
         => let new_name := match name, name' with
                              | Ast.nNamed n0, Ast.nNamed n1
                                => if String.string_dec n0 n1
                                   then Ast.nAnon
                                   else name
                              | _, _ => name
                            end in
            Ast.tProd name'
                      (subst_n_name term0' subst_term var_n new_name)
                      (subst_n_name term1' subst_term (option_map S var_n) new_name)
       | Ast.tLambda name' term0' term1'
         => let new_name := match name, name' with
                              | Ast.nNamed n0, Ast.nNamed n1
                                => if String.string_dec n0 n1
                                   then Ast.nAnon
                                   else name
                              | _, _ => name
                            end in
            Ast.tLambda name'
                        (subst_n_name term0' subst_term var_n new_name)
                        (subst_n_name term1' subst_term (option_map S var_n) new_name)
       | Ast.tLetIn name' term0' term1' term2'
         => let new_name := match name, name' with
                              | Ast.nNamed n0, Ast.nNamed n1
                                => if String.string_dec n0 n1
                                   then Ast.nAnon
                                   else name
                              | _, _ => name
                            end in
            Ast.tLetIn name'
                       (subst_n_name term0' subst_term var_n new_name)
                       (subst_n_name term1' subst_term var_n new_name)
                       (subst_n_name term2' subst_term (option_map S var_n) new_name)
       | Ast.tApp f args
         => Ast.tApp (subst_n_name f subst_term var_n name)
                     (List.map (fun term' => subst_n_name term' subst_term var_n name) args)
       | Ast.tConst _ => in_term
       | Ast.tInd _ => in_term
       | Ast.tConstruct _ _ => in_term
       | Ast.tCase n term0' term1' branches
         => Ast.tCase n
                      (subst_n_name term0' subst_term var_n name)
                      (subst_n_name term1' subst_term var_n name)
                      (List.map (fun term' => subst_n_name term' subst_term var_n name) branches)
       | Ast.tFix term0' n
         => Ast.tFix (List.map (subst_n_name_def (fun term' var_n => subst_n_name term' subst_term var_n name) var_n) term0')
                     n
       | Ast.tUnknown _ => in_term
     end.

(*Definition subst_one_sType1_def
           (subst_one_sType1 : Ast.term -> option Ast.term)
           (in_term : Ast.def Ast.term)
: option (Ast.def Ast.term)
  := match in_term with
       | {| Ast.dname := dname ; Ast.dtype := dtype ; Ast.dbody := dbody ; Ast.rarg := rarg |}
         => let dtype' := subst_one_sType1 dtype in
            let dbody' := subst_one_sType1 dbody in
            match dtype', dbody' with
              | Some dtype'', _ => Some {| Ast.dname := dname;
                                           Ast.dtype := dtype'';
                                           Ast.dbody := dbody;
                                           Ast.rarg := rarg |}
              | None, Some dbody'' => Some {| Ast.dname := dname;
                                              Ast.dtype := dtype;
                                              Ast.dbody := dbody'';
                                              Ast.rarg := rarg |}
              | None, None => None
            end
     end.

Definition option_fold {A} (f : A -> option A) (ls : list A)
  := match List.fold_right
             (fun x acc
              => match acc, f x with
                   | inl acc', _ => inl (x::acc')
                   | inr acc', Some x' => inl (x'::acc')
                   | inr acc', None => inr (x::acc')
                 end)
             (inr [])
             ls
     with
       | inl ls' => Some ls'
       | inr _ => None
     end.

Fixpoint subst_one_sType1 (in_term : Ast.term) (subst_term : Ast.term) {struct in_term} : option Ast.term
  := match in_term with
       | Ast.tRel _ => None
       | Ast.tVar _ => None
       | Ast.tMeta _ => None
       | Ast.tEvar _ => None
       | Ast.tSort (Ast.sType 1) => Some subst_term
       | Ast.tSort _ => None
       | Ast.tCast term0' kind term1'
         => match subst_one_sType1 term0' subst_term, subst_one_sType1 term1' subst_term with
              | Some term0'', _ => Some (Ast.tCast term0'' kind term1')
              | None, Some term1'' => Some (Ast.tCast term0' kind term1'')
              | None, None => None
            end
       | Ast.tProd name' term0' term1'
         => match subst_one_sType1 term0' subst_term, subst_one_sType1 term1' subst_term with
              | Some term0'', _ => Some (Ast.tProd name' term0'' term1')
              | None, Some term1'' => Some (Ast.tProd name' term0' term1'')
              | None, None => None
            end
       | Ast.tLambda name' term0' term1'
         => match subst_one_sType1 term0' subst_term, subst_one_sType1 term1' subst_term with
              | Some term0'', _ => Some (Ast.tLambda name' term0'' term1')
              | None, Some term1'' => Some (Ast.tLambda name' term0' term1'')
              | None, None => None
            end
       | Ast.tLetIn name' term0' term1' term2'
         => match subst_one_sType1 term0' subst_term, subst_one_sType1 term1' subst_term, subst_one_sType1 term2' subst_term with
              | Some term0'', _, _ => Some (Ast.tLetIn name' term0'' term1' term2')
              | None, Some term1'', _ => Some (Ast.tLetIn name' term0' term1'' term2')
              | None, None, Some term2'' => Some (Ast.tLetIn name' term0' term1' term2'')
              | None, None, None => None
            end
       | Ast.tApp f args
         => match subst_one_sType1 f subst_term, option_fold (fun term' => subst_one_sType1 term' subst_term) args with
              | Some f', _ => Some (Ast.tApp f' args)
              | None, Some args' => Some (Ast.tApp f args')
              | None, None => None
            end
       | Ast.tConst _ => None
       | Ast.tInd _ => in_term
       | Ast.tConstruct _ _ => in_term
       | Ast.tCase n term0' term1' branches
         => match subst_one_sType1 term0' subst_term, subst_one_sType1 term1' subst_term with
              | Some f' => Some (Ast.tApp f' args)
              | None => match List.fold_right
                                (fun term acc
                                 => match acc, subst_one_sType1 term subst_term with
                                      | inl acc', _ => inl (term::acc')
                                      | inr acc', Some term' => inl (term'::acc')
                                      | inr acc', None => inr (term::acc')
                                    end)
                                (inr [])
                                branches
                        with
                          | inl branches' => Some (Ast.tCase  f branches')
                          | inr _ => None
                        end
Ast.tCase n
                      (subst_n_name term0' subst_term var_n name)
                      (subst_n_name term1' subst_term var_n name)
                      (List.map (fun term' => subst_n_name term' subst_term var_n name) branches)
       | Ast.tFix term0' n
         => Ast.tFix (List.map (subst_n_name_def (fun term' var_n => subst_n_name term' subst_term var_n name) var_n) term0')
                     n
       | Ast.tUnknown _ => in_term
     end.*)

Fixpoint context_subst_n (in_context : Context) (subst_term : Ast.term) (var_n : option nat) (name : Ast.name) {struct in_context} : Context
  := let new_name n := match name with
                         | Ast.nNamed name'
                           => if string_dec n name'
                              then Ast.nAnon
                              else name
                         | Ast.nAnon => name
                       end in
     match in_context with
       | nil => nil
       | cons T0 Ts
         => context_extend
              (context_subst_n Ts subst_term (option_map S var_n) (match T0 with
                                                                     | CConstr (Ast.nNamed n) _ _ => new_name n
                                                                     | CType n _ => new_name n
                                                                     | CBinder (Ast.nNamed n) _ => new_name n
                                                                     | _ => name
                                                                   end))
              (match T0 with
                 | CBinder n T => CBinder n (subst_n_name T subst_term var_n name)
                 | CType _ _ => T0
                 | CConstr n T body => CConstr n (subst_n_name T subst_term var_n name) (subst_n_name body subst_term var_n name)
               end)
     end.

Definition bump_rel_from_def
           (bump_rel : Ast.term -> option nat -> Ast.term)
           (var_n : option nat)
           (in_term : Ast.def Ast.term)
: Ast.def Ast.term
  := match in_term with
       | {| Ast.dname := dname ; Ast.dtype := dtype ; Ast.dbody := dbody ; Ast.rarg := rarg |}
         => {| Ast.dname := dname;
               Ast.dtype := bump_rel dtype var_n;
               Ast.dbody := bump_rel dbody (option_map S var_n);
               Ast.rarg := rarg |}
     end.

Local Notation term_if_n n := (match n return Type with Ast.nNamed _ => Ast.term | Ast.nAnon => unit end) (only parsing).

Fixpoint bump_rel_from (in_term : Ast.term) (var_n : option nat) (name : Ast.name) (new_value : term_if_n name) {struct in_term} : Ast.term
  := match in_term with
       | Ast.tRel v => match var_n with
                         | Some var_n'
                           => match Compare_dec.lt_dec v var_n' with
                                | left _ => in_term
                                | right _ => Ast.tRel (S v)
                              end
                         | None => in_term
                       end
       | Ast.tVar name0 => match name return term_if_n name -> _ with
                             | Ast.nNamed name1
                               => fun new_value =>
                                    if String.string_dec name0 name1
                                    then new_value
                                    else in_term
                             | Ast.nAnon => fun _ => in_term
                           end new_value
       | Ast.tMeta _ => in_term
       | Ast.tEvar _ => in_term
       | Ast.tSort _ => in_term
       | Ast.tCast term0' kind term1'
         => Ast.tCast (bump_rel_from term0' var_n name new_value)
                      kind
                      (bump_rel_from term1' var_n name new_value)
       | Ast.tProd name' term0' term1'
         => let new_name := match name, name' return { n : _ & term_if_n n } with
                              | Ast.nNamed n0, Ast.nNamed n1
                                => if String.string_dec n0 n1
                                   then (Ast.nAnon; tt)
                                   else (name; new_value)
                              | _, _ => (name; new_value)
                            end in
            Ast.tProd name'
                      (bump_rel_from term0' var_n new_name.1 new_name.2)
                      (bump_rel_from term1' (option_map S var_n) new_name.1 new_name.2)
       | Ast.tLambda name' term0' term1'
         => let new_name := match name, name' return { n : _ & term_if_n n } with
                              | Ast.nNamed n0, Ast.nNamed n1
                                => if String.string_dec n0 n1
                                   then (Ast.nAnon; tt)
                                   else (name; new_value)
                              | _, _ => (name; new_value)
                            end in
            Ast.tLambda name'
                        (bump_rel_from term0' var_n new_name.1 new_name.2)
                        (bump_rel_from term1' (option_map S var_n) new_name.1 new_name.2)
       | Ast.tLetIn name' term0' term1' term2'
         => let new_name := match name, name' return { n : _ & term_if_n n } with
                              | Ast.nNamed n0, Ast.nNamed n1
                                => if String.string_dec n0 n1
                                   then (Ast.nAnon; tt)
                                   else (name; new_value)
                              | _, _ => (name; new_value)
                            end in
            Ast.tLetIn name'
                       (bump_rel_from term0' var_n new_name.1 new_name.2)
                       (bump_rel_from term1' var_n new_name.1 new_name.2)
                       (bump_rel_from term2' (option_map S var_n) new_name.1 new_name.2)
       | Ast.tApp f args
         => Ast.tApp (bump_rel_from f var_n name new_value)
                     (List.map (fun term' => bump_rel_from term' var_n name new_value) args)
       | Ast.tConst _ => in_term
       | Ast.tInd _ => in_term
       | Ast.tConstruct _ _ => in_term
       | Ast.tCase n term0' term1' branches
         => Ast.tCase n
                      (bump_rel_from term0' var_n name new_value)
                      (bump_rel_from term1' var_n name new_value)
                      (List.map (fun term' => bump_rel_from term' var_n name new_value) branches)
       | Ast.tFix term0' n
         => Ast.tFix (List.map (bump_rel_from_def (fun term' var_n => bump_rel_from term' var_n name new_value) var_n) term0')
                     n
       | Ast.tUnknown _ => in_term
     end.

Fixpoint down_from (n : nat)
  := match n with
       | O => []
       | S n' => n'::down_from n'
     end.

Definition up_to n
  := List.rev (down_from n).

(** Quoting the rules from the appendix of the HoTT book, modified for an untyped conversion algorithm *)

Inductive convertible : Context -> Ast.term -> Ast.term -> Type :=
(**
<<
--------------
Γ ⊢ a ≡ a
>> *)
| conv_refl : forall Γ a, convertible Γ a a
(**
<<
Γ ⊢ a ≡ b
--------------
Γ ⊢ b ≡ a
>> *)
| conv_sym : forall Γ a b, convertible Γ a b -> convertible Γ b a
(**
<<
Γ ⊢ a ≡ b    Γ ⊢ b ≡ c
----------------------
       Γ ⊢ a ≡ c
>> *)
| conv_trans : forall Γ a b c, convertible Γ a b -> convertible Γ b c -> convertible Γ a c
(**
<<
Γ ⊢ A ≡ A'    Γ, x : A ⊢ b ≡ b'
-------------------------------- Π-intro-eq
       Γ ⊢ λ x.b ≡ λ x.b'
>> *)
| conv_pi_intro_eq
  : forall Γ x A A' b b',
      convertible Γ A A'
      -> convertible (Γ ▻ CBinder x A) b b'
      -> convertible Γ (Ast.tLambda x A b) (Ast.tLambda x A' b')
| conv_tApp_empty1 : forall Γ f k,
                       convertible Γ f k
                       -> convertible Γ (Ast.tApp f []) k
| conv_tApp_empty2 : forall Γ f k,
                       convertible Γ (Ast.tApp f []) k
                       -> convertible Γ f k
| conv_tApp_cons1 : forall Γ f x xs k,
                       convertible Γ (Ast.tApp (Ast.tApp f [x]) xs) k
                       -> convertible Γ (Ast.tApp f (x::xs)) k
| conv_tApp_cons2 : forall Γ f x xs k,
                      convertible Γ (Ast.tApp f (x::xs)) k
                      -> convertible Γ (Ast.tApp (Ast.tApp f [x]) xs) k
(**
<<
------------------------------- Π-comp
Γ ⊢ (λ (x : A). b)(a) ≡ b[a/x]
>> *)
| conv_beta : forall Γ x A b a,
                convertible Γ (Ast.tApp (Ast.tLambda x A b) [a]) (subst_n_name b a (Some 0%nat) x)
| conv_delta : forall Γ x A body,
                 convertible (Γ ▻ CConstr (Ast.nNamed x) A body) (Ast.tConst x) body
(**
<<
Γ ⊢ f : Π_(x : A) B
---------------------------------------- Π-uniq
Γ ⊢ f ≡ (λ (x : A). f(x)) :> Π_(x : A) B
>> *)
| conv_fun_eta_rel : forall Γ x f A B,
                       has_type Γ f (Ast.tProd x A B)
                       -> convertible Γ f (Ast.tLambda x A (Ast.tApp f [Ast.tRel 0]))
| conv_fun_eta_var : forall Γ x f A B,
                       has_type Γ f (Ast.tProd (Ast.nNamed x) A B)
                       -> convertible Γ f (Ast.tLambda (Ast.nNamed x) A (Ast.tApp f [Ast.tVar x]))
| conv_tApp_respectful : forall Γ f f' x x',
                           convertible Γ f f'
                           -> convertible Γ x x'
                           -> convertible Γ (Ast.tApp f [x]) (Ast.tApp f' [x'])
| conv_tProd_respectful : forall Γ A A' B B' x,
                            convertible Γ A A'
                            -> convertible (Γ ▻ CBinder x A) B B'
                            -> convertible Γ (Ast.tProd x A B) (Ast.tProd x A' B')
| conv_tLambda_unname : forall Γ n A b,
                          convertible Γ
                                      (Ast.tLambda (Ast.nNamed n) A b)
                                      (Ast.tLambda Ast.nAnon A (subst_n_name b (Ast.tRel 0) None (Ast.nNamed n)))
| conv_tProd_unname : forall Γ n A b,
                        convertible Γ
                                    (Ast.tProd (Ast.nNamed n) A b)
                                    (Ast.tProd Ast.nAnon A (subst_n_name b (Ast.tRel 0) None (Ast.nNamed n)))
with has_type : Context -> Ast.term -> Ast.term -> Type :=
(**
<<
(x₁ : A₁, ..., xₙ : Aₙ) ctx
-------------------------------- Vble
x₁ : A₁, ..., xₙ : Aₙ ⊢ xᵢ : Aᵢ
>> *)
| has_type_tRel_0 : forall T Γ n,
                      has_type (Γ ▻ CBinder n T) (Ast.tRel 0) T
| has_type_tRel_S : forall T T' Γ n,
                      has_type Γ (Ast.tRel n) T
                      -> has_type (Γ ▻ T') (Ast.tRel (S n)) T
(**
<<
Γ ⊢ a : A     Γ ⊢ A ≡ B
-----------------------------
        Γ ⊢ a : B
>> *)
| has_type_conv_subst
: forall Γ A a B,
    has_type Γ a A -> convertible Γ A B
    -> has_type Γ a B
| has_type_conv_subst_term
: forall Γ A a b,
    has_type Γ a A -> convertible Γ a b
    -> has_type Γ b A
(**
<<
Γ ctx
------------ U-intro
Γ ⊢ Uᵢ : Uᵢ₊₁
>>
FIXME: This isn't what the numbers stand for!
 *)
| has_type_type
: forall Γ i, has_type Γ (Ast.tSort (Ast.sType i)) (Ast.tSort (Ast.sType (i+1)))
(**
<<
Γ ⊢ A : Uᵢ
------------ U-cumul
Γ ⊢ A : Uᵢ₊₁
>>
FIXME: This isn't what the numbers stand for!
 *)
| has_type_cumul
  : forall Γ A i, has_type Γ A (Ast.tSort (Ast.sType i))
                  -> has_type Γ A (Ast.tSort (Ast.sType (i+1)))
(**
<<
Γ ⊢ A : Uᵢ     Γ, x : A ⊢ B : Uᵢ
-------------------------------- Π-form
     Γ ⊢ Π_(x : A) B : Uᵢ
>> *)
| has_type_tProd
  : forall Γ A x Ui B,
      has_type Γ A (Ast.tSort Ui)
      -> has_type (Γ ▻ CBinder x A) B (Ast.tSort Ui)
      -> has_type Γ (Ast.tProd x A B) (Ast.tSort Ui)
(**
<<
Γ, x : A ⊢ b : B
------------------------------- Π-intro
Γ ⊢ λ (x : A). b : Π_(x : A) B
>> *)
| has_type_tLambda
  : forall Γ x A B b,
      has_type (Γ ▻ CBinder x A) b B
      -> has_type Γ (Ast.tLambda x A b) (Ast.tProd x A B)
(**
<<
Γ ⊢ f : Π_(x : A) B     Γ ⊢ a : A
--------------------------------- Π-elim
Γ ⊢ λ (x : A) ⇒ b : Π_(x : A) B
>> *)
| has_type_tApp
  : forall Γ f x A B a,
      has_type Γ f (Ast.tProd x A B)
      -> has_type Γ a A
      -> has_type Γ (Ast.tApp f [a]) (subst_n_name B a (Some 0%nat) x)
| has_type_tInd : forall Γ name bodies n T,
                    option_map fst (option_map fst (List.nth_error bodies n)) = Some T
                    -> has_type (Γ ▻ CType name bodies) (Ast.tInd (Ast.mkInd name n)) T
(*
Inductive a := x : a * b * c -> a
with b := y : a * b * c -> b
with c := z : a * b * c -> c.
Quote Recursively Definition d := a.
Print d.
Print List.fold_right. *)
| has_type_tConstruct : forall Γ name bodies n_ind n_ctor T,
                          option_map (fun x
                                      => option_map
                                           (fun T0
                                            => List.fold_right
                                                 (fun n_ind' T' => subst_n_name T' (Ast.tInd (Ast.mkInd name n_ind')) (Some 0%nat) Ast.nAnon)
                                                 (snd (fst T0))
                                                 (up_to (List.length bodies)))
                                           (List.nth_error (Ast.ctors (snd x)) n_ctor))
                                     (List.nth_error bodies n_ind) = Some (Some T)
                          -> has_type (Γ ▻ CType name bodies)
                                      (Ast.tConstruct (Ast.mkInd name n_ind) n_ctor)
                                      T
| has_type_tConst_constr : forall Γ n T v,
                             has_type (Γ ▻ CConstr (Ast.nNamed n) T v) (Ast.tConst n) T
| has_type_tConst_binder : forall Γ n T,
                             has_type (Γ ▻ CBinder (Ast.nNamed n) T) (Ast.tConst n) T
| has_type_tLambda_unname : forall Γ n A b B,
                              has_type Γ (Ast.tLambda Ast.nAnon A (subst_n_name b (Ast.tRel 0) None (Ast.nNamed n))) B
                              -> has_type Γ (Ast.tLambda (Ast.nNamed n) A b) B.

Definition has_type_tConstruct1 Γ name body n_ctor T
: option_map (fun T' => subst_n_name (snd (fst T')) (Ast.tInd (Ast.mkInd name 0)) (Some 0%nat) Ast.nAnon)
             (List.nth_error (Ast.ctors (snd body)) n_ctor) = Some T
  -> has_type (Γ ▻ CType name [body])
              (Ast.tConstruct (Ast.mkInd name 0) n_ctor)
              T
  := fun H => has_type_tConstruct Γ name [body] 0 n_ctor T (f_equal Some H).

Definition has_type_tInd1 Γ name body T
: fst (fst body) = T
  -> has_type (Γ ▻ CType name [body])
              (Ast.tInd (Ast.mkInd name 0))
              T
  := fun H => has_type_tInd Γ name [body] 0 T (f_equal Some H).

Fixpoint zip {A B} (ls1 : list A) (ls2 : list B)
  := match ls1, ls2 with
       | nil, _ => nil
       | x::xs, y::ys => (x, y)::zip xs ys
       | _, nil => nil
     end.
Fixpoint zip12 {A B C} (ls1 : list A) (ls2 : list (B * C))
  := match ls1, ls2 with
       | nil, _ => nil
       | x::xs, y::ys => (x, fst y, snd y)::zip12 xs ys
       | _, nil => nil
     end.

Fixpoint context_element_of_program_ind' (P : Ast.program) (ty : list Ast.term)
  := match P with
       | Ast.PType name bodies (Ast.PIn _) => Some (CType name (zip12 ty bodies))
       | Ast.PType _ _ P' => context_element_of_program_ind' P' ty
       | Ast.PIn _ => None
       | Ast.PConstr _ _ P' => context_element_of_program_ind' P' ty
       | Ast.PAxiom _ _ P' => context_element_of_program_ind' P' ty
     end.

Fixpoint context_element_of_program_axiom' (P : Ast.program)
  := match P with
       | Ast.PAxiom name type (Ast.PIn _) => Some (CBinder (Ast.nNamed name) type)
       | Ast.PType _ _ P' => context_element_of_program_axiom' P'
       | Ast.PIn _ => None
       | Ast.PConstr _ _ P' => context_element_of_program_axiom' P'
       | Ast.PAxiom _ _ P' => context_element_of_program_axiom' P'
     end.

Fixpoint context_element_of_program_constr' (P : Ast.program) (ty : Ast.term)
  := match P with
       | Ast.PConstr name body (Ast.PIn _) => Some (CConstr (Ast.nNamed name) ty body)
       | Ast.PType _ _ P' => context_element_of_program_constr' P' ty
       | Ast.PIn _ => None
       | Ast.PConstr _ _ P' => context_element_of_program_constr' P' ty
       | Ast.PAxiom _ _ P' => context_element_of_program_constr' P' ty
     end.

Definition unoption {A} (x : option A)
  := match x return match x with
                      | Some _ => A
                      | None => unit
                    end
     with
       | Some x' => x'
       | None => tt
     end.

Definition get_ind P ty :=
  Eval cbv beta iota zeta delta [unoption context_element_of_program_ind' zip12 fst snd] in
    unoption (context_element_of_program_ind' P ty).
Definition get_constr P ty :=
  Eval cbv beta iota zeta delta [unoption context_element_of_program_constr' zip12 fst snd] in
    unoption (context_element_of_program_constr' P ty).
Definition get_axiom P :=
  Eval cbv beta iota zeta delta [unoption context_element_of_program_axiom' zip12 fst snd] in
    unoption (context_element_of_program_axiom' P).

Declare Reduction eval_prog := hnf.

(* FIXME: Universes*)
Quote Recursively Definition qsigT_ind := @sigT.
Definition sigT_ctx (U1 := Ast.sType 1) (U2 := Ast.sType 1) : ContextElement := Eval eval_prog in get_ind qsigT_ind [Ast.tSort U1 ‘→’ (Ast.tRel 0 ‘→’ Ast.tSort U2) ‘→’ Ast.tSort (umax U1 U2)].
Quote Recursively Definition qlist_ind := @list.
Definition list_ctx (U := Ast.sType 1) : ContextElement := Eval eval_prog in get_ind qlist_ind [Ast.tSort U ‘→’ Ast.tSort U].
Quote Recursively Definition qnat_ind := @nat.
Definition nat_ctx : ContextElement := Eval eval_prog in get_ind qnat_ind [Ast.tSort (Ast.sType 1)].
Quote Recursively Definition qunit_ind := @unit.
Definition unit_ctx : ContextElement := Eval eval_prog in get_ind qunit_ind [Ast.tSort (Ast.sType 1)].
Quote Recursively Definition qsum_ind := @sum.
Definition sum_ctx : ContextElement := Eval eval_prog in get_ind qsum_ind [Ast.tSort (Ast.sType 1)].
Quote Recursively Definition qprod_ind := @prod.
Definition prod_ctx : ContextElement := Eval eval_prog in get_ind qprod_ind [Ast.tSort (Ast.sType 1)].
Quote Recursively Definition qpositive_ind := @positive.
Definition positive_ctx : ContextElement := Eval eval_prog in get_ind qpositive_ind [Ast.tSort (Ast.sType 1)].
Quote Recursively Definition qbool_ind := @bool.
Definition bool_ctx : ContextElement := Eval eval_prog in get_ind qbool_ind [Ast.tSort (Ast.sType 1)].
Quote Recursively Definition qascii_ind := @Ascii.ascii.
Definition ascii_ctx : ContextElement := Eval eval_prog in get_ind qascii_ind [Ast.tSort (Ast.sType 1)].
Quote Recursively Definition qstring_ind := @string.
Definition string_ctx : ContextElement := Eval eval_prog in get_ind qstring_ind [Ast.tSort (Ast.sType 1)].
Quote Recursively Definition quniverse_constr := @Ast.universe.
Definition universe_ctx : ContextElement := Eval eval_prog in get_constr quniverse_constr (Ast.tSort (Ast.sType 1)).
Quote Recursively Definition qident_constr := @Ast.ident.
Definition ident_ctx : ContextElement := Eval eval_prog in get_constr qident_constr (Ast.tSort (Ast.sType 1)).
Quote Recursively Definition qsort_ind := @Ast.sort.
Definition sort_ctx : ContextElement := Eval eval_prog in get_ind qsort_ind [Ast.tSort (Ast.sType 1)].
Quote Recursively Definition qname_ind := @Ast.name.
Definition name_ctx : ContextElement := Eval eval_prog in get_ind qname_ind [Ast.tSort (Ast.sType 1)].
Quote Recursively Definition qcast_kind_ind := @Ast.cast_kind.
Definition cast_kind_ctx : ContextElement := Eval eval_prog in get_ind qcast_kind_ind [Ast.tSort (Ast.sType 1)].
Quote Recursively Definition qinductive_ind := @Ast.inductive.
Definition inductive_ctx : ContextElement := Eval eval_prog in get_ind qinductive_ind [Ast.tSort (Ast.sType 1)].
Quote Recursively Definition qdef_ind := @Ast.def.
Definition def_ctx : ContextElement := Eval eval_prog in get_ind qdef_ind [Ast.tSort (Ast.sType 1) ‘→’ Ast.tSort (Ast.sType 1)].
Quote Recursively Definition qmfixpoint_constr := @Ast.mfixpoint.
Definition mfixpoint_ctx : ContextElement := Eval eval_prog in get_constr qmfixpoint_constr (Ast.tSort (Ast.sType 1)).
Quote Recursively Definition qterm_ind := @Ast.term.
Definition term_ctx : ContextElement := Eval eval_prog in get_ind qterm_ind [Ast.tSort (Ast.sType 1)].
Quote Recursively Definition qinductive_body_ind := @Ast.inductive_body.
Definition inductive_body_ctx : ContextElement := Eval eval_prog in get_ind qinductive_body_ind [Ast.tSort (Ast.sType 1)].
(* echo ... | grep -o '^Definition [^ ]*' | sed s'/Definition //g' | tr '\n' ';' | sed s'/;/; /g' *)
Definition DefaultContext : Context
  := [sigT_ctx; list_ctx; nat_ctx; unit_ctx; sum_ctx; prod_ctx; positive_ctx; bool_ctx; ascii_ctx; string_ctx; universe_ctx; ident_ctx; sort_ctx; name_ctx; cast_kind_ctx; inductive_ctx; def_ctx; mfixpoint_ctx; term_ctx; inductive_body_ctx].
(*

(** FIXME: umax is not the Coq-representation of things *)
| has_type_qsigT
: forall Γ U1 U2,
    has_type Γ ‘sigT’ (Ast.tSort U1 ‘→’ (Ast.tRel 0 ‘→’ Ast.tSort U2) ‘→’ Ast.tSort (umax U1 U2))
| has_type_qlist
: forall Γ U,
    has_type Γ list' (Ast.tSort U ‘→’ Ast.tSort U)
| has_type_qexistT
  : forall Γ U1 U2, has_type Γ ‘existT’ (Ast.tSort U1 ‘→’ (Ast.tRel 0 ‘→’ Ast.tSort U2) ‘→’ Ast.tRel 1 ‘→’ Ast.tApp (Ast.tRel 1) [Ast.tRel 0] ‘→’ Ast.tApp ‘sigT’ [Ast.tRel 3; Ast.tRel 2])
(*  : forall Γ A P x y,
      (*let T := Ast.tApp ‘sigT’ [A; P] in
    has_type T (Ast.tSort U)
    -> has_type A (Ast.tSort U1
    -> has_type P (A ‘→’ Ast.tSort U2)*)
      has_type Γ x A
      -> has_type Γ y (Ast.tApp P [x])
      -> has_type Γ (Ast.tApp ‘existT’ [A; P; x; y]) (Ast.tApp ‘sigT’ [A; P])*)
| has_type_qO : forall Γ, has_type Γ qO nat'
| has_type_qS : forall Γ, has_type Γ qS (nat' ‘→’ nat')
| has_type_qxI : forall Γ, has_type Γ qxI (positive' ‘→’ positive')
| has_type_qxO : forall Γ, has_type Γ qxO (positive' ‘→’ positive')
| has_type_qxH : forall Γ, has_type Γ qxH positive'
| has_type_qtrue : forall Γ, has_type Γ qtrue bool'
| has_type_qfalse : forall Γ, has_type Γ qfalse bool'
| has_type_qAscii : forall Γ, has_type Γ qAscii (bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ ascii')
| has_type_qEmptyString : forall Γ, has_type Γ qEmptyString string'
| has_type_qString : forall Γ, has_type Γ qString (ascii' ‘→’ string' ‘→’ string')
| has_type_qnil : forall Γ U, has_type Γ qnil (Ast.tSort U ‘→’ Ast.tApp list' [Ast.tRel 0])
| has_type_qcons : forall Γ U, has_type Γ qcons (Ast.tSort U ‘→’ Ast.tRel 0 ‘→’ Ast.tApp list' [Ast.tRel 1] ‘→’ Ast.tApp list' [Ast.tRel 2])
| has_type_term' : forall Γ, has_type Γ term' (Ast.tSort Ast.sSet)
| has_type_name' : forall Γ, has_type Γ name' (Ast.tSort Ast.sSet)
| has_type_prod' : forall Γ U1 U2, has_type Γ prod' (Ast.tSort U1 ‘→’ Ast.tSort U2 ‘→’ Ast.tSort (umax U1 U2))
| has_type_def' : forall Γ, has_type Γ def' (Ast.tSort Ast.sSet ‘→’ Ast.tSort Ast.sSet)
| has_type_qmkInd : forall Γ, has_type Γ qmkInd (string' ‘→’ nat' ‘→’ inductive')
(*| has_type_qstProp : has_type Γ (qtSort ‘’ qsProp) (Ast.tSort (Ast.sType 1))
| has_type_qstSet : has_type Γ (qtSort ‘’ qsSet) (Ast.tSort (Ast.sType 1))
| has_type_qstType : forall p p',
                      denote_positive p = Some p'
                      -> has_type Γ (qtSort ‘’ (Ast.tApp qsType [p]))
                                  (Ast.tSort (Ast.sType (1 + p')))*)
| has_type_qsProp : forall Γ, has_type Γ qsProp sort'
| has_type_qsSet : forall Γ, has_type Γ qsSet sort'
| has_type_qsType : forall Γ, has_type Γ qsType (positive' ‘→’ sort')
| has_type_qnAnon : forall Γ, has_type Γ qnAnon name'
| has_type_qnNamed : forall Γ, has_type Γ qnNamed (ident' ‘→’ name')
| has_type_qVmCast : forall Γ, has_type Γ qVmCast cast_kind'
| has_type_qNativeCast : forall Γ, has_type Γ qNativeCast cast_kind'
| has_type_qCast : forall Γ, has_type Γ qCast cast_kind'
| has_type_qRevertCast : forall Γ, has_type Γ qRevertCast cast_kind'
| has_type_qtRel : forall Γ, has_type Γ qtRel (nat' ‘→’ term')
| has_type_qtVar : forall Γ, has_type Γ qtVar (ident' ‘→’ term')
| has_type_qtMeta : forall Γ, has_type Γ qtMeta (nat' ‘→’ term')
| has_type_qtEvar : forall Γ, has_type Γ qtEvar (nat' ‘→’ term')
| has_type_qtSort : forall Γ, has_type Γ qtSort (sort' ‘→’ term')
| has_type_qtCast : forall Γ, has_type Γ qtCast (term' ‘→’ cast_kind' ‘→’ term' ‘→’ term')
| has_type_qtProd : forall Γ, has_type Γ qtProd (name' ‘→’ term' ‘→’ term' ‘→’ term')
| has_type_qtLambda : forall Γ, has_type Γ qtLambda (name' ‘→’ term' ‘→’ term' ‘→’ term')
| has_type_qtLetIn : forall Γ, has_type Γ qtLetIn (name' ‘→’ term' ‘→’ term' ‘→’ term' ‘→’ term')
| has_type_qtApp : forall Γ, has_type Γ qtApp (term' ‘→’ Ast.tApp list' [term'] ‘→’ term')
| has_type_qtConst : forall Γ, has_type Γ qtConst (string' ‘→’ term')
| has_type_qtInd : forall Γ, has_type Γ qtInd (inductive' ‘→’ term')
| has_type_qtConstruct : forall Γ, has_type Γ qtConstruct (inductive' ‘→’ nat' ‘→’ term')
| has_type_qtCase : forall Γ, has_type Γ qtCase (nat' ‘→’ term' ‘→’ term' ‘→’ Ast.tApp list' [term'] ‘→’ term')
| has_type_qtFix : forall Γ, has_type Γ qtFix (mfixpoint' term' ‘→’ nat' ‘→’ term')
| has_type_qtUnknown : forall Γ, has_type Γ qtUnknown (string' ‘→’ term')
| has_type_qmkdef : forall Γ T, has_type Γ qmkdef (name' ‘→’ T ‘→’ T ‘→’ nat' ‘→’ Ast.tApp def' [T])
*)

Existing Class has_type.
Existing Instances
         has_type_tApp
         has_type_tConst_constr
         has_type_tConst_binder
         has_type_tInd
         has_type_tConstruct
         has_type_tConstruct1
         (*has_type_qO has_type_qS
         has_type_qsigT
         has_type_qlist*)
         (*has_type_prod' has_type_name'*)
         (*has_type_qexistT*)
         (*has_type_qtRel has_type_qtVar has_type_qtMeta has_type_qtEvar has_type_qtSort has_type_qtCast has_type_qtProd has_type_qtLambda has_type_qtLetIn has_type_qtApp has_type_qtConst has_type_qtInd has_type_qtConstruct has_type_qtCase has_type_qtFix has_type_qtUnknown*)
         (*has_type_qtrue has_type_qfalse
         has_type_qAscii
         has_type_qEmptyString has_type_qString
         has_type_qxI has_type_qxO has_type_qxH
         has_type_qnil has_type_qcons
         has_type_qsProp has_type_qsSet has_type_qsType
         has_type_qnAnon has_type_qnNamed
         has_type_qVmCast has_type_qNativeCast has_type_qCast has_type_qRevertCast
         has_type_qmkInd has_type_qmkdef
         has_type_term' has_type_def'*)
         has_type_tRel_S has_type_tRel_0
         has_type_tLambda_unname.

Fixpoint ContextLookupCType (Γ : Context) name
  := match Γ with
       | nil => None
       | (CType name' bodies)::Γ'
         => if string_dec name' name
            then Some (CType name' bodies)
            else ContextLookupCType Γ' name
       | _::Γ' => ContextLookupCType Γ' name
     end.

Fixpoint ContextLookupCConstr (Γ : Context) name
  := match Γ with
       | nil => None
       | (CConstr (Ast.nNamed name') ty body)::Γ'
         => if string_dec name' name
            then Some (CConstr (Ast.nNamed name') ty body)
            else ContextLookupCConstr Γ' name
       | _::Γ' => ContextLookupCConstr Γ' name
     end.

Fixpoint ContextLookupCBinder (Γ : Context) name
  := match Γ with
       | nil => None
       | (CBinder (Ast.nNamed name') ty)::Γ'
         => if string_dec name' name
            then Some (0%nat, CBinder (Ast.nNamed name') ty)
            else option_map (fun k => (S (fst k), snd k)) (ContextLookupCBinder Γ' name)
       | _::Γ' => option_map (fun k => (S (fst k), snd k)) (ContextLookupCBinder Γ' name)
     end.


Global Instance has_type_tApp_split {Γ} f x x' xs T
: has_type Γ (Ast.tApp (Ast.tApp f [x]) (x'::xs)) T
  -> has_type Γ (Ast.tApp f (x::x'::xs)) T.
Proof.
  intro H'.
  eapply has_type_conv_subst_term; try eassumption; [].
  apply conv_tApp_cons2.
  apply conv_refl.
Qed.

Class Context_inf := mkContext : Context.
Definition Let_Context_inf_In (ctx : Context_inf) {T} (f : Context_inf -> T)
  := f ctx.

(**
<<
Γ ⊢ a : A     Γ, x : A, Δ ⊢ b : B
--------------------------------- Subst₁
   Γ, Δ[a/x] ⊢ b[a/x] : B[a/x]
>>

HoTT book says provable by induction.
*)
Lemma subst_1 {Γ a x A Δ B b}
: has_type Γ a A -> has_type (Γ ▻ CBinder x A ▻▻ Δ) b B
  -> has_type (Γ ▻▻ context_subst_n Δ a (Some (List.length Γ)) x)%list
              (subst_n_name b a (Some (List.length Γ)) x)
              (subst_n_name B a (Some (List.length Γ)) x).
Proof.
  intros ht1 ht2.
Admitted.

(**
<<
Γ ⊢ A : Uᵢ     Γ, Δ ⊢ b : B
--------------------------------- Wkg₁
   Γ, x : A, Δ ⊢ b : B
>>

HoTT book says provable by induction.  But we actually need to bump [Rel], eeeeew.  But not if Γ is empty.
*)
Lemma wkg_1 {Γ A Δ B b Ui}
: has_type Γ A (Ast.tSort Ui) -> has_type (Γ ▻▻ Δ) b B
  -> has_type (Γ ▻ CBinder Ast.nAnon A ▻▻ Δ)
              (@bump_rel_from b (Some (List.length Δ)) Ast.nAnon tt)
              (@bump_rel_from B (Some (List.length Δ)) Ast.nAnon tt).
Proof.
Admitted.

Lemma wkg_1_nil (Γ := ε) {Δ A B b Ui}
: has_type Γ A (Ast.tSort Ui) -> has_type (Γ ▻▻ Δ) b B
  -> has_type (Γ ▻ CBinder Ast.nAnon A ▻▻ Δ) b B.
Proof.
  subst Γ; simpl.
  unfold context_app, context_extend; simpl.
  rewrite !List.app_nil_r.
  intros H0 H1.
  revert A Ui H0.
  induction H1; try solve [ intros; econstructor; eauto ].
  all:admit.
Admitted.

(**
<<
Γ ⊢ a : A     Γ, x : A, Δ ⊢ b ≡ c :> B
-------------------------------------- Subst₂
   Γ, Δ[a/x] ⊢ b[a/x] ≡ c[a/x] :> B[a/x]
>>

HoTT book says provable by induction.
*)
Lemma subst_2 {Γ x a A Δ b c}
: has_type Γ a A -> convertible (Γ ▻ CBinder x A ▻▻ Δ) b c
  -> convertible (Γ ▻▻ context_subst_n Δ a (Some (List.length Γ)) x)%list
                 (subst_n_name b a (Some (List.length Γ)) x)
                 (subst_n_name c a (Some (List.length Γ)) x).
Proof.
  intros ht1 conv1.
Admitted.

(**
<<
Γ ⊢ A : Uᵢ     Γ, Δ ⊢ b ≡ c :> B
--------------------------------- Wkg₂
   Γ, x : A, Δ ⊢ b ≡ c :> B
>>

HoTT book says provable by induction.  But we actually need to bump [Rel], eeeewww
*)
Lemma wkg_2 {Γ A Δ b c Ui}
: has_type Γ A (Ast.tSort Ui) -> convertible (Γ ▻▻ Δ) b c
  -> convertible (Γ ▻ CBinder Ast.nAnon A ▻▻ Δ)
                 (@bump_rel_from b (Some (List.length Δ)) Ast.nAnon tt)
                 (@bump_rel_from c (Some (List.length Δ)) Ast.nAnon tt).
Proof.
Admitted.

Definition is_a_type Γ (T : Ast.term)
  := { Ui : _ & has_type Γ T (Ast.tSort Ui) }.
Lemma is_a_type_good {Γ t T} : has_type Γ t T -> is_a_type Γ T.
Proof.
Admitted.

Definition is_rel_free (term : Ast.term)
  := forall k n, subst_n_name term k n Ast.nAnon = term.

Definition is_rel_free' (term : Ast.term)
  := forall n, bump_rel_from term n Ast.nAnon tt = term.

Definition is_rel_free_def_iff
           sn br
           (is_rel_free_iff : forall term n, sn term n = term <-> br term n = term)
           (term : Ast.def Ast.term)
: (forall n, subst_n_name_def sn n term = term)
  <-> (forall n, bump_rel_from_def br n term = term).
Proof.
  unfold subst_n_name_def, bump_rel_from_def.
  pose proof (fun term n => proj1 (is_rel_free_iff term n)) as is_rel_free1.
  pose proof (fun term n => proj2 (is_rel_free_iff term n)) as is_rel_free2.
  clear is_rel_free_iff.
  split; intros H n; specialize (H n); destruct term;
  first [ rewrite !is_rel_free1
        | rewrite !is_rel_free2 ];
  try reflexivity;
  inversion H;
  repeat match goal with
           | _ => reflexivity
           | [ H : _ |- _ ] => rewrite !H
         end.
Defined.

Fixpoint is_rel_free_iff term
: is_rel_free term <-> is_rel_free' term.
Proof.
  unfold is_rel_free, is_rel_free' in *.
  destruct term; simpl;
  (split; intro H;
   [ intro n'; specialize (fun k => H k n')
   | intros k n'; specialize (H n') ]);
  repeat match goal with
           | [ |- _ <-> _ ] => split
           | _ => intro
           | _ => progress simpl in *
           | _ => reflexivity
           | [ H : False |- _ ] => solve [ destruct H ]
           | _ => progress subst
           | [ H : forall k : Ast.term, k = Ast.tRel ?x |- _ ] => exfalso; clear -H; specialize (H (Ast.tRel (S x)))
           | _ => discriminate
           | [ H : Ast.tRel _ = Ast.tRel _ |- _ ] => inversion H; clear H
           | [ H : S ?x = ?x |- _ ] => apply PeanoNat.Nat.neq_succ_diag_l in H
           | [ H : ?x = S ?x |- _ ] => symmetry in H; apply PeanoNat.Nat.neq_succ_diag_l in H
           | [ H : (_ < 0)%nat |- _ ] => apply Coq.Arith.PeanoNat.Nat.nle_succ_0 in H
           | [ H : Ast.term -> ?T |- _ ] => specialize (H (Ast.tRel 0%nat))
           | [ H : (?x < ?x)%nat |- _ ] => apply PeanoNat.Nat.lt_irrefl in H
           | [ H : Nat.pred ?x = ?x |- _ ] => is_var x; destruct x
           | [ x : option _ |- _ ] => destruct x
           | [ H : context[Compare_dec.lt_eq_lt_dec ?x ?y] |- _ ] => destruct (Compare_dec.lt_eq_lt_dec x y)
           | [ |- context[Compare_dec.lt_eq_lt_dec ?x ?y] ] => destruct (Compare_dec.lt_eq_lt_dec x y)
           | [ |- context[Compare_dec.lt_dec ?x ?y] ] => destruct (Compare_dec.lt_dec x y)
           | [ H : context[Compare_dec.lt_dec ?x ?y] |- _ ] => destruct (Compare_dec.lt_dec x y)
           | [ H : sumbool _ _ |- _ ] => destruct H
           | [ H : ~?T, H' : ?T |- _ ] => specialize (H H')
           | [ H : (?x < ?y)%nat, H' : (?y < ?x)%nat |- _ ]
             => exfalso; clear -H H'; apply (PeanoNat.Nat.lt_irrefl x); transitivity y; eassumption
         end.
Admitted.

Lemma wkg_rel_free {Γ Δ x A}
: is_rel_free x
  -> is_rel_free A
  -> has_type Γ x A
  -> has_type (Γ ▻▻ Δ) x A.
Proof.
Admitted.

Lemma wkg_conv_rel_free {Γ Δ x y}
: is_rel_free x
  -> is_rel_free y
  -> convertible Γ x y
  -> convertible (Γ ▻▻ Δ) x y.
Proof.
Admitted.

Definition has_type_tConstruct1_Lookup Γ name body n_ctor T
: option_map (fun T' => subst_n_name (snd (fst T')) (Ast.tInd (Ast.mkInd name 0)) (Some 0%nat) Ast.nAnon)
             (List.nth_error (Ast.ctors (snd body)) n_ctor)
  = Some T
  -> is_rel_free T
  -> ContextLookupCType Γ name = Some (CType name [body])
  -> has_type Γ
              (Ast.tConstruct (Ast.mkInd name 0) n_ctor)
              T.
Proof.
  intros H0 H1.
  induction Γ as [|[]]; simpl ContextLookupCType;
  [ intro; discriminate
  |
  | edestruct string_dec
  | ];
  try (intro H''; specialize (IHΓ H'');
       apply (@wkg_rel_free Γ [_]); simpl; [ | | assumption ];
       [ intros ? [?|];
         simpl;
         reflexivity
       | hnf in H1 |- *;
         (intros ??);
         rewrite !H1; reflexivity ]).
  { intro H'.
    inversion H'; subst.
    apply has_type_tConstruct1; assumption. }
Qed.


Definition has_type_tInd1_Lookup Γ name body T
: fst (fst body) = T
  -> is_rel_free T
  -> ContextLookupCType Γ name = Some (CType name [body])
  -> has_type Γ
              (Ast.tInd (Ast.mkInd name 0))
              T.
Proof.
  intros H0 H1.
  induction Γ as [|[]]; simpl ContextLookupCType;
  [ intro; discriminate
  |
  | edestruct string_dec
  | ];
  try (intro H''; specialize (IHΓ H'');
       apply (@wkg_rel_free Γ [_]); simpl; [ | | assumption ];
       [ intros ? [?|];
         simpl;
         reflexivity
       | hnf in H1 |- *;
         (intros ??);
         rewrite !H1; reflexivity ]).
  { intro H'.
    inversion H'; subst.
    apply has_type_tInd1; reflexivity. }
Qed.

Global Instance convertible_Reflexive {Γ} : Reflexive (convertible Γ) := conv_refl _.
Global Instance convertible_Symmetric {Γ} : Symmetric (convertible Γ) := conv_sym _.
Global Instance convertible_Transitive {Γ} : Transitive (convertible Γ) := conv_trans _.

Definition conv_delta_Lookup Γ name
           (body := match ContextLookupCConstr Γ name with
                      | Some (CConstr _ _ body) => body
                      | _ => Ast.tConst name
                    end)
           (H : is_rel_free body)
: convertible Γ (Ast.tConst name) match ContextLookupCConstr Γ name with
                                    | Some (CConstr _ _ body) => body
                                    | _ => Ast.tConst name
                                  end.
Proof.
  subst body.
  induction Γ as [|]; simpl in *.
  { reflexivity. }
  { hnf in H.
    edestruct (_ : ContextElement); simpl;
    auto with nocore;
    try solve [ apply (@wkg_conv_rel_free Γ [_]); hnf; simpl; [ reflexivity | intros; rewrite ?H; reflexivity | auto with nocore ] ];
    edestruct (_ : Ast.name); simpl;
    auto with nocore;
    try solve [ apply (@wkg_conv_rel_free Γ [_]); hnf; simpl; [ reflexivity | intros; rewrite ?H; reflexivity | auto with nocore ] ];
    edestruct string_dec; simpl;
    try (subst; apply conv_delta);
    try solve [ apply (@wkg_conv_rel_free Γ [_]); hnf; simpl; [ reflexivity | intros; rewrite ?H; reflexivity | auto with nocore ] ]. }
Qed.

Definition nat_eq_dec (x y : nat) : {x = y} + {x <> y}.
Proof.
  revert y; induction x.
  { intros [|?]; [ left; reflexivity | right ].
    abstract auto with arith. }
  { intros [|y]; [ right | ].
    { abstract auto with arith. }
    { destruct (IHx y); [ left | right ].
      { apply f_equal; assumption. }
      { abstract eauto with arith. } } }
Defined.

Arguments nat_eq_dec !_ !_ / .

Global Instance tApp_Proper_singleton {Γ}
: Proper ((convertible Γ)
            ==> (fun ls1 ls2
                 => match ls1, ls2 with
                      | nil, nil => True
                      | nil, _ => False
                      | _, nil => False
                      | x::xs, y::ys
                        => (convertible Γ x y * (xs = ys))%type
                    end)
            ==> convertible Γ) Ast.tApp.
Proof.
  intros x y H [|t ls] [|t' ls'] [].
  { apply conv_tApp_empty1; symmetry.
    apply conv_tApp_empty1; symmetry.
    assumption. }
  { intros H' ?; subst.
    revert x y H t t' H'; induction ls'.
    { intros; apply conv_tApp_respectful; assumption. }
    { intros x y H t t' H'.
      apply conv_tApp_cons1; symmetry.
      apply conv_tApp_cons1; symmetry.
      apply IHls'; [ | reflexivity ].
      apply conv_tApp_respectful; assumption. } }
Qed.

Global Instance tApp_Proper {Γ}
: Proper ((convertible Γ)
            ==> (fun ls1 ls2
                 => List.fold_right
                      prod
                      (if nat_eq_dec (List.length ls1) (List.length ls2)
                       then True
                       else False)
                      (List.map
                         (fun ab => convertible Γ (fst ab) (snd ab))
                         (List.combine ls1 ls2)))
            ==> convertible Γ) Ast.tApp.
Proof.
  intros x y H ls.
  revert x y H; induction ls; simpl.
  { intros x y H [|??] [].
    apply tApp_Proper_singleton; trivial. }
  { intros x y H [|y' y's] []; simpl.
    intros H0 H1.
    specialize (fun x y H => IHls x y H y's).
    edestruct nat_eq_dec; unfold eq_rec_r, eq_rec, eq_rect, eq_sym in *; simpl in *.
    { specialize (fun x y H => IHls x y H H1).
      apply conv_tApp_cons1; symmetry.
      apply conv_tApp_cons1; symmetry.
      apply IHls.
      apply tApp_Proper_singleton; trivial; split; trivial. }
    { exfalso; revert H1; clear.
      match goal with
        | [ |- List.fold_right prod False ?ls -> _ ] => generalize ls
      end.
      clear; intro ls.
      induction ls; simpl; intuition. } }
Qed.

Global Instance tApp_Proper_eq {Γ}
: Proper (convertible Γ ==> eq ==> convertible Γ) Ast.tApp.
Proof.
  repeat intro; subst; apply tApp_Proper_singleton; trivial.
  edestruct (_ : list Ast.term); repeat constructor.
Qed.

Global Instance tLambda_Proper1 {Γ n A}
: Proper (convertible (Γ ▻ CBinder n A) ==> convertible Γ) (Ast.tLambda n A).
Proof.
  intros x y H.
  eapply conv_pi_intro_eq; trivial; constructor.
Qed.

Global Instance tLambda_Proper2 {Γ n}
: Proper (convertible Γ ==> eq ==> convertible Γ) (Ast.tLambda n).
Proof.
  intros x y H ???; subst.
  eapply conv_pi_intro_eq; trivial; constructor.
Qed.

Global Instance tProd_Proper1 {Γ n A}
: Proper (convertible (Γ ▻ CBinder n A) ==> convertible Γ) (Ast.tProd n A).
Proof.
  intros x y H.
  eapply conv_tProd_respectful; trivial; constructor.
Qed.

Global Instance tProd_Proper2 {Γ n}
: Proper (convertible Γ ==> eq ==> convertible Γ) (Ast.tProd n).
Proof.
  intros x y H ???; subst.
  eapply conv_tProd_respectful; trivial; constructor.
Qed.
