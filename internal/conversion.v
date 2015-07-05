(* Runs on top of https://github.com/gmalecha/template-coq *)
Require Import Template.Template.

Set Asymmetric Patterns.

Require Import Coq.Strings.String.
Require Import Coq.Program.Program.
Require Import Coq.PArith.BinPos.
Local Open Scope string_scope.
Local Open Scope positive_scope.
Local Open Scope list_scope.

Require Export Lob.quote_term.
Require Import Lob.Notations.

Definition Context := list (Ast.name * Ast.term).
Delimit Scope context_scope with ctx.
Bind Scope context_scope with Context.
Notation ε := (@nil (Ast.name * Ast.term) : Context).
Definition context_extend (Γ : Context) (nx : Ast.name * Ast.term) := cons nx Γ.
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

Fixpoint context_subst_n (in_context : Context) (subst_term : Ast.term) (var_n : option nat) (name : Ast.name) {struct in_context} : Context
  := match in_context with
       | nil => nil
       | cons (n, T) Ts
         => let name' := match n, name with
                           | Ast.nNamed n', Ast.nNamed name'
                             => if string_dec n' name'
                                then Ast.nAnon
                                else name
                           | Ast.nAnon, _ => name
                           | _, Ast.nAnon => name
                         end in
            context_extend
              (context_subst_n Ts subst_term (option_map S var_n) name')
              (n, subst_n_name T subst_term var_n name)
     end.

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
  : forall Γ x A A' B B' b b',
      convertible Γ A A'
      -> convertible (Γ ▻ (x, A)) B B'
      -> convertible (Γ ▻ (x, A)) b b'
      -> convertible Γ (Ast.tLambda x A b) (Ast.tLambda x A b')
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
                            -> convertible (Γ ▻ (x, A)) B B'
                            -> convertible Γ (Ast.tProd x A B) (Ast.tProd x A' B')
with has_type : Context -> Ast.term -> Ast.term -> Type :=
(**
<<
(x₁ : A₁, ..., xₙ : Aₙ) ctx
-------------------------------- Vble
x₁ : A₁, ..., xₙ : Aₙ ⊢ xᵢ : Aᵢ
>> *)
| has_type_tRel_0 : forall T Γ n,
                      has_type (Γ ▻ (n, T)) (Ast.tRel 0) T
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
      -> has_type (Γ ▻ (x, A)) B (Ast.tSort Ui)
      -> has_type Γ (Ast.tProd x A B) (Ast.tSort Ui)
(**
<<
Γ, x : A ⊢ b : B
------------------------------- Π-intro
Γ ⊢ λ (x : A). b : Π_(x : A) B
>> *)
| has_type_tLambda
  : forall Γ x A B b,
      has_type (Γ ▻ (x, A)) b B
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
| has_type_tLambda_unname : forall Γ n A b B,
                              has_type Γ (Ast.tLambda Ast.nAnon A (subst_n_name b (Ast.tRel 0) None (Ast.nNamed n))) B
                              -> has_type Γ (Ast.tLambda (Ast.nNamed n) A b) B.

Existing Class has_type.
Existing Instances
         has_type_tApp
         has_type_qO has_type_qS
         has_type_qsigT
         has_type_qlist
         has_type_prod' has_type_name'
         has_type_qexistT
         has_type_qtRel has_type_qtVar has_type_qtMeta has_type_qtEvar has_type_qtSort has_type_qtCast has_type_qtProd has_type_qtLambda has_type_qtLetIn has_type_qtApp has_type_qtConst has_type_qtInd has_type_qtConstruct has_type_qtCase has_type_qtFix has_type_qtUnknown
         has_type_qtrue has_type_qfalse
         has_type_qAscii
         has_type_qEmptyString has_type_qString
         has_type_qxI has_type_qxO has_type_qxH
         has_type_qnil has_type_qcons
         has_type_qsProp has_type_qsSet has_type_qsType
         has_type_qnAnon has_type_qnNamed
         has_type_qVmCast has_type_qNativeCast has_type_qCast has_type_qRevertCast
         has_type_qmkInd has_type_qmkdef
         has_type_term' has_type_def'
         has_type_tRel_S has_type_tRel_0
         has_type_tLambda_unname.

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
: has_type Γ a A -> has_type (Γ ▻ (x, A) ▻▻ Δ) b B
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
(*Lemma wkg_1 {Γ x A Δ B b Ui}
: has_type Γ A (Ast.tSort Ui) -> has_type (Γ ▻▻ Δ) b B
  -> has_type (Γ ▻ (x, A) ▻▻ Δ) b B.
Proof.
Admitted.*)
Lemma wkg_1_nil (Γ := ε) {Δ x A B b Ui}
: has_type Γ A (Ast.tSort Ui) -> has_type (Γ ▻▻ Δ) b B
  -> has_type (Γ ▻ (x, A) ▻▻ Δ) b B.
Proof.
  subst Γ; simpl.
  unfold context_app, context_extend; simpl.
  rewrite !List.app_nil_r.
  intros H0 H1.
  revert A x Ui H0.
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
: has_type Γ a A -> convertible (Γ ▻ (x, A) ▻▻ Δ) b c
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
(*Lemma wkg_2 {Γ A Δ B b c Ui}
: has_type Γ A (Ast.tSort Ui) -> convertible (Γ ▻▻ Δ) b c B
  -> convertible (Γ ▻ A ▻▻ Δ) b c B.
Proof.
Admitted.*)

Definition is_a_type Γ (T : Ast.term)
  := { Ui : _ & has_type Γ T (Ast.tSort Ui) }.
Lemma is_a_type_good {Γ t T} : has_type Γ t T -> is_a_type Γ T.
Proof.
Admitted.
