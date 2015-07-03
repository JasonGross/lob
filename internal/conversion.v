(* Runs on top of https://github.com/gmalecha/template-coq *)
Require Import Template.Template.

Set Asymmetric Patterns.

Require Import Coq.Strings.String.
Require Import Coq.Program.Program.
Require Import Coq.PArith.BinPos.
Local Open Scope string_scope.
Local Open Scope positive_scope.
Local Open Scope list_scope.

Definition Context := list (Ast.name * Ast.term).
Delimit Scope context_scope with ctx.
Bind Scope context_scope with Context.
Notation ε := (@nil (Ast.name * Ast.term) : Context).
Definition context_extend (Γ : Context) (nx : Ast.name * Ast.term) := cons nx Γ.
Definition context_app (Γ Γ' : Context) := List.app Γ' Γ.
Notation "Γ ▻ x" := (context_extend Γ x) (at level 55, right associativity).
Notation "Γ ▻▻ Γ'" := (context_app Γ Γ') (at level 60, right associativity).

Definition subst_n_name_def
           (subst_n_name : Ast.term -> Ast.term)
           (in_term : Ast.def Ast.term)
: Ast.def Ast.term
  := match in_term with
       | {| Ast.dname := dname ; Ast.dtype := dtype ; Ast.dbody := dbody ; Ast.rarg := rarg |}
         => {| Ast.dname := dname;
               Ast.dtype := subst_n_name dtype;
               Ast.dbody := subst_n_name dbody;
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
         => Ast.tFix (List.map (subst_n_name_def (fun term' => subst_n_name term' subst_term var_n name)) term0')
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
      -> has_type Γ (Ast.tApp f [a]) (subst_n_name B a (Some 0%nat) x).


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

HoTT book says provable by induction.  But we actually need to bump [Rel], eeeeew
*)
(*Lemma wkg_1 {Γ x A Δ B b Ui}
: has_type Γ A (Ast.tSort Ui) -> has_type (Γ ▻▻ Δ) b B
  -> has_type (Γ ▻ (x, A) ▻▻ Δ) b B.
Proof.
Admitted.*)

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
--------------------------------- Wkg₁
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
