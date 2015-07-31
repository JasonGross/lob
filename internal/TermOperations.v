Require Template.Ast.

Set Asymmetric Patterns.
Set Universe Polymorphism.

Require Import Lob.Notations.

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
                      (subst_n_name term0' subst_term var_n name)
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
                        (subst_n_name term0' subst_term var_n name)
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
                       (subst_n_name term0' subst_term var_n name)
                       (subst_n_name term1' subst_term var_n name)
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

Definition weaken_n_name_def
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
