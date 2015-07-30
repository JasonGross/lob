Require Import Coq.Setoids.Setoid Coq.Classes.CMorphisms.
Require Export Lob.Notations Lob.WellTypedLobsTheoremStatement.

(** The proof of the theorem *)

Module Type TermPrimitives0 (Export LC : LobContext).
  Notation W := weakenTyp.

  Axiom weakenTerm : forall {Γ A B}, Term B -> Term (@weakenTyp Γ A B).

  Notation w := weakenTerm.

  Axiom weakenTyp1 : forall {Γ A B}, Typ (Γ ▻ B) -> Typ (Γ ▻ A ▻ (weakenTyp B)).
  Notation W1 := weakenTyp1.

  Axiom weakenTerm1 : forall {Γ A B C}, @Term (Γ ▻ B) C -> @Term (Γ ▻ A ▻ weakenTyp B) (@weakenTyp1 Γ A B C).
  Notation w1 := weakenTerm1.

  Axiom substTerm1 : forall {Γ A B C}
                            (c : Term C)
                            (a : Term A),
                       Term (@substTyp1 Γ A B C a).
  Notation "f ‘’₁ x" := (@substTerm1 _ _ _ _ f x) : term_scope.

  Axiom substTyp2 : forall {Γ A B C}
                           (D : Typ (Γ ▻ A ▻ B ▻ C))
                           (a : Term A),
                      Typ (Γ ▻ substTyp B a ▻ substTyp1 C a).
  Notation "f ‘’₂ x" := (@substTyp2 _ _ _ _ f x) : typ_scope.

  Axiom substTerm2 : forall {Γ A B C D}
                            (c : Term D)
                            (a : Term A),
                       Term (@substTyp2 Γ A B C D a).
  Notation "f ‘’₂ x" := (@substTerm2 _ _ _ _ _ f x) : term_scope.

  Axiom substTyp3 : forall {Γ A B C D}
                           (E : Typ (Γ ▻ A ▻ B ▻ C ▻ D))
                           (a : Term A),
                      Typ (Γ ▻ substTyp B a ▻ substTyp1 C a ▻ substTyp2 D a).
  Notation "f ‘’₃ x" := (@substTyp3 _ _ _ _ _ f x) : typ_scope.

  Axiom substTerm3 : forall {Γ A B C D E}
                            (e : Term E)
                            (a : Term A),
                       Term (@substTyp3 Γ A B C D E a).
  Notation "f ‘’₃ x" := (@substTerm3 _ _ _ _ _ _ f x) : term_scope.

(*  Axiom W1W__to__WW : forall {Γ A B C},
                        @Term (Γ ▻ A ▻ B) (W1 (W C))
                        -> @Term (Γ ▻ A ▻ B) (W (W C)).*)

  Axiom substTyp_weakenTyp
  : forall {Γ A B a},
      @Term Γ (@substTyp Γ A (@weakenTyp Γ A B) a) -> @Term Γ B.
  Notation SW := substTyp_weakenTyp.

  Axiom substTyp_weakenTyp1_weakenTyp
  : forall {Γ T A B}
           {a : Term (W B)},
      @Term (Γ ▻ T) (W1 (W A) ‘’ a)
      -> @Term (Γ ▻ T) (W A).
  Notation SW1W := substTyp_weakenTyp1_weakenTyp.

  Axiom substTyp1_substTyp_weakenTyp_inv
  : forall {Γ C T A} {a : @Term Γ C} {b : @Term Γ (T ‘’ a)},
      @Term Γ (A ‘’ a)
      -> @Term Γ (@weakenTyp _ _ A ‘’₁ a ‘’ b).

  Notation S₁₀W' := substTyp1_substTyp_weakenTyp_inv.

  Axiom substTyp1_substTyp_weakenTyp_weakenTyp
  : forall {Γ T A B}
           {a : @Term Γ A}
           {b : @Term Γ (B ‘’ a)},
      @Term Γ (W (W T) ‘’₁ a ‘’ b)
      -> @Term Γ T.

  Notation S₁₀WW := substTyp1_substTyp_weakenTyp_weakenTyp.

  (*Axiom substTyp2_substTyp1_substTyp_weakenTyp1_weakenTyp1_inv
  : forall {Γ A B C}
           {a : @Term Γ A}
           {T : Typ (Γ ▻ C)}
           {b : @Term Γ (B ‘’ a)}
           {c : @Term Γ (W C ‘’ a)},
      @Term Γ (T ‘’ SW c)
      -> @Term Γ (W1 (W1 T) ‘’₂ a ‘’₁ b ‘’ S₁₀W' c).

  Notation S₂₁₀W1W1' := substTyp2_substTyp1_substTyp_weakenTyp1_weakenTyp1_inv.*)

  Axiom substTyp2_substTyp1_substTyp_weakenTyp_weakenTyp
  : forall {Γ A B C T}
           {a : @Term Γ A}
           {b : @Term Γ (B ‘’ a)}
           {c : @Term Γ (C ‘’₁ a ‘’ b)},
      @Term Γ (W (W T) ‘’₂ a ‘’₁ b ‘’ c)
      -> @Term Γ (T ‘’ a).

  Notation S₂₁₀WW := substTyp2_substTyp1_substTyp_weakenTyp_weakenTyp.

  Axiom weakenTyp_substTyp2_substTyp1_substTyp_weakenTyp_inv
  : forall {Γ A B C T T'}
           {a : @Term Γ A}
           {b : @Term Γ (B ‘’ a)}
           {c : @Term Γ (C ‘’₁ a ‘’ b)},
      @Term (Γ ▻ T') (W (T ‘’₁ a ‘’ b))
      -> @Term (Γ ▻ T') (W (W T ‘’₂ a ‘’₁ b ‘’ c)).

  Notation WS₂₁₀W' := weakenTyp_substTyp2_substTyp1_substTyp_weakenTyp_inv.

  Axiom substTyp3_substTyp2_substTyp1_substTyp_weakenTyp
  : forall {Γ A B C D T T'}
           {a : @Term Γ A}
           {b : @Term Γ (B ‘’ a)}
           {c : @Term Γ (C ‘’₁ a ‘’ b)}
           {d : @Term (Γ ▻ T') (W (D ‘’₂ a ‘’₁ b ‘’ c))},
      @Term (Γ ▻ T') (W1 (W T ‘’₃ a ‘’₂ b ‘’₁ c) ‘’ d)
      -> @Term (Γ ▻ T') (W (T ‘’₂ a ‘’₁ b ‘’ c)).

  Notation W1S₃₂₁₀W := substTyp3_substTyp2_substTyp1_substTyp_weakenTyp.

  Axiom weakenTyp_substTyp2_substTyp1_substTyp_weakenTyp1
  : forall {Γ A B C T T'}
           {a : @Term Γ A}
           {b : Term (B ‘’ a)}
           {c : Term (C ‘’ a)},
      @Term (Γ ▻ T') (W (W1 T ‘’₂ a ‘’₁ b ‘’ S₁₀W' c))
      -> @Term (Γ ▻ T') (W (T ‘’₁ a ‘’ c)).

  Notation WS₂₁₀W1 := weakenTyp_substTyp2_substTyp1_substTyp_weakenTyp1.


  Axiom tProd : forall {Γ} A, Typ (Γ ▻ A) -> Typ Γ.
  Definition tProd_nd : forall {Γ}, Typ Γ -> Typ Γ -> Typ Γ
    := fun Γ A B => @tProd Γ A (W B).
  Notation "A ‘→’ B" := (tProd A%typ B%typ) : typ_scope.
  Notation "A ‘→'’ B" := (tProd_nd A%typ B%typ) : typ_scope.

  Axiom tLambda : forall {Γ A B}, @Term (Γ ▻ A) B -> Term (A ‘→’ B).
  Notation "‘λ.’" := tLambda : term_scope.

  Axiom substTyp_tProd : forall {Γ T A B a},
                           Term (@tProd (Γ ▻ T) A B ‘’ a)
                           -> Term (@tProd Γ (A ‘’ a) (B ‘’₁ a)).
  Notation "S∀" := substTyp_tProd.

  Axiom substTyp1_substTyp_tProd
  : forall {Γ T T' A B a b},
      Term (@tProd (Γ ▻ T ▻ T') A B ‘’₁ a ‘’ b)
      -> Term (@tProd Γ (A ‘’₁ a ‘’ b) (B ‘’₂ a ‘’₁ b)).
  Notation "S₁₀∀" := substTyp1_substTyp_tProd.

  Axiom substTyp2_substTyp1_substTyp_tProd
  : forall {Γ T T' T'' A B a b c},
      Term (@tProd (Γ ▻ T ▻ T' ▻ T'') A B ‘’₂ a ‘’₁ b ‘’ c)
      -> Term (@tProd Γ (A ‘’₂ a ‘’₁ b ‘’ c) (B ‘’₃ a ‘’₂ b ‘’₁ c)).
  Notation "S₂₁₀∀" := substTyp2_substTyp1_substTyp_tProd.

  Axiom weakenTyp_substTyp2_substTyp1_substTyp_tProd
  : forall {Γ T T' T'' T''' A B a b c},
      Term (@weakenTyp _ T''' (@tProd (Γ ▻ T ▻ T' ▻ T'') A B ‘’₂ a ‘’₁ b ‘’ c))
      -> Term (@tProd (Γ ▻ T''') (W (A ‘’₂ a ‘’₁ b ‘’ c)) (W1 (B ‘’₃ a ‘’₂ b ‘’₁ c))).
  Notation "WS₂₁₀∀" := weakenTyp_substTyp2_substTyp1_substTyp_tProd.


  Axiom tApp : forall {Γ A B}
                      (f : Term (@tProd Γ A B))
                      (x : Term A),
                 Term (B ‘’ x).
  Definition tApp_nd : forall {Γ A B},
                         Term (@tProd_nd Γ A B)
                         -> Term A
                         -> Term B
    := fun Γ A B f x => SW (@tApp Γ A (W B) f x).
  Notation "f ‘’ₐ x" := (tApp f x) : term_scope.
  Notation "f ‘'’ₐ x" := (tApp_nd f x) : term_scope.

  Axiom weakenTyp_tProd_nd : forall {Γ A B C},
                            Term (@weakenTyp Γ C (A ‘→'’ B))
                            -> Term (@weakenTyp Γ C A ‘→'’ W B).
  Definition weakenProd_nd : forall {Γ A B C},
                               Term (A ‘→'’ B)
                               -> Term (@weakenTyp Γ C A ‘→'’ W B)
    := fun Γ A B C x => weakenTyp_tProd_nd (w x).
  Notation "w→" := weakenProd_nd.

  Axiom weakenTyp_tProd : forall {Γ A B C},
                            Term (@weakenTyp Γ C (A ‘→’ B))
                            -> Term (@weakenTyp Γ C A ‘→’ W1 B).
  Definition weakenProd : forall {Γ A B C},
                            Term (A ‘→’ B)
                            -> Term (@weakenTyp Γ C A ‘→’ W1 B)
    := fun Γ A B C x => weakenTyp_tProd (w x).
  Notation "w∀" := weakenProd.

  Axiom weakenTyp_tProd_tProd_nd
  : forall {Γ A B C D},
      Term (@weakenTyp Γ D (A ‘→’ B ‘→'’ C))
      -> Term (@weakenTyp Γ D A ‘→’ W1 B ‘→'’ W1 C).
  Definition weakenProd_Prod_nd
  : forall {Γ A B C D},
      Term (A ‘→’ B ‘→'’ C)
      -> Term (@weakenTyp Γ D A ‘→’ W1 B ‘→'’ W1 C)
    := fun Γ A B C D x => weakenTyp_tProd_tProd_nd (w x).
  Notation "w∀→" := weakenProd_Prod_nd.

  Axiom weakenTyp_tProd_nd_tProd_nd
  : forall {Γ A B C D},
      Term (@weakenTyp Γ D (A ‘→'’ B ‘→'’ C))
      -> Term (@weakenTyp Γ D A ‘→'’ W B ‘→'’ W C).
  Definition weakenProd_nd_Prod_nd
  : forall {Γ A B C D},
      Term (A ‘→'’ B ‘→'’ C)
      -> Term (@weakenTyp Γ D A ‘→'’ W B ‘→'’ W C)
    := fun Γ A B C D x => weakenTyp_tProd_nd_tProd_nd (w x).
  Notation "w→→" := weakenProd_nd_Prod_nd.
End TermPrimitives0.

Module Type QuotedPrimitives0 (Export LC : LobContext) (Export TP0 : TermPrimitives0 LC).
  Axiom qtProd_nd
  : @Term (ε ▻ ‘Context’ ▻ ‘Typ’ ▻ W ‘Typ’) (W (W ‘Typ’)).
  Notation "‘tProd_nd’" := qtProd_nd.
  Notation "A ‘‘→'’’ B" := (S₂₁₀WW (‘tProd_nd’ ‘’₂ _ ‘’₁ A%typ ‘’ S₁₀W' B%typ))%term : typ_scope.
  Notation "A ‘‘→'’’ B" := (A ‘‘→'’’ B)%typ : term_scope.

  Axiom qtApp_nd
  : forall {Γ} {A : □ (‘Typ’ ‘’ Γ)} {B : □ (‘Typ’ ‘’ Γ)},
      □ (‘Term’ ‘’₁ Γ ‘’ (A ‘‘→'’’ B)
          ‘→'’ ‘Term’ ‘’₁ Γ ‘’ A
          ‘→'’ ‘Term’ ‘’₁ Γ ‘’ B).
  Notation "‘tApp_nd’" := qtApp_nd.
  Notation "f ‘‘'’’ₐ x" := (qtApp_nd ‘’₁ f ‘’ x)%term : term_scope.

  (* XXX Is this actually true? *)
  Axiom Conv0
  : forall {qH0 qX},
      @Term (ε ▻ ‘Term’ ‘’₁ ‘ε’ ‘’ qH0)
            (W (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ ‘Term’ ‘’₁ ‘ε’ ‘’ qH0 ‘→'’ qX ⌝%typ))
      -> @Term (ε ▻ ‘Term’ ‘’₁ ‘ε’ ‘’ qH0)
               (W
                  (‘Term’ ‘’₁ ‘ε’ ‘’ (⌜ ‘Term’ ‘’₁ ‘ε’ ‘’ qH0 ⌝ ‘‘→'’’ ⌜ qX ⌝))).

  Axiom qquote_term : forall {A},
                        @Term ε (‘□’ ‘’ A ‘→'’ ‘□’ ‘’ ⌜ ‘□’ ‘’ A ⌝%typ).
  Notation "‘quote_term’" := qquote_term : term_scope.

End QuotedPrimitives0.

Module Type TypeQuineC (Export LC : LobContext) (Export LH : LobHypotheses LC) (Export TP0 : TermPrimitives0 LC).
  Axiom H0 : Typ ε.
  Definition H := Term H0.
  Definition qH0 := quote_typ H0.
  Definition qH : Typ ε := (‘Term’ ‘’₁ _ ‘’ qH0)%typ.
  Notation "‘H’" := qH : typ_scope.
  Definition H0' := (‘H’ ‘→'’ ‘X’)%typ.
  Definition H' := Term H0'.
  Definition qH0' := quote_typ H0'.
  Definition qH' : Typ ε := (‘Term’ ‘’₁ _ ‘’ qH0')%typ.
  Notation "‘H'’" := qH' : typ_scope.
End TypeQuineC.

Module Type TypeQuineP (Export LC : LobContext) (Export LH : LobHypotheses LC) (Export TP0 : TermPrimitives0 LC) (Export TQC : TypeQuineC LC LH TP0).
  Axiom toH : H' -> H.
  Axiom fromH : H -> H'.
  Axiom qtoH : Term (‘H'’ ‘→'’ ‘H’).
  Axiom qfromH : Term (‘H’ ‘→'’ ‘H'’).
  Notation "‘toH’" := qtoH : term_scope.
  Notation "‘fromH’" := qfromH : term_scope.
End TypeQuineP.

Module Lob0
       (LC : LobContext)
       (LH : LobHypotheses LC)
       (Export TP0 : TermPrimitives0 LC)
       (Export QP0 : QuotedPrimitives0 LC TP0)
       (Export TQC : TypeQuineC LC LH TP0)
       (Export TQP : TypeQuineP LC LH TP0 TQC)
<: LobsTheorem LC LH.

  Definition lob : X.
  Proof.
    refine (let h : H := toH
                           (‘λ.’
                              ((w→ (‘λ.’ ‘f’))
                                 ‘'’ₐ _))%term in
            f (fromH h ‘'’ₐ ⌜ h ⌝)%term); shelve_unifiable.
    refine (let f := Conv0 (SW1W (w∀ ‘fromH’ ‘’ₐ ‘VAR₀’)) in
            let x := (w→ ‘quote_term’ ‘'’ₐ ‘VAR₀’)%term in
            w→→ ‘tApp_nd’ ‘'’ₐ f ‘'’ₐ x)%term.
  Defined.
End Lob0.

Module Type TermPrimitives (Export LC : LobContext).
  Include (TermPrimitives0 LC).

  Axiom weakenTyp2 : forall {Γ A B C}, Typ (Γ ▻ B ▻ C) -> Typ (Γ ▻ A ▻ W B ▻ W1 C).
  Notation W2 := weakenTyp2.

  Axiom weakenTerm2 : forall {Γ A B C D}, @Term (Γ ▻ B ▻ C) D -> @Term (Γ ▻ A ▻ W B ▻ W1 C) (@weakenTyp2 Γ A B C D).
  Notation w2 := weakenTerm2.

  Axiom substTyp_weakenTyp1_inv
  : forall {Γ A T' T}
           {a : @Term Γ A},
      @Term (Γ ▻ T' ‘’ a) (W (T ‘’ a))
      -> @Term (Γ ▻ T' ‘’ a) (W T ‘’₁ a).

  Notation S₁W' := substTyp_weakenTyp1_inv.

  Axiom substTyp2_substTyp_substTyp_weakenTyp1_weakenTyp_weakenTyp
  : forall {Γ A} {T : Typ (Γ ▻ A)} {T' C B}
           {a : @Term Γ A}
           {b : @Term (Γ ▻ C ‘’ a) (B ‘’₁ a)}
           {c : @Term (Γ ▻ T') (W (C ‘’ a))},
      @Term (Γ ▻ T') (W1 (W (W T) ‘’₂ a ‘’ b) ‘’ c)
      -> @Term (Γ ▻ T') (W (T ‘’ a)).

  Notation S₂₀₀W1WW := substTyp2_substTyp_substTyp_weakenTyp1_weakenTyp_weakenTyp.

  (*Axiom substTyp_substTyp_weakenTyp1_inv_arr
  : forall {Γ B A}
           {b : @Term Γ B}
           {a : @Term (Γ ▻ B) (W (A ‘’ b))}
           {T : Typ (Γ ▻ (A ‘’ b))}
           {X},
      @Term Γ (T ‘’ (SW (a ‘’ b)) ‘→'’ X)
      -> @Term Γ (W1 T ‘’ a ‘’ b ‘→'’ X).

  Notation "S₀₀W1'→" := substTyp_substTyp_weakenTyp1_inv_arr.*)

  Axiom substTyp_substTyp_weakenTyp1_inv_arr
  : forall {Γ B A}
           {b : @Term Γ B}
           {a : @Term (Γ ▻ B) (W A)}
           {T : Typ (Γ ▻ A)}
           {X},
      @Term Γ (T ‘’ (SW (a ‘’ b)) ‘→'’ X)
      -> @Term Γ (W1 T ‘’ a ‘’ b ‘→'’ X).

  Notation "S₀₀W1'→" := substTyp_substTyp_weakenTyp1_inv_arr.

  Axiom substTyp_substTyp_weakenTyp1_arr_inv
  : forall {Γ B A}
           {b : @Term Γ B}
           {a : @Term (Γ ▻ B) (W A)}
           {T : Typ (Γ ▻ A)}
           {X},
      @Term Γ (X ‘→'’ T ‘’ (SW (a ‘’ b)))
      -> @Term Γ (X ‘→'’ W1 T ‘’ a ‘’ b).

  Notation "S₀₀W1'←" := substTyp_substTyp_weakenTyp1_arr_inv.

  Axiom qfcomp_nd
  : forall {Γ A B C},
      @Term Γ (A ‘→'’ B)
      -> @Term Γ (B ‘→'’ C)
      -> @Term Γ (A ‘→'’ C).
  Notation "f ‘∘’ g" := (qfcomp_nd g f) : term_scope.

  Axiom substTyp_tProd_nd_tProd_nd
  : forall {Γ T A B C}
           {a : Term T},
      @Term Γ ((A ‘→'’ B ‘→'’ C) ‘’ a)
      -> @Term Γ ((A ‘’ a) ‘→'’ (B ‘’ a) ‘→'’ (C ‘’ a)).
  Notation "S→→" := substTyp_tProd_nd_tProd_nd.
End TermPrimitives.

Module Type QuotedPrimitives (Export LC : LobContext) (Export TP : TermPrimitives LC).
  Include (QuotedPrimitives0 LC TP).

  Axiom qsigT : forall (T : Typ ε), Typ (ε ▻ T) -> Typ ε.
  Notation "‘sigT’" := qsigT.

  Axiom context_pick_if
  : forall {P : Context -> Type}
           {Γ : Context}
           (val : P Γ)
           (dummy : P (ε ▻ ‘sigT’ ‘Context’ ‘Typ’)),
      P (ε ▻ ‘sigT’ ‘Context’ ‘Typ’).

  Axiom context_pick_if_refl
  : forall {P val dummy},
      @context_pick_if P (ε ▻ ‘sigT’ ‘Context’ ‘Typ’) val dummy = val.

  Axiom qexistT : forall {T P} (x : Term T) (p : Term (P ‘’ x)), Term (‘sigT’ T P).
  Notation "‘existT’" := qexistT.

  Definition quote_sigma (Γv : { Γ : _ & Typ Γ }) : Term (‘sigT’ ‘Context’ ‘Typ’)
    := ‘existT’ ⌜ Γv.1 ⌝%ctx ⌜ Γv.2 ⌝%typ.

  Axiom qcontext_extend : @Term (ε ▻ ‘Context’ ▻ ‘Typ’) (W (W ‘Context’)).
  Notation "Γ ‘▻’ x" := (S₁₀WW (qcontext_extend ‘’₁ Γ ‘’ x%typ)%term) : term_scope.
  Notation "Γ ‘▻’ x" := (Γ ‘▻’ x)%term : context_scope.

  Axiom qsubstTyp
  : forall {Γ} {A : □ (‘Typ’ ‘’ Γ)},
      □ (‘Typ’ ‘’ (Γ ‘▻’ A)
          ‘→'’ ‘Term’ ‘’₁ Γ ‘’ A
          ‘→'’ ‘Typ’ ‘’ Γ).
  Notation "‘substTyp’" := qsubstTyp.
  Notation "f ‘‘’’ x" := (qsubstTyp ‘'’ₐ f ‘'’ₐ x)%term : term_scope.

  Axiom qquote_sigma : @Term ε (‘sigT’ ‘Context’ ‘Typ’ ‘→'’ ‘□’ ‘’ ⌜ ‘sigT’ ‘Context’ ‘Typ’ ⌝%typ).
  Notation "‘quote_sigma’" := qquote_sigma : term_scope.

  Axiom qcast : □ (‘sigT’ ‘Context’ ‘Typ’ ‘→'’ ‘Typ’ ‘’ (‘ε’ ‘▻’ ⌜ ‘sigT’ ‘Context’ ‘Typ’ ⌝)).
  Notation "‘cast’" := qcast.

  Axiom qcast_refl_app
  : forall {T}
           (qs := quote_sigma (ε ▻ ‘sigT’ ‘Context’ ‘Typ’; T)),
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          ((⌜ T ‘’ qs ⌝)
             ‘‘→'’’
             (‘cast’ ‘'’ₐ quote_sigma (ε ▻ ‘sigT’ ‘Context’ ‘Typ’; T)
               ‘‘’’ (‘quote_sigma’ ‘'’ₐ qs)))).
  Notation "‘cast_refl’" := qcast_refl_app.

  Axiom qcast_refl_app_inv
  : forall {T}
           (qs := quote_sigma (ε ▻ ‘sigT’ ‘Context’ ‘Typ’; T)),
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          ((‘cast’ ‘'’ₐ quote_sigma (ε ▻ ‘sigT’ ‘Context’ ‘Typ’; T)
             ‘‘’’ (‘quote_sigma’ ‘'’ₐ qs))
             ‘‘→'’’ (⌜ T ‘’ qs ⌝))).
  Notation "‘cast_refl'’" := qcast_refl_app_inv.

  Axiom quote_typ_distr_tProd_nd
  : forall {H X},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ H ‘→'’ X ⌝%typ
          ‘→'’ ‘Term’ ‘’₁ ‘ε’ ‘’ (⌜ H ⌝ ‘‘→'’’ ⌜ X ⌝)%typ).

  Notation "⌜→'⌝" := quote_typ_distr_tProd_nd.

  Axiom quote_typ_undistr_tProd_nd
  : forall {H X},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’ (⌜ H ⌝ ‘‘→'’’ ⌜ X ⌝)%typ
          ‘→'’ ‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ H ‘→'’ X ⌝%typ).

  Notation "⌜←'⌝" := quote_typ_undistr_tProd_nd.

  Axiom qqfcomp_nd
  : forall {A B C},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’ (A ‘‘→'’’ C)
          ‘→'’ ‘Term’ ‘’₁ ‘ε’ ‘’ (C ‘‘→'’’ B)
          ‘→'’ ‘Term’ ‘’₁ ‘ε’ ‘’ (A ‘‘→'’’ B)).

  Notation "g ‘‘∘’’ f" := (qqfcomp_nd ‘'’ₐ f ‘'’ₐ g)%term : term_scope.

  (*Axiom substTyp2_substTyp_substTyp_SW_substTyp_weakenTyp_weakenTyp
  : forall {Γ A} {T : Typ (Γ ▻ A)} {T' C B}
           {a : @Term Γ A}
           {b : @Term (Γ ▻ C ‘’ a) (B ‘’₁ a)}
           {c : @Term (Γ ▻ T') (W (C ‘’ a))}
           {e : @Term Γ T'},
      @Term Γ (W (W T) ‘’₂ a ‘’ b ‘’ SW (c ‘’ e))
      -> @Term Γ (T ‘’ a).

  Notation S₂₀₀₀WW := substTyp2_substTyp_substTyp_SW_substTyp_weakenTyp_weakenTyp.*)

  Axiom qsubstTerm_substTerm_weakenTerm1_S₂₀₀W1WW
  : forall {T' C B}
           {b : @Term ε (B ‘’ ‘ε’)}
           {c : @Term (ε ▻ T') (W (C ‘’ ‘ε’))}
           {d : @Term (ε ▻ C ‘’ ‘ε’ ▻ W B ‘’₁ ‘ε’) (W (W ‘Typ’) ‘’₂ ‘ε’)}
           {e : @Term ε T'},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’ (SW (S₂₀₀W1WW (w1 (d ‘’ S₁W' (w b)) ‘’ c) ‘’ e))
          ‘→'’ ‘Term’ ‘’₁ ‘ε’ ‘’ (S₂₁₀WW (d ‘’₁ SW (c ‘’ e) ‘’ S₁₀W' b))).
  Notation "‘ssw1’" := qsubstTerm_substTerm_weakenTerm1_S₂₀₀W1WW.

  Axiom qsubstTerm_substTerm_weakenTerm1_S₂₀₀W1WW_inv
  : forall {T' C B}
           {b : @Term ε (B ‘’ ‘ε’)}
           {c : @Term (ε ▻ T') (W (C ‘’ ‘ε’))}
           {d : @Term (ε ▻ C ‘’ ‘ε’ ▻ W B ‘’₁ ‘ε’) (W (W ‘Typ’) ‘’₂ ‘ε’)}
           {e : @Term ε T'},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’ (S₂₁₀WW (d ‘’₁ SW (c ‘’ e) ‘’ S₁₀W' b))
          ‘→'’ ‘Term’ ‘’₁ ‘ε’ ‘’ (SW (S₂₀₀W1WW (w1 (d ‘’ S₁W' (w b)) ‘’ c) ‘’ e))).
  Notation "‘ssw1'’" := qsubstTerm_substTerm_weakenTerm1_S₂₀₀W1WW_inv.

  (*Axiom qsubstTerm_qtApp_nd_qtApp_nd_distr
  : forall {T B C}
           {a : @Term (ε ▻ T) (B ‘→'’ C ‘→'’ W (‘Typ’ ‘’ ‘ε’))}
           {b : @Term (ε ▻ T) B}
           {c : @Term (ε ▻ T) C}
           {v : @Term ε T},
      (□ (‘Term’ ‘’₁ ‘ε’
           ‘’ ((SW ((a ‘'’ₐ b ‘'’ₐ c ‘’ v)))
                 ‘‘→'’’ (SW ((S→→ (a ‘’ v) ‘'’ₐ (b ‘’ v) ‘'’ₐ (c ‘’ v)))))))%term.
  Notation "‘s→→’" := qsubstTerm_qtApp_nd_qtApp_nd_distr.*)

  (*Axiom qsubstTerm_qtApp_nd_qtApp_nd_undistr
  : forall {T B C}
           {a : @Term (ε ▻ T) (B ‘→'’ C ‘→'’ W (‘Typ’ ‘’ ‘ε’))}
           {b : @Term (ε ▻ T) B}
           {c : @Term (ε ▻ T) C}
           {v : @Term ε T},
      (□ (‘Term’ ‘’₁ ‘ε’
           ‘’ ((SW ((S→→ (a ‘’ v) ‘'’ₐ (b ‘’ v) ‘'’ₐ (c ‘’ v))))
                 ‘‘→'’’ (SW ((a ‘'’ₐ b ‘'’ₐ c ‘’ v))))))%term.*)
  Axiom qsubstTerm_qtApp_nd_qtApp_nd_distr
  : forall {T B C}
           {a : @Term ε (B ‘→'’ C ‘→'’ ‘Typ’ ‘’ ‘ε’)}
           {b : @Term ε (T ‘→'’ B)}
           {c : @Term ε (T ‘→'’ C)}
           {v : @Term ε T},
      (□ (‘Term’ ‘’₁ ‘ε’
           ‘’ ((SW ((w→→ a ‘'’ₐ (w→ b ‘'’ₐ ‘VAR₀’) ‘'’ₐ (w→ c ‘'’ₐ ‘VAR₀’) ‘’ v)))
                 ‘‘→'’’ (a ‘'’ₐ (b ‘'’ₐ v) ‘'’ₐ (c ‘'’ₐ v)))))%term.
  Notation "‘s→→’" := qsubstTerm_qtApp_nd_qtApp_nd_distr.

  Axiom qsubstTerm_qtApp_nd_qtApp_nd_undistr
  : forall {T B C}
           {a : @Term ε (B ‘→'’ C ‘→'’ ‘Typ’ ‘’ ‘ε’)}
           {b : @Term ε (T ‘→'’ B)}
           {c : @Term ε (T ‘→'’ C)}
           {v : @Term ε T},
      (□ (‘Term’ ‘’₁ ‘ε’
           ‘’ ((a ‘'’ₐ (b ‘'’ₐ v) ‘'’ₐ (c ‘'’ₐ v))
                 ‘‘→'’’ (SW ((w→→ a ‘'’ₐ (w→ b ‘'’ₐ ‘VAR₀’) ‘'’ₐ (w→ c ‘'’ₐ ‘VAR₀’) ‘’ v))))))%term.
  Notation "‘s←←’" := qsubstTerm_qtApp_nd_qtApp_nd_undistr.
End QuotedPrimitives.

Module TQC (Export LC : LobContext) (Export LH : LobHypotheses LC) (Export TP : TermPrimitives LC) (Export QP : QuotedPrimitives LC TP)
<: TypeQuineC LC LH TP.

  Definition dummy : Typ ε := qContext.

  Definition cast (Γv : { Γ : _ & Typ Γ }) : Typ (ε ▻ ‘sigT’ ‘Context’ ‘Typ’)
    := @context_pick_if Typ Γv.1 Γv.2 (W dummy).

  Definition Hf (h : { Γ : _ & Typ Γ }) : Typ ε
    := (cast h ‘’ quote_sigma h ‘→'’ ‘X’)%typ.

  Definition qh : @Term (ε ▻ ‘sigT’ ‘Context’ ‘Typ’) (W (‘Typ’ ‘’ ‘ε’))
    := (let f := w→ ‘cast’ ‘'’ₐ ‘VAR₀’ in
        let x := (w→ ‘quote_sigma’ ‘'’ₐ ‘VAR₀’)%term in
        w→→ ‘substTyp’ ‘'’ₐ f ‘'’ₐ x)%term.

  Definition h2 : Typ (ε ▻ ‘sigT’ ‘Context’ ‘Typ’)
    := (W1 (‘Term’ ‘’₁ ‘ε’)
           ‘’ S₂₀₀W1WW (w1 (‘tProd_nd’ ‘’₂ ‘ε’ ‘’ S₁W' (w ⌜ ‘X’ ⌝%typ)) ‘’ qh))%typ.

  Definition h : { Γ : _ & Typ Γ }
    := ((ε ▻ ‘sigT’ ‘Context’ ‘Typ’)%ctx; h2).

  Definition H0 : Typ ε.
  Proof.
    refine (Hf h).
  Defined.

  Definition H := Term H0.
  Definition qH0 := quote_typ H0.
  Definition qH : Typ ε := (‘Term’ ‘’₁ _ ‘’ qH0)%typ.
  Notation "‘H’" := qH : typ_scope.
  Definition H0' := (‘H’ ‘→'’ ‘X’)%typ.
  Definition H' := Term H0'.
  Definition qH0' := quote_typ H0'.
  Definition qH' : Typ ε := (‘Term’ ‘’₁ _ ‘’ qH0')%typ.
  Notation "‘H'’" := qH' : typ_scope.
End TQC.

Module Lob
       (LC : LobContext)
       (LH : LobHypotheses LC)
       (Export TP : TermPrimitives LC)
       (Export QP : QuotedPrimitives LC TP).
  Module Export TQC' := TQC LC LH TP QP.

  Module Export TQP'
  <: TypeQuineP LC LH TP TQC'.

    Local Open Scope term_scope.
    Local Open Scope typ_scope.

    Lemma toH_helper : □ (cast h ‘’ quote_sigma h ‘→'’ ‘H’).
    Proof.
      unfold qH, qH0, H0, Hf.
      unfold cast; simpl.
      rewrite context_pick_if_refl.
      simpl.
      unfold h2 at 1.
      refine (S₀₀W1'→ _).
      refine (_ ‘∘’ ‘ssw1’)%term.
      refine (⌜←'⌝ ‘∘’ _)%term.
      refine (qqfcomp_nd ‘'’ₐ _)%term.
      refine (‘s←←’ ‘‘∘’’ _)%term; shelve_unifiable.
      refine (‘cast_refl’ ‘‘∘’’ _)%term; shelve_unifiable.
      refine (⌜→'⌝ ‘'’ₐ _)%term.
      refine (⌜ _ ⌝)%term.
      exact (‘λ.’ ‘VAR₀’).
    Defined.

    Definition qtoH : Term (‘H'’ ‘→'’ ‘H’).
    Proof.
      refine (⌜←'⌝ ‘∘’ _ ‘∘’ ⌜→'⌝)%term.
      refine (qqfcomp_nd ‘'’ₐ _)%term.
      refine (⌜→'⌝ ‘'’ₐ _)%term.
      refine (⌜ _ ⌝)%term.
      apply toH_helper.
    Defined.

    Definition fromH_helper : □ (‘H’ ‘→'’ cast h ‘’ quote_sigma h).
    Proof.
      unfold qH, qH0, H0, Hf.
      unfold cast; simpl.
      rewrite context_pick_if_refl.
      simpl.
      unfold h2 at 2.
      refine (S₀₀W1'← _).
      refine (‘ssw1'’ ‘∘’ _)%term.
      refine (_ ‘∘’ ⌜→'⌝)%term.
      refine (qqfcomp_nd ‘'’ₐ _)%term.
      refine (_ ‘‘∘’’ ‘s→→’)%term; shelve_unifiable.
      refine (_ ‘‘∘’’ ‘cast_refl'’)%term; shelve_unifiable.
      refine (⌜→'⌝ ‘'’ₐ _)%term.
      refine (⌜ _ ⌝)%term.
      exact (‘λ.’ ‘VAR₀’).
    Defined.

    Definition qfromH : Term (‘H’ ‘→'’ ‘H'’).
    Proof.
      refine (⌜←'⌝ ‘∘’ _ ‘∘’ ⌜→'⌝)%term.
      refine (qqfcomp_nd ‘'’ₐ _)%term.
      refine (⌜→'⌝ ‘'’ₐ _)%term.
      refine (⌜ _ ⌝)%term.
      apply fromH_helper.
    Defined.

    Definition toH : H' -> H.
    Proof.
      refine (qfcomp_nd _).
      apply toH_helper.
    Defined.

    Definition fromH : H -> H'.
    Proof.
      refine (qfcomp_nd _).
      apply fromH_helper.
    Defined.
    Notation "‘toH’" := qtoH : term_scope.
    Notation "‘fromH’" := qfromH : term_scope.
  End TQP'.


  Module Lob' := Lob0 LC LH TP QP TQC' TQP'.
  Definition lob := Eval cbv delta [Lob'.lob] in Lob'.lob.
End Lob.
