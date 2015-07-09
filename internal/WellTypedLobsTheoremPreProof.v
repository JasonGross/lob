Require Import Coq.Setoids.Setoid Coq.Classes.CMorphisms.
Require Export Lob.Notations Lob.WellTypedLobsTheoremStatement.

(** The proof of the theorem *)

Axiom proof_admitted : False.
Ltac admit' := case proof_admitted.

Ltac do_shelve tac := tac; [ shelve | | ].

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

  (*Axiom substTyp2_substTyp1_substTyp_weakenTyp1_weakenTyp1_inv
  : forall {Γ A B C}
           {a : @Term Γ A}
           {T : Typ (Γ ▻ C)}
           {b : @Term Γ (B ‘’ a)}
           {c : @Term Γ (W C ‘’ a)},
      @Term Γ (T ‘’ SW c)
      -> @Term Γ (W1 (W1 T) ‘’₂ a ‘’₁ b ‘’ S₁₀W' c).

  Notation S₂₁₀W1W1' := substTyp2_substTyp1_substTyp_weakenTyp1_weakenTyp1_inv.*)

  Axiom substTyp2_substTyp1_substTyp_weakenTyp_weakenTyp_inv
  : forall {Γ B}
           {b : @Term Γ B}
           {C D}
           {A : Typ (Γ ▻ B)}
           {c : @Term Γ (C ‘’ b)}
           {d : @Term Γ (D ‘’₁ b ‘’ c)},
      @Term Γ (W (W A) ‘’₂ b ‘’₁ c ‘’ d)
      -> @Term Γ (A ‘’ b).

  Notation S₂₁₀WW' := substTyp2_substTyp1_substTyp_weakenTyp_weakenTyp_inv.

  Axiom weakenTyp_substTyp_substTyp2_substTyp1_substTyp_weakenTyp1_weakenTyp1_inv
  : forall {Γ T' B C D A}
           {a : @Term (Γ ▻ B ▻ C ▻ W D) (W (W A))}
           {T : Typ (Γ ▻ B ▻ A)}
           {b : @Term Γ B}
           {c : @Term Γ (C ‘’ b)}
           {d : @Term Γ (D ‘’ b)},
      @Term (Γ ▻ T') (W (T ‘’₁ b ‘’ (S₂₁₀WW' (a ‘’₂ b ‘’₁ c ‘’ S₁₀W' d))))
      -> @Term (Γ ▻ T') (W ((W1 (W1 T)) ‘’ a ‘’₂ b ‘’₁ c ‘’ S₁₀W' d)).

  Notation WS₀₂₁₀W1W1' := weakenTyp_substTyp_substTyp2_substTyp1_substTyp_weakenTyp1_weakenTyp1_inv.

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
  Notation "A ‘→’ B" := (tProd A B) : typ_scope.
  Notation "A ‘→'’ B" := (tProd_nd A B) : typ_scope.

  Axiom tLambda : forall {Γ A B}, @Term (Γ ▻ A) B -> Term (A ‘→’ B).
  Definition tLambda_nd : forall {Γ A B},
                            @Term Γ B -> Term (A ‘→'’ B)
    := fun Γ A B b => @tLambda Γ A (W B) (w b).
  Notation "‘λ.’" := tLambda : term_scope.
  Notation "‘λ'.’" := tLambda_nd : term_scope.

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
End TermPrimitives0.

Module Type QuotedPrimitives0 (Export LC : LobContext) (Export TP0 : TermPrimitives0 LC).
  Axiom qtProd_nd
  : @Term (ε ▻ ‘Context’ ▻ ‘Typ’ ▻ W ‘Typ’) (W (W ‘Typ’)).
  Notation "‘tProd_nd’" := qtProd_nd.

  Axiom qtApp_nd
  : □ (‘Context’ ‘→’ ‘Typ’ ‘→’ W ‘Typ’
        ‘→’ W1 (W1 ‘Term’) ‘’ ‘tProd_nd’
        ‘→'’ W ‘Term’
        ‘→'’ W1 ‘Term’).
  Notation "‘tApp_nd’" := qtApp_nd.

  (* XXX Is this actually true? *)
  Axiom Conv0
  : forall {qH0 qX},
      @Term (ε ▻ ‘Term’ ‘’₁ ‘ε’ ‘’ qH0)
            (W (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ ‘Term’ ‘’₁ ‘ε’ ‘’ qH0 ‘→'’ qX ⌝%typ))
      -> @Term (ε ▻ ‘Term’ ‘’₁ ‘ε’ ‘’ qH0)
               (W
                  (‘Term’ ‘’₁ ‘ε’
                    ‘’ S₂₁₀WW' (‘tProd_nd’ ‘’₂ ‘ε’ ‘’₁ ⌜ ‘Term’ ‘’₁ ‘ε’ ‘’ qH0 ⌝%typ ‘’ S₁₀W' ⌜ qX ⌝%typ))).

  Axiom qquote_term : forall {A : Typ ε},
                        @Term ε (A ‘→'’ ‘Term’ ‘’₁ _ ‘’ ⌜ A ⌝%typ).
  Notation "‘quote_term’" := qquote_term : term_scope.

End QuotedPrimitives0.

Module Type TypeQuine (Export LC : LobContext) (Export LH : LobHypotheses LC) (Export TP0 : TermPrimitives0 LC).
  Axiom H0 : Typ ε.
  Definition H := Term H0.
  Definition qH0 := quote_typ H0.
  Definition qH := ((substTyp1 ‘Term’ _) ‘’ qH0)%typ.
  Notation "‘H’" := qH : typ_scope.
  Definition H0' := (‘H’ ‘→'’ ‘X’)%typ.
  Definition H' := Term H0'.
  Definition qH0' := quote_typ H0'.
  Definition qH' := ((substTyp1 ‘Term’ _) ‘’ qH0')%typ.
  Notation "‘H'’" := qH' : typ_scope.
  Axiom toH : H' -> H.
  Axiom fromH : H -> H'.
  Axiom qtoH : Term (‘H'’ ‘→'’ ‘H’).
  Axiom qfromH : Term (‘H’ ‘→'’ ‘H'’).
  Notation "‘toH’" := qtoH : term_scope.
  Notation "‘fromH’" := qfromH : term_scope.
End TypeQuine.

Module Lob0
       (LC : LobContext)
       (LH : LobHypotheses LC)
       (Export TP0 : TermPrimitives0 LC)
       (Export QP0 : QuotedPrimitives0 LC TP0)
       (Export TQ : TypeQuine LC LH TP0)
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
            WS₂₁₀W1
              (W1S₃₂₁₀W
                 (WS₂₁₀∀
                      (W1S₃₂₁₀W
                         (w∀ (S₂₁₀∀ (S₁₀∀ (S∀ (‘tApp_nd’ ‘’ₐ ‘ε’) ‘’ₐ ⌜ ‘H’ ⌝%typ) ‘’ₐ S₁₀W' ⌜ ‘X’ ⌝%typ))
                             ‘’ₐ WS₀₂₁₀W1W1' f))
                      ‘’ₐ WS₂₁₀W' x))%term).
  Defined.
End Lob0.

Module Type TermPrimitives (Export LC : LobContext).
  Include (TermPrimitives0 LC).

  Axiom context_eq_dec : forall Γ Γ' : Context, {Γ = Γ'} + {Γ <> Γ'}.
  Axiom context_eq_dec_refl : forall Γ, context_eq_dec Γ Γ = left eq_refl.

  Axiom qsigT : forall (T : Typ ε), Typ (ε ▻ T) -> Typ ε.
  Notation "‘sigT’" := qsigT.
End TermPrimitives.

Module Type QuotedPrimitives (Export LC : LobContext) (Export TP : TermPrimitives LC).
  Include (QuotedPrimitives0 LC TP).

  Axiom qcontext_extend : @Term (ε ▻ ‘Context’ ▻ ‘Typ’) (W (W ‘Context’)).
  Notation "Γ ‘▻’ x" := (qcontext_extend ‘’₁ Γ ‘’ x)%typ : term_scope.
  Notation "Γ ‘▻’ x" := (Γ ‘▻’ x)%term : context_scope.

End QuotedPrimitives.

Module TQ (Export LC : LobContext) (Export LH : LobHypotheses LC) (Export TP : TermPrimitives LC) (Export QP : QuotedPrimitives LC TP)
<: TypeQuine LC LH TP.

  Definition dummy : Typ ε := qContext.

  Definition quote_sigma (Γv : { Γ : _ & Typ Γ }) : Term (‘sigT’ ‘Context’ ‘Typ’).
  Proof.
  Admitted.

  Definition cast (Γv : { Γ : _ & Typ Γ }) : Typ (ε ▻ ‘sigT’ ‘Context’ ‘Typ’).
  Proof.
    refine (if context_eq_dec Γv.1 (ε ▻ ‘sigT’ ‘Context’ ‘Typ’)
            then @eq_rect _ _ Typ Γv.2 _ _
            else W dummy);
      assumption.
  Defined.

  Definition H0 : Typ ε.
  Proof.
    refine (let h : { Γ : _ & Typ Γ }
                := ((ε ▻ ‘sigT’ ‘Context’ ‘Typ’)%ctx;
                    _ (W (‘Term’ ‘’₁ ‘ε’))%typ)
            in (cast h ‘’ quote_sigma h ‘→'’ ‘X’)%typ).
    admit'.
  Defined.

  Definition H := Term H0.
  Definition qH0 := quote_typ H0.
  Definition qH := ((substTyp1 ‘Term’ _) ‘’ qH0)%typ.
  Notation "‘H’" := qH : typ_scope.
  Definition H0' := (‘H’ ‘→'’ ‘X’)%typ.
  Definition H' := Term H0'.
  Definition qH0' := quote_typ H0'.
  Definition qH' := ((substTyp1 ‘Term’ _) ‘’ qH0')%typ.
  Notation "‘H'’" := qH' : typ_scope.

  Definition toH : H' -> H.
  Proof.
    unfold H', H, H0, H0', qH, cast; simpl.
    rewrite context_eq_dec_refl; simpl.

  Axiom fromH : H -> H'.
  Axiom qtoH : Term (‘H'’ ‘→'’ ‘H’).
  Axiom qfromH : Term (‘H’ ‘→'’ ‘H'’).
  Notation "‘toH’" := qtoH : term_scope.
  Notation "‘fromH’" := qfromH : term_scope.
End TQ.

Module Lob
       (LC : LobContext)
       (LH : LobHypotheses LC)
       (Export TP : TermPrimitives LC)
       (Export QP : QuotedPrimitives LC TP)
<: LobsTheorem LC LH.
  Module TQ' := TQ LC LH TP QP.
  Include (Lob0 LC LH TP QP TQ').
End Lob.
