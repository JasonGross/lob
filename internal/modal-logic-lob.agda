module modal-logic-lob where
data TYP : Set where
  ARR : TYP → TYP → TYP -- the type of implications, or function types
  BOX : TYP → TYP -- the modal □ operator, denoted to TERM
  LӦB-SENTENCE : TYP → TYP -- the Lӧbian sentence "If this sentence is provable, then A"
                           -- this is the modal fixpoint of λ Ψ. □ Ψ → A

data TERM : TYP → Set where
  k : {A : TYP} → TERM A → TERM (BOX A) -- from A, we deduce □ A
  distr : {A B : TYP} → TERM (ARR (BOX (ARR A B)) (ARR (BOX A) (BOX B))) -- we deduce □ (A → B) → □ A → □ B
  s4 : {A : TYP} → TERM (ARR (BOX A) (BOX (BOX A))) -- we deduce □ A →  □ □ A
  app : {A B : TYP} → TERM (ARR A B) → TERM A → TERM B -- from A → B, and A, we deduce B
  lӧb→ : {A : TYP} → TERM (ARR (LӦB-SENTENCE A) (ARR (BOX (LӦB-SENTENCE A)) A)) -- LӦB-SENTENCE A is Ψ such that Ψ → (□ Ψ → A)
  lӧb← : {A : TYP} → TERM (ARR (ARR (BOX (LӦB-SENTENCE A)) A) (LӦB-SENTENCE A)) -- LӦB-SENTENCE A is Ψ such that (□ Ψ → A) → Ψ
  compose : {A B C : TYP} → TERM (ARR A B) → TERM (ARR B C) → TERM (ARR A C) -- from A → B and B → C, we deduce A → C
  compose2 : {A B C : TYP} → TERM (ARR A B) → TERM (ARR A (ARR B C)) → TERM (ARR A C) -- from A → B and A → B → C, we deduce A → C

⟦_⟧ᵀ : TYP → Set
⟦ ARR A B ⟧ᵀ = ⟦ A ⟧ᵀ → ⟦ B ⟧ᵀ
⟦ BOX T ⟧ᵀ = TERM T
⟦ LӦB-SENTENCE A ⟧ᵀ = TERM (LӦB-SENTENCE A) → ⟦ A ⟧ᵀ

⟦_⟧ᵗ : {T : TYP} → TERM T → ⟦ T ⟧ᵀ
⟦ k e ⟧ᵗ = e
⟦ distr ⟧ᵗ box-a-b box-a = app box-a-b box-a
⟦ s4 ⟧ᵗ = k
⟦ app f x ⟧ᵗ = ⟦ f ⟧ᵗ ⟦ x ⟧ᵗ
⟦ lӧb→ ⟧ᵗ = λ x → x -- this implication is true because on denotation, the two are judgmentally equal
⟦ lӧb← ⟧ᵗ = λ x → x -- this implication is true because on denotation, the two are judgmentally equal
⟦ compose f g ⟧ᵗ = λ x → ⟦ g ⟧ᵗ (⟦ f ⟧ᵗ x)
⟦ compose2 f g ⟧ᵗ = λ x → ⟦ g ⟧ᵗ x (⟦ f ⟧ᵗ x)

module proof {A : TYP} (step1 : TERM (ARR (BOX A) A)) where
  Ψ = LӦB-SENTENCE A

  step3 : TERM (ARR Ψ (ARR (BOX Ψ) A)) -- Ψ → (□ Ψ → A)
  step3 = lӧb→

  step4 : TERM (BOX (ARR Ψ (ARR (BOX Ψ) A))) -- □ (Ψ → (□ Ψ → A))
  step4 = k step3

  step5 : TERM (ARR (BOX Ψ) (BOX (ARR (BOX Ψ) A))) -- □ Ψ → □ (□ Ψ → A)
  step5 = app distr step4

  step6 : TERM (ARR (BOX (ARR (BOX Ψ) A)) (ARR (BOX (BOX Ψ)) (BOX A))) -- □ (□ Ψ → A) → (□ □ Ψ → □ A)
  step6 = distr

  step7 : TERM (ARR (BOX Ψ) (ARR (BOX (BOX Ψ)) (BOX A))) -- □ Ψ → (□ □ Ψ → □ A)
  step7 = compose step5 step6

  step8 : TERM (ARR (BOX Ψ) (BOX (BOX Ψ))) -- □ Ψ → □ □ Ψ
  step8 = s4

  step9 : TERM (ARR (BOX Ψ) (BOX A)) -- □ Ψ → □ A
  step9 = compose2 step8 step7

  step10 : TERM (ARR (BOX Ψ) A) -- □ Ψ → A
  step10 = compose step9 step1

  step11 : TERM (ARR (ARR (BOX Ψ) A) Ψ) -- (□ Ψ → A) → Ψ
  step11 = lӧb←

  step12 : TERM Ψ -- Ψ
  step12 = app step11 step10

  step13 : TERM (BOX Ψ) -- □ Ψ
  step13 = k step12

  step14 : TERM A -- A
  step14 = app step10 step13
