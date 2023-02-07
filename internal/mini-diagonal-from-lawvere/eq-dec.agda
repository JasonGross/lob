{-# OPTIONS --without-K --allow-unsolved-metas #-}
module mini-diagonal-from-lawvere.eq-dec where
open import mini-diagonal-from-lawvere.core
open import mini-diagonal-from-lawvere.len
open import common

tag-ctx : CtxSyntax → ℕ
tag-ctx ε = 0
tag-ctx (Γ ▻ x) = 1

tag-ty : ∀ {Γ} → TySyntax Γ → ℕ
tag-ty (t ‘→’ t₁) = 0
tag-ty (x ⨾𝒰 x₁) = 1
tag-ty (t ‘×’ t₁) = 2
tag-ty 𝟙 = 3
tag-ty (‘Σ’ t t₁) = 4
tag-ty (‘Π’ t t₁) = 5
tag-ty ‘CtxSyntax’ = 6
tag-ty ‘TySyntax’ = 7
tag-ty ‘TmSyntax’ = 8

tag-tm : ∀ {Γ T} → TmSyntax {Γ} T → ℕ
tag-tm ‘id’ = 0
tag-tm (x ⨾ x₁) = 1
tag-tm apply = 2
tag-tm (curry x) = 3
tag-tm dup = 4
tag-tm (x ‘××’ x₁) = 5
tag-tm ⌜ x ⌝c = 6
tag-tm (□-map x) = 7
tag-tm (□-map𝒰 x) = 8
tag-tm □-×-codistr = 9
tag-tm □-𝟙-codistr = 10
tag-tm quot = 11
tag-tm fst = 12
tag-tm (t ‘,Σ’ t₁) = 13
tag-tm (const t) = 14
tag-tm (x ‘’ₐ t) = 15
tag-tm ‘tt’ = 16
tag-tm ⌜ x ⌝ = 17
tag-tm ⌜ t ⌝ₜ = 18
tag-tm ‘quote’ = 19
tag-tm (semidec-eq-proj₁ t x x₁) = 20
tag-tm ‘subst’ = 21

record CtxSyntax<_ (n : ℕ) : Set where
  constructor ctx<
  field ctx : CtxSyntax
  field lt : Ctx-len ctx < n
open CtxSyntax<_ using (ctx)
record TySyntax< (n : ℕ) (Γ : CtxSyntax< n) : Set where
  constructor ty<
  field ty : TySyntax (Γ .ctx)
  field lt : Ty-len ty < n
open TySyntax< using (ty)
record TmSyntax< (n : ℕ) {Γ} (T : TySyntax< n Γ) : Set where
  constructor tm<
  field tm : TmSyntax (T .ty)
  field lt : Tm-len tm < n
open TmSyntax< using (tm)

ctx<ty< : ∀ {n} → (v : Σ _ TySyntax) → Ctx-len (Σ.proj₁ v) < n → Ty-len (Σ.proj₂ v) < n → Σ _ (TySyntax< n)
ctx<ty< (Γ , T) l₁ l₂ = (ctx< Γ l₁ , ty< T l₂)

ctx<ty<tm< : ∀ {n} → (v : Σ (Σ _ TySyntax) (λ{ (Γ , T) → TmSyntax {Γ} T })) → Ctx-len (Σ.proj₁ (Σ.proj₁ v)) < n → Ty-len (Σ.proj₂ (Σ.proj₁ v)) < n → Tm-len (Σ.proj₂ v) < n → Σ (Σ _ (TySyntax< n)) (λ{ (Γ , T) → TmSyntax< n {Γ} T })
ctx<ty<tm< ((Γ , T) , t) l₁ l₂ l₃ = ((ctx< Γ l₁ , ty< T l₂) , tm< t l₃)

ctx<≡ : ∀ {n} {Γ₁ Γ₂ : CtxSyntax< n} → Γ₁ .ctx ≡ Γ₂ .ctx → Γ₁ ≡ Γ₂
ctx<≡ {n} {ctx< Γ₁ l₁} {ctx< .Γ₁ l₂} refl = ap (ctx< _) <-alleq

ty<≡ : ∀ {n Γ} {T₁ T₂ : TySyntax< n Γ} → T₁ .ty ≡ T₂ .ty → T₁ ≡ T₂
ty<≡ {n} {Γ} {ty< T₁ l₁} {ty< .T₁ l₂} refl = ap (ty< _) <-alleq

ctx<,ty<≡ : ∀ {n} {T₁ T₂ : Σ _ (TySyntax< n)} → _,_ {_} {_} {_} {TySyntax} _ (Σ.proj₂ T₁ .ty) ≡ (_ , Σ.proj₂ T₂ .ty) → T₁ ≡ T₂
ctx<,ty<≡ {n} {ctx< Γ₁ _ , ty< T₁ _} {ctx< .Γ₁ _ , ty< .T₁ _} refl = ap (λ{ (l₁ , l₂) → (ctx< Γ₁ l₁ , ty< T₁ l₂) }) (<-alleq ×≡ <-alleq)

ctx-ty : ∀ {sz} → Σ _ (TySyntax< sz) → Σ _ TySyntax
ctx-ty (Γ , T) = Γ .ctx , T .ty

tm<≡ : ∀ {n Γ T} {t₁ t₂ : TmSyntax< n {Γ} T} → t₁ .tm ≡ t₂ .tm → t₁ ≡ t₂
tm<≡ {n} {Γ} {T} {tm< t₁ l₁} {tm< .t₁ l₂} refl = ap (tm< _) <-alleq

ctx-ty-tm : ∀ {sz} → Σ (Σ _ (TySyntax< sz)) (λ{ (Γ , T) → TmSyntax< sz {Γ} T }) → Σ (Σ _ TySyntax) (λ{ (Γ , T) → TmSyntax {Γ} T })
ctx-ty-tm (ΓT , t) = ctx-ty ΓT , t .tm

ctx<,ty<,tm<≡ : ∀ {n} {T₁ T₂ : Σ (Σ _ (TySyntax< n)) (λ{ (Γ , T) → TmSyntax< n {Γ} T })} → _,_ {_} {_} {Σ _ TySyntax} {λ{ (Γ , T) → TmSyntax {Γ} T }} _ (Σ.proj₂ T₁ .tm) ≡ (_ , Σ.proj₂ T₂ .tm) → T₁ ≡ T₂
ctx<,ty<,tm<≡ {n} {(ctx< Γ₁ _ , ty< T₁ _) , tm< t₁ _} {(ctx< .Γ₁ _ , ty< .T₁ _) , tm< .t₁ _} refl = ap (λ{ (l₁ , l₂ , l₃) → ((ctx< Γ₁ l₁ , ty< T₁ l₂) , tm< t₁ l₃) }) (<-alleq ×≡ <-alleq ×≡ <-alleq)

↑≤ctx : ∀ {n m} → n ≤ m → CtxSyntax< n → CtxSyntax< m
↑≤ctx pf (ctx< Γ p) = ctx< Γ (p ■<≤ pf)

↑≤ty : ∀ {n m} → (p : n ≤ m) → ∀ {Γ} → TySyntax< n Γ → TySyntax< m (↑≤ctx p Γ)
↑≤ty pf (ty< T p) = ty< T (p ■<≤ pf)

↑≤tm : ∀ {n m} → (p : n ≤ m) → ∀ {Γ T q r} → TmSyntax< n {Γ} T → TmSyntax< m {ctx< (Γ .ctx) q} (ty< (T .ty) r)
↑≤tm pf (tm< T p) = tm< T (p ■<≤ pf)

↑≤tm-strict : ∀ {n m} → (p : n ≤ m) → ∀ {Γ T} → TmSyntax< n {Γ} T → TmSyntax< m {↑≤ctx p Γ} (↑≤ty p T)
↑≤tm-strict p t = ↑≤tm p t

↑ctx : ∀ {n m} → n < m → CtxSyntax< n → CtxSyntax< m
↑ctx pf (ctx< Γ p) = ctx< Γ (p ■< pf)

↑ty : ∀ {n m} → (p : n < m) → ∀ {Γ} → TySyntax< n Γ → TySyntax< m (↑ctx p Γ)
↑ty pf (ty< T p) = ty< T (p ■< pf)

↑tm : ∀ {n m} → (p : n < m) → ∀ {Γ T} → TmSyntax< n {Γ} T → TmSyntax< m {↑ctx p Γ} (↑ty p T)
↑tm pf (tm< T p) = tm< T (p ■< pf)

_▻<_ : ∀ {sz} → (Γ : CtxSyntax< sz) → (T : TySyntax< sz Γ) → CtxSyntax< (suc sz)
Γ ▻< T = ctx< (Γ .ctx ▻ T .ty) (<-suc→ (TySyntax<.lt T))

-- sz on args is the exclusive upper bound on arg size
args-of-tag-ctx : ℕ → ℕ → Set
args-of-tag-ctx _ 0 = ⊤
args-of-tag-ctx sz 1 = Σ (CtxSyntax< sz) (TySyntax< sz)
args-of-tag-ctx _ _ = ⊥

↑≤args-of-tag-ctx : ∀ {n m} → (p : n ≤ m) → ∀ {t} → args-of-tag-ctx n t → args-of-tag-ctx m t
↑≤args-of-tag-ctx {_} _ {0} tt = tt
↑≤args-of-tag-ctx {suc _} p {1} (Γ , T) = ↑≤ctx p Γ , ↑≤ty p T

ap-inv-↑≤args-of-tag-ctx : ∀ {n m} → (p₁ p₂ : n ≤ m) → ∀ {t} (v₁ v₂ : args-of-tag-ctx n t) → ↑≤args-of-tag-ctx p₁ {t} v₁ ≡ ↑≤args-of-tag-ctx p₂ {t} v₂ → v₁ ≡ v₂
ap-inv-↑≤args-of-tag-ctx {n} {m} p₁ p₂ {0} tt tt pf = refl
ap-inv-↑≤args-of-tag-ctx {suc _} {m} p₁ p₂ {1} (Γ₁ , T₁) (Γ₂ , T₂) pf = ctx<,ty<≡ (ap ctx-ty pf)

reconstruct-ctx : ∀ {n} → Σ _ (args-of-tag-ctx n) → CtxSyntax< (suc n)
reconstruct-ctx {_} (0 , a) = ctx< ε (rigidify< refl)
reconstruct-ctx {suc _} (1 , ((ctx< Γ _) , (ty< T p))) = (ctx< (Γ ▻ T) (<-suc→ p))

deconstruct-ctx : ∀ Γ → args-of-tag-ctx (Ctx-len Γ) (tag-ctx Γ)
deconstruct-ctx ε = tt
deconstruct-ctx (Γ ▻ T) = (ctx< Γ (Ty-len< T ■< <-suc)) , (ty< T <-suc)

reconstruct-ctx-eq : ∀ Γ → reconstruct-ctx (tag-ctx Γ , deconstruct-ctx Γ) ≡ (ctx< Γ <-suc)
reconstruct-ctx-eq ε = refl
reconstruct-ctx-eq (Γ ▻ x) = refl

args-of-tag-ty : ℕ → ℕ → Set
args-of-tag-ty sz 0 = Σ _ λ{ Γ → TySyntax< sz Γ × TySyntax< sz Γ }
args-of-tag-ty sz 1 with sz
... | suc (suc sz) = Σ _ λ{ Γ → Σ (TySyntax< sz Γ × TySyntax< sz Γ) λ{ ((ty< a a<) , (ty< b b<)) → TmSyntax< (suc sz) {↑ctx <-suc Γ} (ty< (a ‘→’ b) (<-suc→ (max-<-spec-build a< b<))) × TySyntax< (suc sz) (ctx< (_ ▻ b) (<-suc→ b<)) } }
... | _ = ⊥
args-of-tag-ty sz 2 = Σ _ λ{ Γ → TySyntax< sz Γ × TySyntax< sz Γ }
args-of-tag-ty sz 3 = CtxSyntax< sz
args-of-tag-ty sz 4 with sz
... | zero = ⊥
... | suc sz = Σ _ λ{ Γ → Σ (TySyntax< sz Γ) λ{ A → TySyntax< (suc sz) (Γ ▻< A) } }
args-of-tag-ty sz 5 with sz
... | zero = ⊥
... | suc sz = Σ _ λ{ Γ → Σ (TySyntax< sz Γ) λ{ A → TySyntax< (suc sz) (Γ ▻< A) } }
args-of-tag-ty sz 6 = CtxSyntax< sz
args-of-tag-ty sz 7 with sz
... | suc (suc sz) = CtxSyntax< sz
... | _ = ⊥
args-of-tag-ty sz 8 with sz
... | suc (suc (suc (suc (suc sz)))) = CtxSyntax< sz
... | _ = ⊥
args-of-tag-ty sz _ = ⊥

↑≤args-of-tag-ty : ∀ {n m} → (p : n ≤ m) → ∀ {t} → args-of-tag-ty n t → args-of-tag-ty m t
↑≤args-of-tag-ty p {0} (Γ , (a , b)) = ↑≤ctx p Γ , (↑≤ty p a , ↑≤ty p b)
↑≤args-of-tag-ty p {2} (Γ , (a , b)) = ↑≤ctx p Γ , (↑≤ty p a , ↑≤ty p b)
↑≤args-of-tag-ty p {3} Γ = ↑≤ctx p Γ
↑≤args-of-tag-ty p {6} Γ = ↑≤ctx p Γ
↑≤args-of-tag-ty {suc n} {suc m} p {4} (Γ , (a , b)) = ↑≤ctx (<-suc← p) Γ , (↑≤ty (<-suc← p) a , ↑≤ty p b)
↑≤args-of-tag-ty {suc n} {suc m} p {5} (Γ , (a , b)) = ↑≤ctx (<-suc← p) Γ , (↑≤ty (<-suc← p) a , ↑≤ty p b)
↑≤args-of-tag-ty {suc (suc n)} {suc (suc m)} p {1} (Γ , ((a , b) , (s , T)))
  = let p = <-suc← p in let p' = <-suc← p in ↑≤ctx p' Γ , ((↑≤ty p' a , ↑≤ty p' b) , (↑≤tm p s , ↑≤ty p T))
↑≤args-of-tag-ty {suc (suc n)} {suc (suc m)} p {7} Γ = ↑≤ctx (<-suc← (<-suc← p)) Γ
↑≤args-of-tag-ty {suc (suc (suc (suc (suc n))))} {suc (suc (suc (suc (suc m))))} p {8} Γ = ↑≤ctx (<-suc← (<-suc← (<-suc← (<-suc← (<-suc← p))))) Γ

ap-inv-↑≤args-of-tag-ty : ∀ {n m} → (p₁ p₂ : n ≤ m) → ∀ {t} (v₁ v₂ : args-of-tag-ty n t) → ↑≤args-of-tag-ty p₁ {t} v₁ ≡ ↑≤args-of-tag-ty p₂ {t} v₂ → v₁ ≡ v₂
ap-inv-↑≤args-of-tag-ty {n} {m} p₁ p₂ {0} (ctx< Γ _ , (ty< a _ , ty< b _)) (ctx< Γ' _ , (ty< a' _ , ty< b' _)) pf with (ap (λ{ (Γ , (a , b)) → (Γ .ctx , (a .ty , b .ty)) }) pf)
... | refl = ap (λ{ (l₁ , l₂ , l₃) → (ctx< Γ l₁ , (ty< a l₂ , ty< b l₃)) }) (<-alleq ×≡ <-alleq ×≡ <-alleq)
ap-inv-↑≤args-of-tag-ty {n} {m} p₁ p₂ {2} (ctx< Γ _ , (ty< a _ , ty< b _)) (ctx< Γ' _ , (ty< a' _ , ty< b' _)) pf with (ap (λ{ (Γ , (a , b)) → (Γ .ctx , (a .ty , b .ty)) }) pf)
... | refl = ap (λ{ (l₁ , l₂ , l₃) → (ctx< Γ l₁ , (ty< a l₂ , ty< b l₃)) }) (<-alleq ×≡ <-alleq ×≡ <-alleq)
ap-inv-↑≤args-of-tag-ty {n} {m} p₁ p₂ {3} (ctx< Γ _) (ctx< Γ' _) pf = ctx<≡ (ap ctx pf)
ap-inv-↑≤args-of-tag-ty {n} {m} p₁ p₂ {6} (ctx< Γ _) (ctx< Γ' _) pf = ctx<≡ (ap ctx pf)
ap-inv-↑≤args-of-tag-ty {suc n} {suc m} p₁ p₂ {4} (ctx< Γ l₁ , (ty< a l₂ , ty< b l₃)) (ctx< Γ' l₁' , (ty< a' l₂' , ty< b' l₃')) pf = helper {l₁} {l₂} {l₃} {l₁'} {l₂'} {l₃'} (ap (λ{ (Γ , (a , b)) → (Γ .ctx , (a .ty , b .ty)) }) pf)
  where
    helper : ∀ {l₁ l₂ l₃ l₁' l₂' l₃'} → (Γ , (a , b)) ≡ (Γ' , (a' , b')) → (ctx< Γ l₁ , (ty< a l₂ , ty< b l₃)) ≡ (ctx< Γ' l₁' , (ty< a' l₂' , ty< b' l₃'))
    helper refl = ap (λ{ (l₁ , l₂ , l₃) → (ctx< Γ l₁ , (ty< a l₂ , ty< b l₃)) }) (<-alleq ×≡ <-alleq ×≡ <-alleq)
ap-inv-↑≤args-of-tag-ty {suc n} {suc m} p₁ p₂ {5} (ctx< Γ l₁ , (ty< a l₂ , ty< b l₃)) (ctx< Γ' l₁' , (ty< a' l₂' , ty< b' l₃')) pf = helper {l₁} {l₂} {l₃} {l₁'} {l₂'} {l₃'} (ap (λ{ (Γ , (a , b)) → (Γ .ctx , (a .ty , b .ty)) }) pf)
  where
    helper : ∀ {l₁ l₂ l₃ l₁' l₂' l₃'} → (Γ , (a , b)) ≡ (Γ' , (a' , b')) → (ctx< Γ l₁ , (ty< a l₂ , ty< b l₃)) ≡ (ctx< Γ' l₁' , (ty< a' l₂' , ty< b' l₃'))
    helper refl = ap (λ{ (l₁ , l₂ , l₃) → (ctx< Γ l₁ , (ty< a l₂ , ty< b l₃)) }) (<-alleq ×≡ <-alleq ×≡ <-alleq)
ap-inv-↑≤args-of-tag-ty {suc (suc n)} {suc (suc m)} p₁ p₂ {1} (ctx< Γ l₁ , ((ty< a l₂ , ty< b l₃) , (tm< s l₄ , ty< T l₅))) (ctx< Γ' l₁' , ((ty< a' l₂' , ty< b' l₃') , (tm< s' l₄' , ty< T' l₅'))) pf = helper {l₁} {l₂} {l₃} {l₄} {l₅} {l₁'} {l₂'} {l₃'} {l₄'} {l₅'} (ap (λ{ (Γ , ((a , b) , (s , T))) → (Γ .ctx , ((a .ty , b .ty) , (s .tm , T .ty))) }) pf)
  where
    helper : ∀ {l₁ l₂ l₃ l₄ l₅ l₁' l₂' l₃' l₄' l₅'} → (Γ , ((a , b) , (s , T))) ≡ (Γ' , ((a' , b') , (s' , T'))) → (ctx< Γ l₁ , ((ty< a l₂ , ty< b l₃) , (tm< s l₄ , ty< T l₅))) ≡ (ctx< Γ' l₁' , ((ty< a' l₂' , ty< b' l₃') , (tm< s' l₄' , ty< T' l₅')))
    helper refl = ap (λ{ (l₁ , l₂ , l₃ , l₄ , l₅) → (ctx< Γ l₁ , ((ty< a l₂ , ty< b l₃) , (tm< s l₄ , ty< T l₅))) }) (<-alleq ×≡ <-alleq ×≡ <-alleq ×≡ <-alleq ×≡ <-alleq)
ap-inv-↑≤args-of-tag-ty {suc (suc n)} {suc (suc m)} p₁ p₂ {7} (ctx< Γ _) (ctx< Γ' _) pf = ctx<≡ (ap ctx pf)
ap-inv-↑≤args-of-tag-ty {suc (suc (suc (suc (suc n))))} {suc (suc (suc (suc (suc m))))} p₁ p₂ {8} (ctx< Γ _) (ctx< Γ' _) pf = ctx<≡ (ap ctx pf)

reconstruct-ty : ∀ {n} → Σ _ (args-of-tag-ty n) → Σ _ (TySyntax< (suc n))
reconstruct-ty (0 , (Γ , ((ty< A A<) , (ty< B B<)))) = ↑ctx <-suc Γ , (ty< (A ‘→’ B) (<-suc→ (max-<-spec-build A< B<)))
reconstruct-ty (2 , (Γ , (ty< A A< , ty< B B<))) = ↑ctx <-suc Γ , (ty< (A ‘×’ B) (<-suc→ (max-<-spec-build A< B<)))
reconstruct-ty (3 , (ctx< Γ Γ<)) = ctx< Γ (Γ< ■< <-suc) , (ty< (𝟙 {Γ}) (<-suc→ Γ<))
reconstruct-ty (6 , ctx< Γ Γ<) = ctx< Γ (Γ< ■< <-suc) , ty< (‘CtxSyntax’ {Γ}) (<-suc→ Γ<)
reconstruct-ty {suc sz} (4 , (ctx< Γ Γ< , (ty< A A< , ty< B B<))) = ctx< Γ (Γ< ■< <-suc ■< <-suc) , ty< (‘Σ’ A B) (<-suc→ (max-<-spec-build (A< ■< <-suc) B<))
reconstruct-ty {suc sz} (5 , (ctx< Γ Γ< , (ty< A A< , ty< B B<))) = ctx< Γ (Γ< ■< <-suc ■< <-suc) , ty< (‘Π’ A B) (<-suc→ (max-<-spec-build (A< ■< <-suc) B<))
reconstruct-ty {suc (suc sz)} (1 , (ctx< Γ Γ< , ((ty< a a< , ty< b b<) , ((tm< s s<) , (ty< T T<))))) = ctx< (Γ ▻ a) (<-suc→ (a< ■< <-suc ■< <-suc)) , ty< (s ⨾𝒰 T) (<-suc→ (<-suc→ (max-<-spec-build s< T<)))
reconstruct-ty {suc (suc sz)} (7 , ctx< Γ Γ<) = ctx< (Γ ▻ ‘CtxSyntax’) (<-suc→ (<-suc→ (Γ< ■< <-suc))) , ty< (‘TySyntax’ {Γ}) (<-suc→ (<-suc→ (<-suc→ Γ<)))
reconstruct-ty {suc (suc (suc (suc (suc sz))))} (8 , ctx< Γ Γ<) = ctx< (Γ ▻ ‘Σ’ ‘CtxSyntax’ ‘TySyntax’) (<-suc→ (<-suc→ (<-suc→ (max-<-spec-build (Γ< ■< <-suc ■< <-suc ■< <-suc) (<-suc→ (<-suc→ (Γ< ■< <-suc))))))) , ty< (‘TmSyntax’ {Γ}) (<-suc→ (<-suc→ (<-suc→ (<-suc→ (<-suc→ (<-suc→ Γ<))))))

deconstruct-ty : ∀ {Γ} T → args-of-tag-ty (Ty-len T) (tag-ty {Γ} T)
deconstruct-ty (A ‘→’ B) = ctx< _ (<-trans (Ty-len< A) (<-max-spec-L-suc <-suc)) , ((ty< A (<-max-spec-L-suc <-suc)) , (ty< B (<-max-spec-R-suc <-suc)))
deconstruct-ty (s ⨾𝒰 T) = ctx< _ (<-max-spec-R (<-suc ■< <-suc→ (Ty-len< _) ■< Ty-len< T)) , ((ty< _ (<-max-spec-L (<-max-spec-L-suc <-suc ■< (Tm-len< s))) , ty< _ (<-suc ■< <-max-spec-R {_} {Tm-len s} (Ty-len< T))) , ((tm< s (<-max-spec-L-suc <-suc)) , (ty< T (<-max-spec-R-suc <-suc))))
deconstruct-ty (A ‘×’ B) = ctx< _ (<-trans (Ty-len< A) (<-max-spec-L-suc <-suc)) , ((ty< A (<-max-spec-L-suc <-suc)) , (ty< B (<-max-spec-R-suc <-suc)))
deconstruct-ty (𝟙 {Γ}) = ctx< Γ <-suc
deconstruct-ty (‘Σ’ A B) = ctx< _ (<-max-spec-L (Ty-len< A)) , (ty< A (<-max-spec-R (<-suc ■< Ty-len< B)) , ty< B (<-max-spec-R-suc <-suc))
deconstruct-ty (‘Π’ A B) = ctx< _ (<-max-spec-L (Ty-len< A)) , (ty< A (<-max-spec-R (<-suc ■< Ty-len< B)) , ty< B (<-max-spec-R-suc <-suc))
deconstruct-ty (‘CtxSyntax’ {Γ}) = ctx< Γ <-suc
deconstruct-ty (‘TySyntax’ {Γ}) = ctx< Γ <-suc
deconstruct-ty (‘TmSyntax’ {Γ}) = ctx< Γ <-suc

reconstruct-ty-eq : ∀ {Γ} T → reconstruct-ty {Ty-len T} (tag-ty T , deconstruct-ty T) ≡ ((ctx< Γ (Ty-len< T ■< <-suc)) , ty< T <-suc)
reconstruct-ty-eq (A ‘→’ B) = ctx<,ty<≡ refl
reconstruct-ty-eq (s ⨾𝒰 T) = ctx<,ty<≡ refl
reconstruct-ty-eq (A ‘×’ B) = ctx<,ty<≡ refl
reconstruct-ty-eq 𝟙 = ctx<,ty<≡ refl
reconstruct-ty-eq (‘Σ’ A B) = ctx<,ty<≡ refl
reconstruct-ty-eq (‘Π’ A B) = ctx<,ty<≡ refl
reconstruct-ty-eq ‘CtxSyntax’ = ctx<,ty<≡ refl
reconstruct-ty-eq ‘TySyntax’ = ctx<,ty<≡ refl
reconstruct-ty-eq ‘TmSyntax’ = ctx<,ty<≡ refl

args-of-tag-tm : ℕ → ℕ → Set
args-of-tag-tm sz 0 = Σ _ TySyntax
args-of-tag-tm sz 1 = Σ _ λ{ Γ → Σ (TySyntax Γ × TySyntax Γ × TySyntax Γ) λ{ (a , b , c) → (a ~> b) × (b ~> c) } }
args-of-tag-tm sz 2 = Σ _ λ{ Γ → TySyntax Γ × TySyntax Γ }
args-of-tag-tm sz 3 = Σ _ λ{ Γ → Σ (TySyntax Γ × TySyntax Γ × TySyntax Γ) λ{ (a , b , c) → ((a ‘×’ b) ~> c) } }
args-of-tag-tm sz 4 = Σ _ λ{ Γ → TySyntax Γ }
args-of-tag-tm sz 5 = Σ _ λ{ Γ → Σ (TySyntax Γ × TySyntax Γ × TySyntax Γ × TySyntax Γ) λ{ (a , b , c , d) → (a ~> b) × (c ~> d) } }
args-of-tag-tm sz 6 = CtxSyntax × CtxSyntax
args-of-tag-tm sz 7 = Σ _ λ{ Γ → Σ (TySyntax Γ × TySyntax Γ) λ{ (a , b) → (a ~> b) } }
args-of-tag-tm sz 8 = Σ _ λ{ Γ → Σ (TySyntax Γ) λ{ a → (a ~>𝒰) } }
args-of-tag-tm sz 9 = Σ _ λ{ Γ → TySyntax Γ × TySyntax Γ }
args-of-tag-tm sz 10 = CtxSyntax
args-of-tag-tm sz 11 = Σ _ λ{ Γ → TySyntax Γ }
args-of-tag-tm sz 12 = Σ _ λ{ Γ → TySyntax Γ × TySyntax Γ }
args-of-tag-tm sz 13 = Σ _ λ { Γ → Σ (TySyntax Γ × TySyntax Γ) λ{ (X , A) → Σ _ λ{ B → Σ (TmSyntax {Γ} (X ‘→’ A)) λ{ a → TmSyntax {Γ} (‘Π’ X (a ⨾𝒰 B)) } } } }
args-of-tag-tm sz 14 = Σ _ λ{ Γ → Σ (TySyntax Γ × TySyntax Γ) λ{ (a , b) → TmSyntax {Γ} b } }
args-of-tag-tm sz 15 = Σ _ λ{ Γ → Σ (TySyntax Γ × TySyntax Γ) λ{ (a , b) → (a ~> b) × TmSyntax {Γ} a } }
args-of-tag-tm sz 16 = CtxSyntax
args-of-tag-tm sz 17 = Σ (CtxSyntax × CtxSyntax) λ{ (Γ , C) → TySyntax C }
args-of-tag-tm sz 18 = Σ (CtxSyntax × CtxSyntax) λ{ (Γ , C) → Σ _ λ{ A → TmSyntax {C} A } }
args-of-tag-tm sz 19 = CtxSyntax
args-of-tag-tm sz 20 = Σ _ λ{ Γ → Σ (_ × TySyntax Γ) λ{ (A , B) → Σ (TmSyntax {Γ} (𝟙 ‘→’ ‘CtxSyntax’)) λ{ c → ((‘Π’ 𝟙 (c ⨾𝒰 A)) ~> B) × (𝟙 ~> B) } } }
args-of-tag-tm sz (suc 20) = Σ _ λ{ Γ → TySyntax Γ }
args-of-tag-tm sz _ = ⊥

↑≤args-of-tag-tm : ∀ {n m} → (p : n ≤ m) → ∀ {t} → args-of-tag-tm n t → args-of-tag-tm m t
↑≤args-of-tag-tm p {t} v = {!!}

ap-inv-↑≤args-of-tag-tm : ∀ {n m} → (p₁ p₂ : n ≤ m) → ∀ {t} (v₁ v₂ : args-of-tag-tm n t) → ↑≤args-of-tag-tm p₁ {t} v₁ ≡ ↑≤args-of-tag-tm p₂ {t} v₂ → v₁ ≡ v₂
ap-inv-↑≤args-of-tag-tm {n} {m} p₁ p₂ {t} v₁ v₂ pf = {!!}

reconstruct-tm : ∀ {n} → Σ _ (args-of-tag-tm n) → Σ (Σ _ (TySyntax< (suc n))) (λ{ (Γ , T) → TmSyntax< (suc n) {Γ} T })
reconstruct-tm (0 , (Γ , a)) = (_ , _) , tm< (‘id’ {Γ} {a}) {!!}
reconstruct-tm (1 , (_ , (_ , (f , g)))) = (_ , _) , tm< (f ⨾ g) {!!}
reconstruct-tm (2 , (_ , (a , b))) = (_ , _) , tm< (apply {_} {a} {b}) {!!}
reconstruct-tm (3 , (_ , (_ , f))) = (_ , _) , tm< (curry f) {!!}
reconstruct-tm (4 , (_ , a)) = (_ , _) , tm< (dup {_} {a}) {!!}
reconstruct-tm (5 , (_ , (_ , (f , g)))) = (_ , _) , tm< (f ‘××’ g) {!!}
reconstruct-tm (6 , (Γ , c)) = (_ , _) , tm< (⌜_⌝c {Γ} c) {!!}
reconstruct-tm (7 , (_ , (_ , f))) = (_ , _) , tm< (□-map f) {!!}
reconstruct-tm (8 , (_ , (_ , f))) = (_ , _) , tm< (□-map𝒰 f) {!!}
reconstruct-tm (9 , (_ , (a , b))) = (_ , _) , tm< (□-×-codistr {_} {a} {b}) {!!}
reconstruct-tm (10 , Γ) = (_ , _) , tm< (□-𝟙-codistr {Γ}) {!!}
reconstruct-tm (11 , (_ , a)) = (_ , _) , tm< (quot {_} {a}) {!!}
reconstruct-tm (12 , (_ , (a , b))) = (_ , _) , tm< (fst {_} {a} {b}) {!!}
reconstruct-tm (13 , (_ , (_ , (_ , (x , y))))) = (_ , _) , tm< (x ‘,Σ’ y) {!!}
reconstruct-tm (14 , (_ , ((a , b) , v))) = (_ , _) , tm< (const {_} {a} {b} v) {!!}
reconstruct-tm (15 , (_ , (_ , (f , x)))) = (_ , _) , tm< (f ‘’ₐ x) {!!}
reconstruct-tm (16 , Γ) = (_ , _) , tm< (‘tt’ {Γ}) {!!}
reconstruct-tm (17 , ((Γ , C) , T)) = (ctx< Γ {!!} , _) , tm< (⌜ T ⌝) {!!}
reconstruct-tm (18 , ((Γ , C) , (T , t))) = (ctx< Γ {!!} , _) , tm< (⌜ t ⌝ₜ) {!!}
reconstruct-tm (19 , Γ) = (_ , _) , tm< (‘quote’ {Γ}) {!!}
reconstruct-tm (20 , (_ , (_ , (c , (t , f))))) = (_ , _) , tm< (semidec-eq-proj₁ c t f) {!!}
reconstruct-tm (suc 20 , (Γ , A)) = (_ , _) , tm< (‘subst’ {Γ} {A}) {!!}

deconstruct-tm : ∀ {Γ T} t → args-of-tag-tm (Tm-len t) (tag-tm {Γ} {T} t)
deconstruct-tm (‘id’ {Γ} {a}) = _ , a
deconstruct-tm (f ⨾ g) = _ , (_ , _ , _) , f , g
deconstruct-tm (apply {Γ} {a} {b}) = Γ , (a , b)
deconstruct-tm (curry f) = _ , (_ , f)
deconstruct-tm (dup {Γ} {a}) = Γ , a
deconstruct-tm (f ‘××’ g) = _ , (_ , (f , g))
deconstruct-tm (⌜_⌝c {Γ} c) = Γ , c
deconstruct-tm (□-map f) = _ , (_ , f)
deconstruct-tm (□-map𝒰 f) = _ , (_ , f)
deconstruct-tm (□-×-codistr {_} {a} {b}) = _ , (a , b)
deconstruct-tm (□-𝟙-codistr {Γ}) = Γ
deconstruct-tm (quot {_} {a}) = _ , a
deconstruct-tm (fst {_} {a} {b}) = _ , (a , b)
deconstruct-tm (x ‘,Σ’ y) = _ , (_ , (_ , (x , y)))
deconstruct-tm (const {_} {a} {b} t) = _ , ((a , _) , t)
deconstruct-tm (f ‘’ₐ x) = _ , ((_ , _) , (f , x))
deconstruct-tm (‘tt’ {Γ}) = Γ
deconstruct-tm (⌜_⌝ {Γ} T) = (Γ , _) , T
deconstruct-tm (⌜_⌝ₜ {Γ} t) = (Γ , _) , (_ , t)
deconstruct-tm (‘quote’ {Γ}) = Γ
deconstruct-tm (semidec-eq-proj₁ c t f) = _ , ((_ , _) , (c , (t , f)))
deconstruct-tm (‘subst’ {Γ} {A}) = Γ , A

reconstruct-tm-eq : ∀ {Γ T} t → reconstruct-tm {Tm-len t} (tag-tm {Γ} {T} t , deconstruct-tm {Γ} {T} t) ≡ ((ctx< Γ (Ty-len< T ■< Tm-len< t ■< <-suc) , ty< T (Tm-len< t ■< <-suc)) , tm< t <-suc)
reconstruct-tm-eq ‘id’ = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq (f ⨾ g) = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq apply = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq (curry f) = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq dup = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq (f ‘××’ g) = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq ⌜ c ⌝c = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq (□-map f) = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq (□-map𝒰 f) = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq □-×-codistr = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq □-𝟙-codistr = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq quot = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq fst = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq (x ‘,Σ’ y) = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq (const t) = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq (f ‘’ₐ x) = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq ‘tt’ = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq ⌜ T ⌝ = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq ⌜ t ⌝ₜ = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq ‘quote’ = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq (semidec-eq-proj₁ c t f) = ctx<,ty<,tm<≡ refl
reconstruct-tm-eq ‘subst’ = ctx<,ty<,tm<≡ refl

module sized where
  Ctx-dec-eq : ∀ {n} → dec-eq (CtxSyntax< n)
  Ty-dec-eq : ∀ {n} → dec-eq (Σ _ (TySyntax< n))
  Tm-dec-eq : ∀ {n} → dec-eq (Σ (Σ _ (TySyntax< n)) λ{ (Γ , T) → TmSyntax< n {Γ} T })

  Ty-dec-eq-homogenous : ∀ {n Γ} → dec-eq (TySyntax< n Γ)
  Ty-dec-eq-homogenous {n} {Γ} T₁ T₂ with (Ty-dec-eq {n} (Γ , T₁) (Γ , T₂))
  ... | inj₁ p = inj₁ (trans (K-from-dec (Ctx-dec-eq {n}) (λ{ p → T₁ ≡ sub (TySyntax< n) p T₁ }) refl) (apD-proj₂ p))
  ... | inj₂ n = inj₂ λ{ refl → n refl }

  Tm-dec-eq-homogenous : ∀ {n Γ T} → dec-eq (TmSyntax< n {Γ} T)
  Tm-dec-eq-homogenous {n} {Γ} {T} t₁ t₂ with (Tm-dec-eq (_ , t₁) (_ , t₂))
  ... | inj₁ p = inj₁ (trans (K-from-dec Ty-dec-eq (λ{ p → t₁ ≡ sub (λ{ (Γ , T) → TmSyntax< n {Γ} T }) p t₁ }) refl) (apD-proj₂ p))
  ... | inj₂ n = inj₂ λ{ refl → n refl }

  args-of-tag-ctx-dec-eq : ∀ {sz n} → dec-eq (args-of-tag-ctx sz n)
  args-of-tag-ctx-dec-eq {_} {0} tt tt = inj₁ refl
  args-of-tag-ctx-dec-eq {suc sz} {1} = Ty-dec-eq {suc sz}
  args-of-tag-ctx-dec-eq {suc _} {suc (suc _)} ()

  args-of-tag-ty-dec-eq : ∀ {sz n} → dec-eq (args-of-tag-ty sz n)
  args-of-tag-ty-dec-eq {sz} {0} = Σ-dec-eq (Ctx-dec-eq {sz}) (×-dec-eq Ty-dec-eq-homogenous Ty-dec-eq-homogenous)
  args-of-tag-ty-dec-eq {sz} {2} = Σ-dec-eq Ctx-dec-eq (×-dec-eq Ty-dec-eq-homogenous Ty-dec-eq-homogenous)
  args-of-tag-ty-dec-eq {sz} {3} = Ctx-dec-eq
  args-of-tag-ty-dec-eq {sz} {4} with sz
  ... | 0 = λ()
  ... | suc sz = Σ-dec-eq Ctx-dec-eq (Σ-dec-eq Ty-dec-eq-homogenous Ty-dec-eq-homogenous)
  args-of-tag-ty-dec-eq {sz} {5} with sz
  ... | 0 = λ()
  ... | suc sz = Σ-dec-eq Ctx-dec-eq (Σ-dec-eq Ty-dec-eq-homogenous Ty-dec-eq-homogenous)
  args-of-tag-ty-dec-eq {sz} {6} = Ctx-dec-eq
  args-of-tag-ty-dec-eq {0} {suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))} ()
  args-of-tag-ty-dec-eq {suc sz} {suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))} ()
  args-of-tag-ty-dec-eq {suc (suc sz)} {1} = Σ-dec-eq Ctx-dec-eq (Σ-dec-eq (×-dec-eq Ty-dec-eq-homogenous Ty-dec-eq-homogenous) (×-dec-eq Tm-dec-eq-homogenous Ty-dec-eq-homogenous))
  args-of-tag-ty-dec-eq {suc (suc sz)} {7} = Ctx-dec-eq
  args-of-tag-ty-dec-eq {suc (suc (suc (suc (suc sz))))} {8} = Ctx-dec-eq

  args-of-tag-tm-dec-eq : ∀ {sz n} → dec-eq (args-of-tag-tm sz n)
  args-of-tag-tm-dec-eq {sz} {n} = {!!}

  Ctx-dec-eq {suc sz} Γ₁ Γ₂ = res
    module Ctx-dec-eq where
      dec-tag : dec-eq-on (tag-ctx (Γ₁ .ctx)) (tag-ctx (Γ₂ .ctx))
      dec-tag = ℕ-dec-eq _ _

      dec-len : dec-eq-on (Ctx-len (Γ₁ .ctx)) (Ctx-len (Γ₂ .ctx))
      dec-len = ℕ-dec-eq _ _

      dec-args : (p : tag-ctx (Γ₁ .ctx) ≡ tag-ctx (Γ₂ .ctx))
        → (q : Ctx-len (Γ₁ .ctx) ≡ Ctx-len (Γ₂ .ctx))
        → dec-eq-on (↑≤args-of-tag-ctx (CtxSyntax<_.lt Γ₂) (sub (args-of-tag-ctx _) p (sub (λ{ t → args-of-tag-ctx t (tag-ctx (Γ₁ .ctx)) }) q (deconstruct-ctx (Γ₁ .ctx)))))
                    (↑≤args-of-tag-ctx (CtxSyntax<_.lt Γ₂) (deconstruct-ctx (Γ₂ .ctx)))
      dec-args p q = args-of-tag-ctx-dec-eq {sz} {tag-ctx (Γ₂ .ctx)} _ _

      res : dec-eq-on Γ₁ Γ₂
      res with dec-tag | dec-len
      ... | inj₁ p | inj₁ q with (dec-args p q)
      ...                   | inj₁ r = inj₁ (ctx<≡ (trans (sym (ap (λ{ Γ → Γ .ctx }) (reconstruct-ctx-eq _))) (trans (trans (helper q) (ap (λ{ Γ → (reconstruct-ctx Γ) .ctx }) (p ,≡ ap-inv-↑≤args-of-tag-ctx _ _ _ _ r))) (ap (λ{ Γ → Γ .ctx }) (reconstruct-ctx-eq _)))))
        where
          helper : ∀ {n} → (q : Ctx-len (Γ₁ .ctx) ≡ n)
            → reconstruct-ctx (tag-ctx (Γ₁ .ctx) , deconstruct-ctx (Γ₁ .ctx)) .ctx
              ≡
              reconstruct-ctx (tag-ctx (Γ₁ .ctx) , sub (λ{ t → args-of-tag-ctx t (tag-ctx (Γ₁ .ctx)) }) q (deconstruct-ctx (Γ₁ .ctx))) .ctx
          helper refl = refl
      ...                   | inj₂ r = inj₂ (λ{ refl → r (ℕ2-K (λ{ p q → ↑≤args-of-tag-ctx (CtxSyntax<_.lt Γ₁) (sub (args-of-tag-ctx _) p (sub (λ{ t → args-of-tag-ctx t (tag-ctx (Γ₁ .ctx)) }) q _)) ≡ _ }) refl {p} {q}) })
      res | inj₂ p | _ = inj₂ (λ{ refl → p refl })
      res | inj₁ _ | inj₂ p = inj₂ (λ{ refl → p refl })

  Ty-dec-eq {suc sz} ΓT₁@(_ , T₁) ΓT₂@(_ , T₂) = res
    module Ty-dec-eq where
      dec-tag : dec-eq-on (tag-ty (T₁ .ty)) (tag-ty (T₂ .ty))
      dec-tag = ℕ-dec-eq _ _

      dec-len : dec-eq-on (Ty-len (T₁ .ty)) (Ty-len (T₂ .ty))
      dec-len = ℕ-dec-eq _ _

      dec-args : (p : tag-ty (T₁ .ty) ≡ tag-ty (T₂ .ty))
        → (q : Ty-len (T₁ .ty) ≡ Ty-len (T₂ .ty))
          → dec-eq-on (↑≤args-of-tag-ty (TySyntax<.lt T₂) {tag-ty (T₂ .ty)} (sub (args-of-tag-ty (Ty-len (T₂ .ty))) p (sub (λ{ t → args-of-tag-ty t (tag-ty (T₁ .ty)) }) q (deconstruct-ty (T₁ .ty)))))
                      (↑≤args-of-tag-ty (TySyntax<.lt T₂) {tag-ty (T₂ .ty)} (deconstruct-ty (T₂ .ty)))
      dec-args p q = args-of-tag-ty-dec-eq {sz} {tag-ty (T₂ .ty)} _ _

      res : dec-eq-on ΓT₁ ΓT₂
      res with dec-tag | dec-len
      ... | inj₁ p | inj₁ q with (dec-args p q)
      ...                   | inj₁ r = inj₁ (ctx<,ty<≡ (trans (sym (ap ctx-ty (reconstruct-ty-eq _))) (trans (trans (helper q) (ap (λ{ T → ctx-ty (reconstruct-ty T) }) (p ,≡ ap-inv-↑≤args-of-tag-ty (TySyntax<.lt T₂) (TySyntax<.lt T₂) {tag-ty (T₂ .ty)} _ _ r))) (ap ctx-ty (reconstruct-ty-eq _)))))
        where
          helper : ∀ {n} → (q : Ty-len (T₁ .ty) ≡ n)
            → ctx-ty (reconstruct-ty (tag-ty (T₁ .ty) , deconstruct-ty (T₁ .ty)))
              ≡
              ctx-ty (reconstruct-ty (tag-ty (T₁ .ty) , sub (λ{ t → args-of-tag-ty t (tag-ty (T₁ .ty)) }) q (deconstruct-ty (T₁ .ty))))
          helper refl = refl
      ...                   | inj₂ r = inj₂ (λ{ refl → r (ℕ2-K (λ{ p q → ↑≤args-of-tag-ty (TySyntax<.lt T₁) {tag-ty (T₂ .ty)} (sub (args-of-tag-ty _) p (sub (λ{ t → args-of-tag-ty t (tag-ty (T₁ .ty)) }) q _)) ≡ _ }) refl {p} {q}) })
      res | inj₂ p | _ = inj₂ (λ{ refl → p refl })
      res | inj₁ _ | inj₂ p = inj₂ (λ{ refl → p refl })

  Tm-dec-eq {suc sz} Γt₁@(_ , t₁) Γt₂@(_ , t₂) = res
    module Tm-dec-eq where
      dec-tag : dec-eq-on (tag-tm (t₁ .tm)) (tag-tm (t₂ .tm))
      dec-tag = ℕ-dec-eq _ _

      dec-len : dec-eq-on (Tm-len (t₁ .tm)) (Tm-len (t₂ .tm))
      dec-len = ℕ-dec-eq _ _

      dec-args : (p : tag-tm (t₁ .tm) ≡ tag-tm (t₂ .tm))
        → (q : Tm-len (t₁ .tm) ≡ Tm-len (t₂ .tm))
        → dec-eq-on (↑≤args-of-tag-tm (TmSyntax<.lt t₂) {tag-tm (t₂ .tm)} (sub (args-of-tag-tm (Tm-len (t₂ .tm))) p (sub (λ{ t → args-of-tag-tm t (tag-tm (t₁ .tm)) }) q (deconstruct-tm (t₁ .tm)))))
                    (↑≤args-of-tag-tm (TmSyntax<.lt t₂) {tag-tm (t₂ .tm)} (deconstruct-tm (t₂ .tm)))
      dec-args p q = args-of-tag-tm-dec-eq {sz} {tag-tm (t₂ .tm)} _ _

      res : dec-eq-on Γt₁ Γt₂
      res with dec-tag | dec-len
      ... | inj₁ p | inj₁ q with (dec-args p q)
      ...                   | inj₁ r = inj₁ ((ctx<,ty<,tm<≡ (trans (sym (ap ctx-ty-tm (reconstruct-tm-eq _))) (trans (trans (helper q) (ap (λ{ T → ctx-ty-tm (reconstruct-tm T) }) (p ,≡ ap-inv-↑≤args-of-tag-tm (TmSyntax<.lt t₂) (TmSyntax<.lt t₂) {tag-tm (t₂ .tm)} _ _ r))) (ap ctx-ty-tm (reconstruct-tm-eq _))))))
        where
          helper : ∀ {n} → (q : Tm-len (t₁ .tm) ≡ n)
            → ctx-ty-tm (reconstruct-tm {Tm-len (t₁ .tm)} (tag-tm (t₁ .tm) , deconstruct-tm (t₁ .tm)))
              ≡
              ctx-ty-tm (reconstruct-tm {n} (tag-tm (t₁ .tm) , sub (λ{ t → args-of-tag-tm t (tag-tm (t₁ .tm)) }) q (deconstruct-tm (t₁ .tm))))
          helper refl = refl
      ...                   | inj₂ r = inj₂ (λ{ refl → r (ℕ2-K (λ{ p q → ↑≤args-of-tag-tm (TmSyntax<.lt t₁) {tag-tm (t₂ .tm)} (sub (args-of-tag-tm (Tm-len (t₂ .tm))) p (sub (λ{ t → args-of-tag-tm t (tag-tm (t₁ .tm)) }) q (deconstruct-tm (t₁ .tm)))) ≡ ↑≤args-of-tag-tm (TmSyntax<.lt t₁) {tag-tm (t₂ .tm)} (deconstruct-tm (t₂ .tm)) }) refl {p} {q}) })
      res | inj₂ p | _ = inj₂ (λ{ refl → p refl })
      res | inj₁ _ | inj₂ p = inj₂ (λ{ refl → p refl })

Ctx-dec-eq : dec-eq CtxSyntax
Ctx-dec-eq Γ₁ Γ₂ with (sized.Ctx-dec-eq (ctx< Γ₁ (<-max-spec-L {_} {_} {suc (Ctx-len Γ₂)} <-suc)) (ctx< Γ₂ (<-max-spec-R {_} {suc (Ctx-len Γ₁)} {_} <-suc)))
... | inj₁ p = inj₁ (ap ctx p)
... | inj₂ p = inj₂ (λ{ refl → p (ctx<≡ refl) })
Ty-dec-eq : dec-eq (Σ _ TySyntax)
Ty-dec-eq ΓT₁@(Γ₁ , T₁) ΓT₂@(Γ₂ , T₂)
  with (sized.Ty-dec-eq
       (ctx<ty< ΓT₁ (<-max-spec-L {_} {_} {max (suc (Ctx-len Γ₂)) (suc (Ty-len T₂))} (<-max-spec-L {_} {_} {suc (Ty-len T₁)} <-suc))
                    (<-max-spec-L {_} {_} {max (suc (Ctx-len Γ₂)) (suc (Ty-len T₂))} (<-max-spec-R {_} {suc (Ctx-len Γ₁)} {_} <-suc)))
       (ctx<ty< ΓT₂ (<-max-spec-R {_} {max (suc (Ctx-len Γ₁)) (suc (Ty-len T₁))} {_} (<-max-spec-L {_} {_} {suc (Ty-len T₂)} <-suc))
                    (<-max-spec-R {_} {max (suc (Ctx-len Γ₁)) (suc (Ty-len T₁))} {_} (<-max-spec-R {_} {suc (Ctx-len Γ₂)} {_} <-suc))))
... | inj₁ p = inj₁ (ap ctx-ty p)
... | inj₂ p = inj₂ (λ{ refl → p (ctx<,ty<≡ refl) })
Tm-dec-eq : dec-eq (Σ (Σ _ TySyntax) λ{ (Γ , T) → TmSyntax {Γ} T })
Tm-dec-eq Γt₁@((Γ₁ , T₁) , t₁) Γt₂@((Γ₂ , T₂) , t₂)
  with (sized.Tm-dec-eq
       (ctx<ty<tm< Γt₁ (<-max-spec-L {_} {_} {max (max (suc (Ctx-len Γ₂)) (suc (Ty-len T₂))) (suc (Tm-len t₂))} (<-max-spec-L {_} {_} {suc (Tm-len t₁)} (<-max-spec-L {_} {_} {suc (Ty-len T₁)} <-suc)))
                       (<-max-spec-L {_} {_} {max (max (suc (Ctx-len Γ₂)) (suc (Ty-len T₂))) (suc (Tm-len t₂))} (<-max-spec-L {_} {_} {suc (Tm-len t₁)} (<-max-spec-R {_} {suc (Ctx-len Γ₁)} {_} <-suc)))
                       (<-max-spec-L {_} {_} {max (max (suc (Ctx-len Γ₂)) (suc (Ty-len T₂))) (suc (Tm-len t₂))} (<-max-spec-R {_} {max (suc (Ctx-len Γ₁)) (suc (Ty-len T₁))} {_} <-suc)))
       (ctx<ty<tm< Γt₂ (<-max-spec-R {_} {max (max (suc (Ctx-len Γ₁)) (suc (Ty-len T₁))) (suc (Tm-len t₁))} {_} (<-max-spec-L {_} {_} {suc (Tm-len t₂)} (<-max-spec-L {_} {_} {suc (Ty-len T₂)} <-suc)))
                       (<-max-spec-R {_} {max (max (suc (Ctx-len Γ₁)) (suc (Ty-len T₁))) (suc (Tm-len t₁))} {_} (<-max-spec-L {_} {_} {suc (Tm-len t₂)} (<-max-spec-R {_} {suc (Ctx-len Γ₂)} {_} <-suc)))
                       (<-max-spec-R {_} {max (max (suc (Ctx-len Γ₁)) (suc (Ty-len T₁))) (suc (Tm-len t₁))} {_} (<-max-spec-R {_} {max (suc (Ctx-len Γ₂)) (suc (Ty-len T₂))} {_} <-suc))))
... | inj₁ p = inj₁ (ap ctx-ty-tm p)
... | inj₂ p = inj₂ (λ{ refl → p (ctx<,ty<,tm<≡ refl) })

Ty-dec-eq-homogenous : ∀ {Γ} → dec-eq (TySyntax Γ)
Ty-dec-eq-homogenous {Γ} T₁ T₂ with (Ty-dec-eq (Γ , T₁) (Γ , T₂))
... | inj₁ p = inj₁ (trans (K-from-dec Ctx-dec-eq (λ{ p → T₁ ≡ sub TySyntax p T₁ }) refl) (apD-proj₂ p))
... | inj₂ n = inj₂ λ{ refl → n refl }

Tm-dec-eq-homogenous : ∀ {Γ T} → dec-eq (TmSyntax {Γ} T)
Tm-dec-eq-homogenous {Γ} {T} t₁ t₂ with (Tm-dec-eq (_ , t₁) (_ , t₂))
... | inj₁ p = inj₁ (trans (K-from-dec Ty-dec-eq (λ{ p → t₁ ≡ sub (λ{ (Γ , T) → TmSyntax {Γ} T }) p t₁ }) refl) (apD-proj₂ p))
... | inj₂ n = inj₂ λ{ refl → n refl }
