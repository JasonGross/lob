{-# OPTIONS --without-K #-}
module well-typed-initial-context-internal where
open import well-typed-syntax
open import well-typed-syntax-helpers
open import well-typed-syntax-helpers-postulates
open import common

pattern ε₀▻‘Typ’ = ε₀
  ▻ ‘Set’ {- ‘Context’ : Typ ε -}
pattern ‘Context’p₀ = El (WSet ‘VAR₀’)

εp₁ : Context
εp₁ = ε₀▻‘Typ’
  ▻ (‘Context’p₀ ‘→'’ ‘Set’) {- ‘Typ’ : Typ (ε ▻ ‘Context’)-}
‘Context’p₁ : Typ εp₁
‘Context’p₁ = W ‘Context’p₀
‘Typ’p₁     : Typ (εp₁ ▻ ‘Context’p₁)
‘Typ’p₁     = El (WWSet (un‘λ'∙’ (weakenTyp-tProd-nd ‘VAR₀’)))

εp₂        : Context
‘Context’p₂ : Typ εp₂
‘Typ’p₂     : Typ (εp₂ ▻ ‘Context’p₂)
‘Term’p₂    : Typ (εp₂ ▻ ‘Context’p₂ ▻ ‘Typ’p₂)
εp₂ = εp₁
  ▻ (‘Context’p₁ ‘→’ ‘Typ’p₁ ‘→'’ W ‘Set’) {- ‘Term’ : Typ (ε ▻ ‘Context’ ▻ ‘Typ’) -}
‘Context’p₂ = W ‘Context’p₁
‘Typ’p₂     = W1 ‘Typ’p₁
‘Term’p₂    = El (WWWSet
                    (weakenTyp-weakenTyp1-weakenTyp
                     (un‘λ'∙’ (un‘λ∙’ (weakenTyp-tProd-tProd-nd ‘VAR₀’)))))

εp₃        : Context
‘Context’p₃ : Typ εp₃
‘Typ’p₃     : Typ (εp₃ ▻ ‘Context’p₃)
‘Term’p₃    : Typ (εp₃ ▻ ‘Context’p₃ ▻ ‘Typ’p₃)
‘ε₀’p₃       : Term ‘Context’p₃
εp₃ = εp₂
  ▻ ‘Context’p₂ {- ‘ε₀’ -}
‘Context’p₃ = W ‘Context’p₂
‘Typ’p₃     = W1 ‘Typ’p₂
‘Term’p₃    = W2 ‘Term’p₂
‘ε₀’p₃       = ‘VAR₀’

εp₄ : Context
εp₄ = εp₃
  ▻ (‘Context’p₃ ‘→’ ‘Typ’p₃ ‘→'’ W ‘Context’p₃) {- ‘_▻_’ -}
‘Context’p₄ : Typ εp₄
‘Context’p₄ = W ‘Context’p₃
‘Typ’p₄     : Typ (εp₄ ▻ ‘Context’p₄)
‘Typ’p₄     = W1 ‘Typ’p₃
‘Term’p₄    : Typ (εp₄ ▻ ‘Context’p₄ ▻ ‘Typ’p₄)
‘Term’p₄    = W2 ‘Term’p₃
‘ε₀’p₄       : Term ‘Context’p₄
‘ε₀’p₄       = w ‘ε₀’p₃
‘_▻_’p₄     : Term (‘Context’p₄ ‘→’ ‘Typ’p₄ ‘→'’ W ‘Context’p₄)
‘_▻_’p₄     = weakenTyp-tProd-tProd-nd-nd ‘VAR₀’

εp₅ : Context
εp₅ = εp₄
  ▻ (‘Context’p₄ ‘→’ ‘Typ’p₄ ‘→’ W1 (W1 ‘Typ’p₄) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₄) ‘→'’ W ‘Typ’p₄) {- ‘Σ'’ -}
‘Context’p₅ : Typ εp₅
‘Context’p₅ = W ‘Context’p₄
‘Typ’p₅     : Typ (εp₅ ▻ ‘Context’p₅)
‘Typ’p₅     = W1 ‘Typ’p₄
‘Term’p₅    : Typ (εp₅ ▻ ‘Context’p₅ ▻ ‘Typ’p₅)
‘Term’p₅    = W2 ‘Term’p₄
‘ε₀’p₅       : Term ‘Context’p₅
‘ε₀’p₅       = w ‘ε₀’p₄
‘_▻_’p₅     : Term (‘Context’p₅ ‘→’ ‘Typ’p₅ ‘→'’ W ‘Context’p₅)
‘_▻_’p₅     = w∀→₂ ‘_▻_’p₄
‘‘Σ'’’p₅     : Term (‘Context’p₅ ‘→’ ‘Typ’p₅ ‘→’ W1 (W1 ‘Typ’p₅) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₅) ‘→'’ W ‘Typ’p₅)
‘‘Σ'’’p₅     = weakenTyp-tProd-tProd-tProd-substTyp-tProd-nd-weakenTyp ‘VAR₀’

εp₆ : Context
εp₆ = εp₅
  ▻ (‘Context’p₅ ‘→’ ‘Typ’p₅ ‘→’ W1 (W1 ‘Typ’p₅) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₅) ‘→'’ ‘Term’p₅ ‘→'’ W ‘Typ’p₅) {- _‘’_ -}
‘Context’p₆ : Typ εp₆
‘Context’p₆ = W ‘Context’p₅
‘Typ’p₆     : Typ (εp₆ ▻ ‘Context’p₆)
‘Typ’p₆     = W1 ‘Typ’p₅
‘Term’p₆    : Typ (εp₆ ▻ ‘Context’p₆ ▻ ‘Typ’p₆)
‘Term’p₆    = W2 ‘Term’p₅
‘ε₀’p₆       : Term ‘Context’p₆
‘ε₀’p₆       = w ‘ε₀’p₅
‘_▻_’p₆     : Term (‘Context’p₆ ‘→’ ‘Typ’p₆ ‘→'’ W ‘Context’p₆)
‘_▻_’p₆     = w∀→₂ ‘_▻_’p₅
‘‘Σ'’’p₆     : Term (‘Context’p₆ ‘→’ ‘Typ’p₆ ‘→’ W1 (W1 ‘Typ’p₆) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₆) ‘→'’ W ‘Typ’p₆)
‘‘Σ'’’p₆     = w∀∀‘’→ ‘‘Σ'’’p₅
‘_‘’_’p₆     : Term (‘Context’p₆ ‘→’ ‘Typ’p₆ ‘→’ W1 (W1 ‘Typ’p₆) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₆) ‘→'’ ‘Term’p₆ ‘→'’ W ‘Typ’p₆)
‘_‘’_’p₆     = weakenTyp-tProd-tProd-tProd-substTyp-tProd-nd-tProd-nd-weakenTyp ‘VAR₀’

εp₇ : Context
εp₇ = εp₆
  ▻ (‘Context’p₆ ‘→’ ‘Typ’p₆ ‘→’ W1 (W1 ‘Typ’p₆) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₆) ‘→'’ W ‘Typ’p₆) {- _‘→’_ -}
‘Context’p₇ : Typ εp₇
‘Context’p₇ = W ‘Context’p₆
‘Typ’p₇     : Typ (εp₇ ▻ ‘Context’p₇)
‘Typ’p₇     = W1 ‘Typ’p₆
‘Term’p₇    : Typ (εp₇ ▻ ‘Context’p₇ ▻ ‘Typ’p₇)
‘Term’p₇    = W2 ‘Term’p₆
‘ε₀’p₇       : Term ‘Context’p₇
‘ε₀’p₇       = w ‘ε₀’p₆
‘_▻_’p₇     : Term (‘Context’p₇ ‘→’ ‘Typ’p₇ ‘→'’ W ‘Context’p₇)
‘_▻_’p₇     = w∀→₂ ‘_▻_’p₆
‘‘Σ'’’p₇     : Term (‘Context’p₇ ‘→’ ‘Typ’p₇ ‘→’ W1 (W1 ‘Typ’p₇) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₇) ‘→'’ W ‘Typ’p₇)
‘‘Σ'’’p₇     = w∀∀‘’→ ‘‘Σ'’’p₆
‘_‘’_’p₇     : Term (‘Context’p₇ ‘→’ ‘Typ’p₇ ‘→’ W1 (W1 ‘Typ’p₇) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₇) ‘→'’ ‘Term’p₇ ‘→'’ W ‘Typ’p₇)
‘_‘’_’p₇     = w∀∀‘’→→ ‘_‘’_’p₆
‘_‘→’_’p₇    : Term (‘Context’p₇ ‘→’ ‘Typ’p₇ ‘→’ W1 (W1 ‘Typ’p₇) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₇) ‘→'’ W ‘Typ’p₇)
‘_‘→’_’p₇    = weakenTyp-tProd-tProd-tProd-substTyp-tProd-nd-weakenTyp ‘VAR₀’

εp₈ : Context
εp₈ = εp₇
  ▻ (‘Context’p₇ ‘→’ ‘Typ’p₇ ‘→’ W ‘Typ’p₇ ‘→'’ W1 (W1 ‘Typ’p₇) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₇)) {- W -}
‘Context’p₈ : Typ εp₈
‘Context’p₈ = W ‘Context’p₇
‘Typ’p₈     : Typ (εp₈ ▻ ‘Context’p₈)
‘Typ’p₈     = W1 ‘Typ’p₇
‘Term’p₈    : Typ (εp₈ ▻ ‘Context’p₈ ▻ ‘Typ’p₈)
‘Term’p₈    = W2 ‘Term’p₇
‘ε₀’p₈       : Term ‘Context’p₈
‘ε₀’p₈       = w ‘ε₀’p₇
‘_▻_’p₈     : Term (‘Context’p₈ ‘→’ ‘Typ’p₈ ‘→'’ W ‘Context’p₈)
‘_▻_’p₈     = w∀→₂ ‘_▻_’p₇
‘‘Σ'’’p₈     : Term (‘Context’p₈ ‘→’ ‘Typ’p₈ ‘→’ W1 (W1 ‘Typ’p₈) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₈) ‘→'’ W ‘Typ’p₈)
‘‘Σ'’’p₈     = w∀∀‘’→ ‘‘Σ'’’p₇
‘_‘’_’p₈     : Term (‘Context’p₈ ‘→’ ‘Typ’p₈ ‘→’ W1 (W1 ‘Typ’p₈) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₈) ‘→'’ ‘Term’p₈ ‘→'’ W ‘Typ’p₈)
‘_‘’_’p₈     = w∀∀‘’→→ ‘_‘’_’p₇
‘_‘→’_’p₈    : Term (‘Context’p₈ ‘→’ ‘Typ’p₈ ‘→’ W1 (W1 ‘Typ’p₈) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₈) ‘→'’ W ‘Typ’p₈)
‘_‘→’_’p₈    = w∀∀‘’→ ‘_‘→’_’p₇
‘W’p₈       : Term (‘Context’p₈ ‘→’ ‘Typ’p₈ ‘→’ W ‘Typ’p₈ ‘→'’ W1 (W1 ‘Typ’p₈) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₈))
‘W’p₈       = weakenTyp-tProd-tProd-tProd-weakenTyp-substTyp-tProd-nd ‘VAR₀’

εp₉ : Context
εp₉ = εp₈
  ▻ (‘Context’p₈ ‘→’ ‘Typ’p₈ ‘→'’ W ‘Context’p₈ ‘→’ W1 ‘Typ’p₈ ‘→'’ W ‘Typ’p₈) {- context-pick-if -}
‘Context’p₉         : Typ εp₉
‘Context’p₉         = W ‘Context’p₈
‘Typ’p₉             : Typ (εp₉ ▻ ‘Context’p₉)
‘Typ’p₉             = W1 ‘Typ’p₈
‘Term’p₉            : Typ (εp₉ ▻ ‘Context’p₉ ▻ ‘Typ’p₉)
‘Term’p₉            = W2 ‘Term’p₈
‘ε₀’p₉               : Term ‘Context’p₉
‘ε₀’p₉               = w ‘ε₀’p₈
‘_▻_’p₉             : Term (‘Context’p₉ ‘→’ ‘Typ’p₉ ‘→'’ W ‘Context’p₉)
‘_▻_’p₉             = w∀→₂ ‘_▻_’p₈
‘‘Σ'’’p₉             : Term (‘Context’p₉ ‘→’ ‘Typ’p₉ ‘→’ W1 (W1 ‘Typ’p₉) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₉) ‘→'’ W ‘Typ’p₉)
‘‘Σ'’’p₉             = w∀∀‘’→ ‘‘Σ'’’p₈
‘_‘’_’p₉             : Term (‘Context’p₉ ‘→’ ‘Typ’p₉ ‘→’ W1 (W1 ‘Typ’p₉) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₉) ‘→'’ ‘Term’p₉ ‘→'’ W ‘Typ’p₉)
‘_‘’_’p₉             = w∀∀‘’→→ ‘_‘’_’p₈
‘_‘→’_’p₉            : Term (‘Context’p₉ ‘→’ ‘Typ’p₉ ‘→’ W1 (W1 ‘Typ’p₉) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₉) ‘→'’ W ‘Typ’p₉)
‘_‘→’_’p₉            = w∀∀‘’→ ‘_‘→’_’p₈
‘W’p₉               : Term (‘Context’p₉ ‘→’ ‘Typ’p₉ ‘→’ W ‘Typ’p₉ ‘→'’ W1 (W1 ‘Typ’p₉) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’p₉))
‘W’p₉               = w∀∀→‘’ ‘W’p₈
‘context-pick-if’p₉ : Term (‘Context’p₉ ‘→’ ‘Typ’p₉ ‘→'’ W ‘Context’p₉ ‘→’ W1 ‘Typ’p₉ ‘→'’ W ‘Typ’p₉)
‘context-pick-if’p₉ = weakenTyp-tProd-tProd-tProd-nd-weakenTyp-tProd-weakenTyp1-tProd-nd-weakenTyp ‘VAR₀’

ε : Context
ε = εp₉

‘Context’ : Typ ε
‘Context’ = ‘Context’p₉

‘Typ’ : Typ (ε ▻ ‘Context’)
‘Typ’ = ‘Typ’p₉

‘Term’ : Typ (ε ▻ ‘Context’ ▻ ‘Typ’)
‘Term’ = ‘Term’p₉

‘ε₀’ : Term ‘Context’
‘ε₀’ = ‘ε₀’p₉

‘_▻_’ : Term (‘Context’ ‘→’ ‘Typ’ ‘→'’ W ‘Context’)
‘_▻_’ = ‘_▻_’p₉

‘‘Σ'’’ : Term (‘Context’ ‘→’ ‘Typ’ ‘→’ W1 (W1 ‘Typ’) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’) ‘→'’ W ‘Typ’)
‘‘Σ'’’ = ‘‘Σ'’’p₉

‘_‘’_’ : Term (‘Context’ ‘→’ ‘Typ’ ‘→’ W1 (W1 ‘Typ’) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’) ‘→'’ ‘Term’ ‘→'’ W ‘Typ’)
‘_‘’_’ = ‘_‘’_’p₉

‘_‘→’_’ : Term (‘Context’ ‘→’ ‘Typ’ ‘→’ W1 (W1 ‘Typ’) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’) ‘→'’ W ‘Typ’)
‘_‘→’_’ = ‘_‘→’_’p₉

‘W’ : Term (‘Context’ ‘→’ ‘Typ’ ‘→’ W ‘Typ’ ‘→'’ W1 (W1 ‘Typ’) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’))
‘W’ = ‘W’p₉

‘context-pick-if’ : Term (‘Context’ ‘→’ ‘Typ’ ‘→'’ W ‘Context’ ‘→’ W1 ‘Typ’ ‘→'’ W ‘Typ’)
‘context-pick-if’ = ‘context-pick-if’p₉
