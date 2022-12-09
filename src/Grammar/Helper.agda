{-# OPTIONS --safe #-}

module Grammar.Helper where

open import Data.Nat public
open import Data.Product
open import Data.Fin public renaming (zero to fz; suc to fs; _<_ to _f<_; _≟_ to _≟f_) using (Fin; punchIn; punchOut; #_; lift; _↑ʳ_)
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.Unit
open import Data.Bool using (true; false)
open import Level renaming (zero to lzero; suc to lsuc) hiding (lift)


open import Grammar public


private variable
  ℓ ℓ′ : Level
  P Q R : Set ℓ
  n m k : ℕ
  i j : Fin n

over : (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
over = lift 1

movTerm : Term n → (Fin n → Fin m) → Term m
movForm : Form n → (Fin n → Fin m) → Form m

movTerm ∅     f = ∅
movTerm (⋃ t) f = ⋃ (movTerm t f)
movTerm (𝒫 t) f = 𝒫 (movTerm t f)
movTerm ⟨ t , s ⟩ f = ⟨ movTerm t f , movTerm s f ⟩
movTerm ⟨ t ∣ ϕ ⟩ f = ⟨ movTerm t f ∣ movForm ϕ (over f) ⟩
movTerm (ϕ $[ t ]) f = movForm ϕ (over (over f)) $[ movTerm t f ]
movTerm Ω     f = Ω
movTerm (𝕧 i) f = 𝕧 (f i)

movForm ⊥′       f = ⊥′
movForm (r ＝ s) f = (movTerm r f) ＝ (movTerm s f)
movForm (r ∈ s)  f = (movTerm r f) ∈ (movTerm s f)
movForm (~ ϕ)    f = ~ (movForm ϕ f)
movForm (ϕ ∧ ψ)  f = (movForm ϕ f) ∧ (movForm ψ f)
movForm (ϕ ∨ ψ)  f = (movForm ϕ f) ∨ (movForm ψ f)
movForm (ϕ ⇒ ψ)  f = (movForm ϕ f) ⇒ (movForm ψ f)
movForm (∀f ϕ)   f = ∀f (movForm ϕ (over f))
movForm (∃f ϕ)   f = ∃f (movForm ϕ (over f))

movCxt : Cxt n k → (Fin n → Fin m) → Cxt m k
movCxt ∅       f = ∅
movCxt (Γ ◂ ϕ) f = (movCxt Γ f) ◂ (movForm ϕ f)

punchInTerm : Term n → Fin (suc n) → Term (suc n)
punchInTerm t i = movTerm t (punchIn i)

punchInForm : Form n → Fin (suc n) → Form (suc n)
punchInForm ϕ i = movForm ϕ (punchIn i)

punchInCxt : Cxt n k → Fin (suc n) → Cxt (suc n) k
punchInCxt Γ i = movCxt Γ (punchIn i)

liftTerm : ∀ {n} {m} → Term n → Term (m + n)
liftTerm {m = m} t = movTerm t (m ↑ʳ_)

liftForm : ∀ {n} {m} → Form n → Form (m + n)
liftForm {m = m} t = movForm t (m ↑ʳ_)

bumpTerm : Term n → Term (suc n)
bumpTerm t = punchInTerm t fz

syntax liftTerm t = ↑ t
infix 20 liftTerm

bumpForm : Form n → Form (suc n)
bumpForm ϕ = punchInForm ϕ fz

bumpCxt : Cxt n m → Cxt (suc n) m
bumpCxt Γ = punchInCxt Γ fz

subsTerm : Term (suc n) → Fin (suc n) → Term n → Term n
subsForm : Form (suc n) → Fin (suc n) → Term n → Form n

subsTerm ∅     i s = ∅
subsTerm (⋃ t) i s = ⋃ (subsTerm t i s)
subsTerm ⟨ t , s ⟩ i r = ⟨ subsTerm t i r , subsTerm s i r ⟩
subsTerm ⟨ t ∣ ϕ ⟩ i s = ⟨ subsTerm t i s ∣ subsForm ϕ (fs i) (bumpTerm s) ⟩
subsTerm (ϕ $[ t ]) i s = subsForm ϕ (fs (fs i)) (liftTerm s) $[ subsTerm t i s ]
subsTerm (𝒫 t) i s = 𝒫 (subsTerm t i s)
subsTerm Ω     i s = Ω
subsTerm (𝕧 j) i s with i ≟f j
... | yes i≡j = s
... | no ¬i≡j = 𝕧 (punchOut ¬i≡j)

subsForm ⊥′       i t = ⊥′
subsForm (r ＝ s) i t = (subsTerm r i t) ＝ (subsTerm s i t)
subsForm (r ∈ s)  i t = (subsTerm r i t) ∈ (subsTerm s i t)
subsForm (~ ϕ)    i t = ~ subsForm ϕ i t
subsForm (ϕ ∧ ψ)  i t = subsForm ϕ i t ∧ subsForm ψ i t
subsForm (ϕ ∨ ψ)  i t = subsForm ϕ i t ∨ subsForm ψ i t
subsForm (ϕ ⇒ ψ)  i t = subsForm ϕ i t ⇒ subsForm ψ i t
subsForm (∀f ϕ)   i t = ∀f (subsForm ϕ (fs i) (bumpTerm t))
subsForm (∃f ϕ)   i t = ∃f (subsForm ϕ (fs i) (bumpTerm t))

subsCxt : Cxt (suc n) m → Fin (suc n) → Term n → Cxt n m
subsCxt ∅       i t = ∅
subsCxt (Γ ◂ ϕ) i t = subsCxt Γ i t ◂ subsForm ϕ i t

syntax subsForm ϕ i t = ϕ [ i := t ]

lookupCxt : Fin m → Cxt n m → Form n
lookupCxt fz     (Γ ◂ ϕ) = ϕ
lookupCxt (fs i) (Γ ◂ ϕ) = lookupCxt i Γ

insertCxt : Fin (suc m) → Cxt n m → Form n → Cxt n (suc m)
insertCxt fz     Γ       ϕ = Γ ◂ ϕ
insertCxt (fs i) (Γ ◂ ψ) ϕ = insertCxt i Γ ϕ ◂ ψ

genSentence : Sentence → Form n
genSentence ϕ = movForm ϕ λ ()
