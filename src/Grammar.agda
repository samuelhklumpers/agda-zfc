{-# OPTIONS --safe #-}

module Grammar where

open import Data.Nat public
open import Data.Product
open import Data.Fin public renaming (zero to fz; suc to fs; _<_ to _f<_; _≟_ to _≟f_) using (Fin; punchIn; punchOut; #_)
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.Unit
open import Data.Bool using (true; false)
open import Level renaming (zero to lzero; suc to lsuc)

private variable
  ℓ ℓ′ : Level
  P Q R : Set ℓ
  n m k : ℕ
  i j : Fin n

-- symbols
infix 1 _▷_
infix 1 _Cxt⊂_
infixl 2 _◂_
infix 3 ∀f_ ∃f_
infixl 4 _∨_
infixl 5 _∧_ 
infixr 6 _⇒_
infix 7 ~_
infix 8 _＝_ _∈_
infix 9 ⟨_,_⟩
infix 10 ⋃_ 𝒫_ 𝕧_

-- grammar
data Term : ℕ → Set
data Form : ℕ → Set

data Term where
  ∅     : Term n                          -- emptyset
  ⟨_,_⟩ : Term n → Term n → Term n        -- pair
  ⟨_∣_⟩ : Term n → Form (1 + n) → Term n  -- comprehension/separation
  _$[_] : Form (2 + n) → Term n → Term n  -- replacement
  ⋃_    : (t : Term n) → Term n           -- union
  𝒫_    : (t : Term n) → Term n           -- powerset
  Ω     : Term n                          -- infinity

  𝕧_    : (i : Fin n)  → Term n           -- variable

private variable
  t s : Term n

data Form where
  ⊥′   : Form n
  _＝_ : (r : Term n) → (s : Term n) → Form n
  _∈_  : (r : Term n) → (s : Term n) → Form n
  ~_   : (ϕ : Form n) → Form n
  _∧_  : (ϕ : Form n) → (ψ : Form n) → Form n
  _∨_  : (ϕ : Form n) → (ψ : Form n) → Form n
  _⇒_  : (ϕ : Form n) → (ψ : Form n) → Form n
  ∀f_  : (ϕ : Form (suc n)) → Form n
  ∃f_  : (ϕ : Form (suc n)) → Form n

private variable
  ϕ ψ χ : Form n

Sentence = Form 0

data Cxt : ℕ → ℕ → Set where
  ∅   : Cxt n 0
  _◂_ : Cxt n m → Form n → Cxt n (suc m)

private variable
  Γ Δ : Cxt n m

data _▷_ : Cxt n m → Form n → Set where
  ▷z : Γ ◂ ϕ ▷ ϕ
  ▷s : Γ ▷ ϕ → Γ ◂ ψ ▷ ϕ

data _Cxt⊂_ : Cxt n m → Cxt n k → Set where
  Cxt⊂-refl  : Γ Cxt⊂ Γ
  Cxt⊂-right : Γ Cxt⊂ Δ → Γ Cxt⊂ Δ ◂ ϕ
  Cxt⊂-both  : Γ Cxt⊂ Δ → Γ ◂ ϕ Cxt⊂ Δ ◂ ϕ
