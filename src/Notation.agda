{-# OPTIONS --safe #-}

module Notation where

open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.Unit
open import Data.Bool using (true; false)
open import Level renaming (zero to lzero; suc to lsuc)


open import Grammar.Helper public

infix 3 ∃!_
infix 6 _⇔_
infix 8 _⊂_
infix 9 [_,_] [_] _∪_


private variable
  ℓ ℓ′ : Level
  P Q R : Set ℓ
  n m k : ℕ
  i j : Fin n

  r s t : Term n
  ϕ ψ χ : Form n
  Γ Δ : Cxt n m


_∪_ : Term n → Term n → Term n
t ∪ s = ⋃ ⟨ t , s ⟩

[_] : Term n → Term n
[ t ] = ⟨ t , t ⟩

[_,_] : Term n → Term n → Term n
[ t , s ] = ⟨ t , ⟨ t , s ⟩ ⟩

∃!_ : Form (suc n) → Form n
∃! ϕ = ∃f ϕ ∧ (∀f punchInForm ϕ (# 1) ⇒ 𝕧 # 0 ＝ 𝕧 # 1)

_⇔_ : Form n → Form n → Form n
ϕ ⇔ ψ = ψ ⇒ ϕ ∧ ϕ ⇒ ψ -- with this direction, we have that ∧-er takes ϕ ⇔ ψ to ϕ ⇒ ψ

_⊂_ : Term n → Term n → Form n
t ⊂ s = ∀f 𝕧 # 0 ∈ bumpTerm t ⇒ 𝕧 # 0 ∈ bumpTerm s 
