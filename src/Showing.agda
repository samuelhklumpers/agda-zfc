{-# OPTIONS --safe #-}

module Showing where

open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.Unit
open import Data.Bool using (if_then_else_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.String hiding (_<?_)
open import Data.Fin using (toℕ)
open import Data.List using (_∷_)
open import Data.Char renaming (toℕ to toℕc; fromℕ to fromℕc) hiding (_<?_)


open import ZFC


private variable
  ℓ ℓ′ : Level
  A P Q R : Set ℓ
  n m k : ℕ
  i j : Fin n

  r s t : Term n
  ϕ ψ χ : Form n
  Γ Δ : Cxt n m


record Shows (A : Set ℓ) : Set ℓ where
  field
    -- precedence, binders
    showP : ℕ → ℕ → A → String
    binders : A → ℕ

open Shows {{...}}

showb : {{Shows A}} → ℕ → A → String
showb b = showP 0 b

shows : {{Shows A}} → A → String
shows x = showP 0 (binders x) x

ord-a : ℕ
ord-a = toℕc 'a'

ifparens : ℕ → ℕ → String → String
ifparens x y s = if x <ᵇ y then parens s else s

instance
  showTerm : ∀ {n} → Shows (Term n)
  showForm : ∀ {n} → Shows (Form n)

  showP ⦃ showTerm ⦄ p b ∅         = "∅"
  showP ⦃ showTerm ⦄ p b ⟨ t , s ⟩ = "⟨ " ++ showP 0 b t ++ " , " ++ showP 0 b s ++ " ⟩" 
  showP ⦃ showTerm ⦄ p b ⟨ t ∣ ϕ ⟩ = "⟨ " ++ showP 0 b t ++ " ∣ " ++ showP 0 b ϕ ++ " ⟩"
  showP ⦃ showTerm ⦄ p b (ϕ $[ t ]) = ifparens 0 p (showP 0 b ϕ ++ " $[ " ++ showP 0 b t ++ " ]")
  showP ⦃ showTerm ⦄ p b (⋃ t)     = "⋃ " ++ showP 0 b t
  showP ⦃ showTerm ⦄ p b (𝒫 t)     = "𝒫 " ++ showP 0 b t
  showP ⦃ showTerm ⦄ p b Ω         = "Ω"
  showP ⦃ showTerm ⦄ p b (𝕧 i)     = fromChar (fromℕc ((pred b ∸ toℕ i) + ord-a))

  binders ⦃ showTerm {n = n} ⦄ t = n

  showP ⦃ showForm ⦄ p b ⊥′ = "⊥′"
  showP ⦃ showForm ⦄ p b (r ＝ s) = ifparens 10 p (showP 0 b r ++ " ＝ " ++ showP 0 b s)
  showP ⦃ showForm ⦄ p b (r ∈ s) = ifparens 10 p (showP 0 b r ++ " ∈ " ++ showP 0 b s)
  showP ⦃ showForm ⦄ p b (~ ϕ) = ifparens 4 p ("~ " ++ showP 4 b ϕ)
  showP ⦃ showForm ⦄ p b (ϕ ∧ ψ) = ifparens 2 p (showP 2 b ϕ ++ " ∧ " ++ showP 2 b ψ)
  showP ⦃ showForm ⦄ p b (ϕ ∨ ψ) = ifparens 1 p (showP 1 b ϕ ++ " ∨ " ++ showP 1 b ψ)
  showP ⦃ showForm ⦄ p b (ϕ ⇒ ψ) = ifparens 3 p (showP 3 b ϕ ++ " ⇒ " ++ showP 3 b ψ) 
  showP ⦃ showForm ⦄ p b (∀f ϕ) = ifparens 0 p ("∀" ++ fromChar (fromℕc (b + ord-a)) ++  " " ++ showP 0 (suc b) ϕ) 
  showP ⦃ showForm ⦄ p b (∃f ϕ) = ifparens 0 p ("∃" ++ fromChar (fromℕc (b + ord-a)) ++  " " ++ showP 0 (suc b) ϕ) 

  binders ⦃ showForm {n = n} ⦄ ϕ = n

instance
  showCxt : ∀ {n m} → Shows (Cxt n m)
  showP ⦃ showCxt ⦄ p b ∅       = ""
  showP ⦃ showCxt ⦄ p b (∅ ◂ x) = showP 0 b x
  showP ⦃ showCxt ⦄ p b ((Γ ◂ y) ◂ x) = showP 0 b (Γ ◂ y) ++ " , " ++ showP 0 b x 

  binders ⦃ showCxt {n = n} ⦄ Γ = n

instance
  showType : ∀ {n m ϕ} {Γ : Cxt n m} → Shows (n , Γ ⊢ ϕ)
  showP ⦃ showType {ϕ = ϕ} {Γ = Γ} ⦄ p b _ = showP 0 b Γ ++ " ⊢ " ++ showP 0 b ϕ

  binders ⦃ showType {n = n} ⦄ _ = n
