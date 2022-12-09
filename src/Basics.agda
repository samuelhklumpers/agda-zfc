{-# OPTIONS --safe #-}

module Basics where

open import Data.Maybe
open import Data.Fin.Properties
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import ZFC
open import Showing

private variable
  P Q : Set
  n m : ℕ
  i j : Fin n
  ϕ ψ : Form n
  Γ Δ : Cxt n m
  t s : Term n

-- alternative formulations
∃-e′ : n , Γ ⊢ ∃f ϕ → n , Γ ⊢ ∀f (ϕ ⇒ bumpForm ψ) → n , Γ ⊢ ψ
∃-e′ {ϕ = ϕ} p q =
  ∃-e
    p
    (⇒-e
      ϕ
      (weak (Cxt⊂-right Cxt⊂-refl) (∀-e q))
      (𝕧-i ▷z))

⇒-e′ : n , Γ ⊢ ϕ ⇒ ψ → n , Γ ⊢ ϕ → n , Γ ⊢ ψ
⇒-e′ = ⇒-e _

~-e′ : n , Γ ⊢ ~ ϕ → n , Γ ⊢ ϕ → n , Γ ⊢ ⊥′
~-e′ = ~-e _

-- weaker formulation
∀-ew : n , Γ ⊢ ∀f ϕ → ∀ t → n , Γ ⊢ ϕ [ # 0 := t ]
∀-ew p t = h1l (subv (∀-e p) (# 0) t)

-- preliminaries
dne : n , Γ ⊢ ~ ~ ϕ ⇒ ϕ
dne {ϕ = ϕ} = ⇒-i (∨-e (lem ϕ) (𝕧-i ▷z) (⊥-e (~-e′ (𝕧-i (▷s ▷z)) (𝕧-i ▷z))))

case : ∀ ϕ {ψ} → n , Γ ◂ ϕ ⊢ ψ → n , Γ ◂ ~ ϕ ⊢ ψ → n , Γ ⊢ ψ
case ϕ p q = ∨-e (lem ϕ) p q

⇒-refl : n , Γ ⊢ ϕ ⇒ ϕ
⇒-refl = ⇒-i (𝕧-i ▷z)

＝-refl : n , Γ ⊢ ∀f (𝕧 # 0 ＝ 𝕧 # 0)
＝-refl = ∀-i (⇒-e′ (∀-ew (∀-ew ext _) _) (∀-i (∧-i
  ⇒-refl
  ⇒-refl
  )))

＝-sym : n , Γ ⊢ ∀f ∀f (𝕧 # 1 ＝ 𝕧 # 0 ⇒ 𝕧 # 0 ＝ 𝕧 # 1)
＝-sym = ∀-i (∀-i (⇒-i (subs (𝕧 # 2 ＝ 𝕧 # 1) (# 2) (𝕧-i ▷z) (∀-ew ＝-refl (𝕧 # 1)))))

＝-trans : n , Γ ⊢ ∀f ∀f ∀f 𝕧 # 2 ＝ 𝕧 # 1 ⇒ 𝕧 # 1 ＝ 𝕧 # 0 ⇒ 𝕧 # 2 ＝ 𝕧 # 0
＝-trans = ∀-i (∀-i (∀-i (⇒-i (⇒-i (subs (𝕧 (# 3) ＝ 𝕧 (# 1)) (# 1) (𝕧-i ▷z) (𝕧-i (▷s ▷z)))))))

x∈[x] : n , Γ ⊢ ∀f 𝕧 # 0 ∈ [ 𝕧 # 0 ]
x∈[x] = ∀-i (⇒-e′ (∧-el (∀-ew (∀-ew (∀-ew pair (𝕧 fz)) (𝕧 fz)) (𝕧 (# 0)))) (∨-il (∀-ew ＝-refl (𝕧 # 0))))

x∈[x]! : n , Γ ⊢ ∀f ∀f 𝕧 # 0 ∈ [ 𝕧 # 1 ] ⇒ 𝕧 # 0 ＝ 𝕧 # 1
x∈[x]! = ∀-i (∀-i (⇒-i (∨-e (⇒-e′ (∧-er (∀-ew (∀-ew (∀-ew pair (𝕧 # 1)) (𝕧 # 1)) (𝕧 # 0))) (𝕧-i ▷z)) (𝕧-i ▷z) (𝕧-i ▷z))))

x∉x : n , Γ ⊢ ∀f ~ 𝕧 # 0 ∈ 𝕧 # 0
x∉x = ∀-i (~-i (∃-e′ (⇒-e′ (∀-ew reg [ 𝕧 # 0 ]) (∃-i (𝕧 # 0) (∀-ew x∈[x] (𝕧 # 0)))) (∀-i (⇒-i (~-e′ (∧-er (𝕧-i ▷z)) (∃-i (𝕧 # 1)
  (∧-i (subs (𝕧 (# 1) ∈ 𝕧 (# 2)) (# 2) (⇒-e′ (∀-ew (∀-ew ＝-sym _) _) (⇒-e′ (∀-ew (∀-ew x∈[x]! _) _) (∧-el (𝕧-i ▷z)))) (𝕧-i (▷s ▷z))) (∀-ew x∈[x] (𝕧 # 1)))))))))

⟨x∣⊥⟩-empty : n , Γ ⊢ ∀f ∀f ~ 𝕧 # 0 ∈ ⟨ 𝕧 # 1 ∣ ⊥′ ⟩
⟨x∣⊥⟩-empty = ∀-i (∀-i (~-i (∧-er (⇒-e′ (∧-er (∀-ew (sep ⊥′ (𝕧 # 1)) (𝕧 (# 0)))) (𝕧-i ▷z)))))

_×_ : (x y : Term n) → Term n
x × y = ⟨ 𝒫 𝒫 (x ∪ y) ∣ ∃f (∃f 𝕧 (# 0) ∈ liftTerm x ∧ (𝕧 (# 1) ∈ liftTerm y ∧ 𝕧 (# 2) ＝ [ 𝕧 # 0 , 𝕧 # 1 ])) ⟩ 

∀[∈_]_ : Term n → Form (1 + n) → Form n
∀[∈ t ] ϕ = ∀f 𝕧 # 0 ∈ (bumpTerm t) ⇒ ϕ

∃[∈_]_ : Term n → Form (1 + n) → Form n
∃[∈ t ] ϕ = ∃f 𝕧 # 0 ∈ (bumpTerm t) ∧ ϕ

infix 4 ∀[∈_]_ ∃[∈_]_

Rel : (x y r : Term n) → Form n
Rel x y r = r ⊂ (x × y)

Fun : (x y r : Term n) → Form n
Fun x y r = Rel x y r ∧ (∀[∈ x ] ∃[∈ ↑ y ] (∀[∈ ↑ y ] [ 𝕧 # 2 , 𝕧 # 0 ] ∈ ↑ r ⇒ 𝕧 # 0 ＝ 𝕧 # 1))

_⟶_ : Term n → Term n → Term n
x ⟶ y = ⟨ 𝒫 (x × y) ∣ Fun (↑ x) (↑ y) (𝕧 # 0) ⟩

{-
-- SMP 130
tuple-＝ : ⊢″ ∀f ∀f ∀f ∀f [ 𝕧 # 0 , 𝕧 # 1 ] ＝ [ 𝕧 # 2 , 𝕧 # 3 ] ⇔ (𝕧 # 0 ＝ 𝕧 # 2 ∧ 𝕧 # 1 ＝ 𝕧 # 3)
tuple-＝ = ∀-i (∀-i (∀-i (∀-i (∧-i
  (⇒-i (∧-i
    {!!} -- first need well-foundedness, and is actually fairly tricky
    {!!}))
  (⇒-i (⇒-e′ (∀-ew (∀-ew ext [ 𝕧 # 2 , 𝕧 # 3 ]) [ 𝕧 # 0 , 𝕧 # 1 ]) (∀-i (∧-i
    (⇒-i (subs (𝕧 (# 0) ∈ [ 𝕧 (# 1) , 𝕧 (# 5) ]) (# 1) (∧-el (𝕧-i (▷s ▷z)))
         (subs (𝕧 (# 0) ∈ [ 𝕧 (# 1) , 𝕧 (# 2) ]) (# 2) (∧-er (𝕧-i (▷s ▷z)))
         (𝕧-i ▷z))))
    (⇒-i (subs (𝕧 (# 0) ∈ [ 𝕧 (# 1) , 𝕧 (# 3) ]) (# 1) (⇒-e′ (∀-ew (∀-ew ＝-sym _) _) (∧-el (𝕧-i (▷s ▷z))))
         (subs (𝕧 (# 0) ∈ [ 𝕧 (# 4) , 𝕧 (# 2) ]) (# 2) (⇒-e′ (∀-ew (∀-ew ＝-sym _) _) (∧-er (𝕧-i (▷s ▷z)))) (𝕧-i ▷z))))
    ))))
  ))))
-}
