{-# OPTIONS --safe #-}

module ZFC where

open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.Unit
open import Data.Bool using (true; false)
open import Level renaming (zero to lzero; suc to lsuc)


open import Notation public


private variable
  ℓ ℓ′ : Level
  P Q R : Set ℓ
  n m k : ℕ
  i j : Fin n

  r s t : Term n
  ϕ ψ χ : Form n
  Γ Δ : Cxt n m


-- entailment
-- follows the book ``Sets, Models and Proofs'' to an extent
infix 2 _,_⊢_ ⊢′ ⊢″_

data _,_⊢_ : (n : ℕ) {m : ℕ} → Cxt n m → Form n → Set where
  -- assumption
  𝕧-i : Γ ▷ ϕ
      -----------
      → n , Γ ⊢ ϕ

  -- conjunction
  ∧-i  : n , Γ ⊢ ϕ
       → n , Γ ⊢ ψ
      ----------------
       → n , Γ ⊢ ϕ ∧ ψ
       
  ∧-el : n , Γ ⊢ ϕ ∧ ψ
       ---------------
       → n , Γ ⊢ ϕ
       
  ∧-er : n , Γ ⊢ ϕ ∧ ψ
       ---------------
       → n , Γ ⊢ ψ

  ∧-eb : n , Γ ⊢ ϕ ∧ ψ
       → n , Γ ◂ ϕ ◂ ψ ⊢ χ
       -------------------
       → n , Γ ⊢ χ

  -- disjunction
  ∨-il : n , Γ ⊢ ϕ
       ---------------
       → n , Γ ⊢ ϕ ∨ ψ
       
  ∨-ir : n , Γ ⊢ ψ
       ---------------
       → n , Γ ⊢ ϕ ∨ ψ
       
  ∨-e  : n , Γ     ⊢ ϕ ∨ ψ
       → n , Γ ◂ ϕ ⊢ χ
       → n , Γ ◂ ψ ⊢ χ
       -------------------
       → n , Γ ⊢ χ

  -- implication
  ⇒-i : n , Γ ◂ ϕ ⊢ ψ
      ---------------
      → n , Γ ⊢ ϕ ⇒ ψ 

  ⇒-e : ∀ ϕ
      → n , Γ ⊢ ϕ ⇒ ψ
      → n , Γ ⊢ ϕ
      ---------------
      → n , Γ ⊢ ψ

  -- negation
  ~-i : n , Γ ◂ ϕ ⊢ ⊥′
      ----------------
      → n , Γ ⊢ ~ ϕ
      
  ~-e : ∀ ϕ
      → n , Γ ⊢ ~ ϕ
      → n , Γ ⊢ ϕ
      -------------
      → n , Γ ⊢ ⊥′

  -- absurdum
  ⊥-e : n , Γ ⊢ ⊥′
      ------------
      → n , Γ ⊢ ϕ

  -- substitution  
  subs : ∀ ϕ i
       → n , Γ ⊢ t ＝ s
       → n , Γ ⊢ ϕ [ i := t ]
       ----------------------
       → n , Γ ⊢ ϕ [ i := s ]

  -- universal quantification:
  -- In Γ in a proof of bumpCxt Γ ⊢ ϕ, no formula in Γ can reference the fresh variable
  -- hence the variable is free, and the quantification is valid.
  -- Note that we do not use punchInCxt, because then we would have to make ∀f an actual Fin binder
  ∀-i : (suc n) , bumpCxt Γ ⊢ ϕ
      -------------------------
      → n , Γ ⊢ ∀f ϕ
      
  ∀-e : --∀ t →
      n , Γ ⊢ ∀f ϕ
      ------------------------
      → (suc n) , bumpCxt Γ ⊢ ϕ 
      -- → n , Γ ⊢ ϕ [ # 0 := t ]
  -- NB: we use this wrap/unwrap description, so we can instantiate universal quantifiers to undefinable terms
  -- outdated remark: -- NB! this states ∀f ϕ ⇒ ∃f ϕ, and this is precisely true when t exists, and our domain is non-empty!

  -- existential quantification:
  -- In contrast to universal quantification, we require that there actually is a term validating ϕ,
  -- which may be referenced in Γ
  ∃-i : ∀ t
      → n , Γ ⊢ ϕ [ # 0 := t ]
      ------------------------
      → n , Γ ⊢ ∃f ϕ
      
  ∃-e : n , Γ ⊢ ∃f ϕ
      → (suc n) , bumpCxt Γ ◂ ϕ ⊢ bumpForm ψ
      --------------------------------------
      → n , Γ ⊢ ψ

  lem : ∀ ϕ
      -----------------
      → n , Γ ⊢ ϕ ∨ ~ ϕ

  -- zfc
  -- extensionality: ∀ x y . (∀ z . z ∈ y ⇔ z ∈ x) ⇒ y ＝ x 
  ext : n , Γ ⊢ ∀f ∀f (∀f 𝕧 (# 0) ∈ 𝕧 (# 1) ⇔ 𝕧 (# 0) ∈ 𝕧 (# 2)) ⇒ 𝕧 (# 0) ＝ 𝕧 (# 1)

  -- empty set
  emp : n , Γ ⊢ ∀f ~ 𝕧 (# 0) ∈ ∅ 

  -- pairing
  pair : n , Γ ⊢ ∀f ∀f ∀f 𝕧 (# 0) ∈ ⟨ 𝕧 (# 2) , 𝕧 (# 1) ⟩ ⇔ (𝕧 (# 0) ＝ 𝕧 (# 2) ∨ 𝕧 (# 0) ＝ 𝕧 (# 1))

  -- separation
  sep : ∀ ϕ t → n , Γ ⊢ ∀f 𝕧 (# 0) ∈ bumpTerm ⟨ t ∣ ϕ ⟩ ⇔ (𝕧 (# 0) ∈ bumpTerm t ∧ ϕ)
  sep' : ∀ ϕ → n , Γ ⊢ ∀f ∀f 𝕧 (# 0) ∈ ⟨ 𝕧 # 1 ∣ punchInForm (punchInForm ϕ (# 1)) (# 1) ⟩ ⇔ (𝕧 # 0 ∈ 𝕧 # 1 ∧ punchInForm ϕ (# 1))
  --sep : ∀ (ϕ : Form (2 + n)) → n , Γ ⊢ ∀f ∃f ∀f 𝕧 (# 0) ∈ 𝕧 (# 1) ⇔ (𝕧 (# 0) ∈ 𝕧 (# 2) ∧ punchInForm ϕ (# 1))

  -- union
  uni : n , Γ ⊢ ∀f ∀f 𝕧 (# 0) ∈ ⋃ (𝕧 (# 1)) ⇔ (∃f 𝕧 (# 0) ∈ 𝕧 (# 2) ∧ 𝕧 (# 1) ∈ 𝕧 (# 0))

  -- power
  pow : n , Γ ⊢ ∀f ∀f 𝕧 (# 0) ∈ 𝒫 (𝕧 (# 1)) ⇔ 𝕧 # 0 ⊂ 𝕧 # 1

  -- infinity
  inf : n , Γ ⊢ ∅ ∈ Ω ∧ (∀f 𝕧 # 0 ∈ Ω ∧ 𝕧 # 0 ∪ [ 𝕧 # 0 ] ∈ Ω) 

  -- replacement
  rep : ∀ ϕ t → n , Γ ⊢ (∀f ∃f ∀f (punchInForm ϕ (# 1) ⇔ 𝕧 # 0 ＝ 𝕧 # 1)) ⇒ (∀f 𝕧 # 0 ∈ bumpTerm (ϕ $[ t ]) ⇔ (∃f (𝕧 # 0 ∈ liftTerm t ∧ ϕ)))
  rep' : ∀ ϕ → n , Γ ⊢ (∀f ∃f ∀f (punchInForm ϕ (# 1) ⇔ 𝕧 # 0 ＝ 𝕧 # 1)) ⇒ (∀f ∀f 𝕧 # 0 ∈ (punchInForm (punchInForm ϕ (# 2)) (# 2)) $[ 𝕧 # 1 ] ⇔ (∃f (𝕧 # 0 ∈ 𝕧 # 1 ∧ punchInForm ϕ (# 2))))
  --rep : ∀ ϕ → n , Γ ⊢ (∀f ∃f ∀f (ϕ ⇔ 𝕧 # 0 ＝ 𝕧 # 1)) ⇒ (∀f ∃f ∀f 𝕧 # 0 ∈ 𝕧 # 2 ⇒ (∃f 𝕧 # 0 ∈ 𝕧 # 2 ∧ punchInForm ϕ (# 2)))

  -- regularity
  reg : n , Γ ⊢ ∀f (∃f 𝕧 # 0 ∈ 𝕧 # 1) ⇒ (∃f 𝕧 # 0 ∈ 𝕧 # 1 ∧ ~ (∃f 𝕧 # 0 ∈ 𝕧 # 1 ∧ 𝕧 # 0 ∈ 𝕧 # 2))  

  -- choice
  ac : n , Γ ⊢ ∀f (∀f ∀f ~ (∃f 𝕧 # 0 ∈ 𝕧 # 1 ∧ 𝕧 # 0 ∈ 𝕧 # 2)) ⇒ (∃f ∀f (𝕧 # 0 ∈ 𝕧 # 1) ⇒ (∃! 𝕧 # 0 ∈ 𝕧 # 1 ∧ 𝕧 # 0 ∈ 𝕧 # 2)) 

  -- admissible rules
  -- weakening: if we can prove something assuming Γ, then we can also prove it assuming more
  weak : Γ Cxt⊂ Δ
       → n , Γ ⊢ ϕ
       -----------
       → n , Δ ⊢ ϕ

  subv : (suc n) , Γ ⊢ ϕ
       → ∀ i t
       -----------
       → n , subsCxt Γ i t ⊢ subsForm ϕ i t

  --punch : ∀ i → (suc n) , punchInCxt Γ i ⊢ punchInForm ϕ i → n , Γ ⊢ ϕ

  h1l : n , subsCxt (bumpCxt Γ) (# 0) t ⊢ ϕ → n , Γ ⊢ ϕ
  h1r : n , Γ ⊢ ϕ → n , subsCxt (bumpCxt Γ) (# 0) t ⊢ ϕ

  --h2l : ∀ ϕ → n , Γ ⊢ ϕ [ # 0 := inTerm (bumpTerm t) (# 0) s ] → n , Γ ⊢ ϕ [ # 0 := t ]
  --h2r : ∀ ϕ → n , Γ ⊢ ϕ [ # 0 := t ] → n , Γ ⊢ ϕ [ # 0 := inTerm (bumpTerm t) (# 0) s ]

  --h2l : n , Γ ⊢ punchInForm ϕ i [ i := t ] → n , Γ ⊢ ϕ
  --h2r : n , Γ ⊢ ϕ → n , Γ ⊢ punchInForm ϕ i [ i := t ]

⊢′ : Form 0 → Cxt 0 m → Set
⊢′ ϕ Γ = 0 , Γ ⊢ ϕ

syntax ⊢′ ϕ Γ = Γ ⊢′ ϕ

⊢″_ : Form 0 → Set
⊢″ ϕ = 0 , ∅ ⊢ ϕ

-- the theory is all done!
