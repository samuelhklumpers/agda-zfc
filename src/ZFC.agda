module ZFC where

open import Data.Nat
open import Data.Product
open import Data.Fin renaming (zero to fz; suc to fs; _<_ to _f<_; _≟_ to _≟f_)
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
infix 2 _,_⊢_
infix 2 _◂_
infix 3 ∀f_ ∃f_ ∃!_
infix 4 _∨_
infix 5 _∧_ 
infix 6 _⇒_ _⇔_
infix 7 ~_
infix 8 _＝_ _∈_ _⊂_ [_]
infix 9 _⹁_
infix 10 ⋃_ 𝒫_ 𝕧_

-- grammar
data Term : ℕ → Set
data Form : ℕ → Set

data Term where
  ∅     : Term n
  _⹁_   : Term n → Term n → Term n
  ⋃_    : (t : Term n) → Term n
  𝒫_    : (t : Term n) → Term n
  Ω     : Term n

  𝕧_    : (i : Fin n)  → Term n

[_] : Term n → Term n
[ t ] = ⋃ (t ⹁ t)

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

over : (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
over f fz     = fz
over f (fs i) = fs (f i)

movTerm : Term n → (Fin n → Fin m) → Term m
movTerm ∅     f = ∅
movTerm (⋃ t) f = ⋃ (movTerm t f)
movTerm (𝒫 t) f = 𝒫 (movTerm t f)
movTerm (t ⹁ s) f = movTerm t f ⹁ movTerm s f
movTerm Ω     f = Ω
movTerm (𝕧 i) f = 𝕧 (f i)

bumpTerm : Term n → Term (suc n)
bumpTerm t = movTerm t fs

movForm : Form n → (Fin n → Fin m) → Form m
movForm ⊥′       f = ⊥′
movForm (r ＝ s) f = (movTerm r f) ＝ (movTerm s f)
movForm (r ∈ s)  f = (movTerm r f) ∈ (movTerm s f)
movForm (~ ϕ)    f = ~ (movForm ϕ f)
movForm (ϕ ∧ ψ)  f = (movForm ϕ f) ∧ (movForm ψ f)
movForm (ϕ ∨ ψ)  f = (movForm ϕ f) ∨ (movForm ψ f)
movForm (ϕ ⇒ ψ)  f = (movForm ϕ f) ⇒ (movForm ψ f)
movForm (∀f ϕ)   f = ∀f (movForm ϕ (over f))
movForm (∃f ϕ)   f = ∃f (movForm ϕ (over f))

punchInForm : Form n → Fin (suc n) → Form (suc n)
punchInForm ϕ i = movForm ϕ (punchIn i)

∃!_ : Form (suc n) → Form n
∃! ϕ = ∃f ϕ ∧ (∀f punchInForm ϕ (# 1) ⇒ 𝕧 # 0 ＝ 𝕧 # 1)

_⇔_ : Form n → Form n → Form n
ϕ ⇔ ψ = ϕ ⇒ ψ ∧ ψ ⇒ ϕ

_⊂_ : Term n → Term n → Form n
t ⊂ s = ∀f 𝕧 # 0 ∈ bumpTerm t ⇒ 𝕧 # 0 ∈ bumpTerm s 

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

-- helpers
inTerm : Term (suc n) → Fin (suc n) → Term n → Term n
inTerm ∅     i s = ∅
inTerm (⋃ t) i s = ⋃ (inTerm t i s)
inTerm (t ⹁ s) i r = inTerm t i r ⹁ inTerm s i r
inTerm (𝒫 t) i s = 𝒫 (inTerm t i s)
inTerm Ω     i s = Ω
inTerm (𝕧 j) i s with i ≟f j
... | yes i≡j = s
... | no ¬i≡j = 𝕧 (punchOut ¬i≡j)

bumpForm : Form n → Form (suc n)
bumpForm ϕ = movForm ϕ fs

inForm : Form (suc n) → Fin (suc n) → Term n → Form n
inForm ⊥′       i t = ⊥′
inForm (r ＝ s) i t = (inTerm r i t) ＝ (inTerm s i t)
inForm (r ∈ s)  i t = (inTerm r i t) ∈ (inTerm s i t)
inForm (~ ϕ)    i t = ~ inForm ϕ i t
inForm (ϕ ∧ ψ)  i t = inForm ϕ i t ∧ inForm ψ i t
inForm (ϕ ∨ ψ)  i t = inForm ϕ i t ∨ inForm ψ i t
inForm (ϕ ⇒ ψ)  i t = inForm ϕ i t ⇒ inForm ψ i t
inForm (∀f ϕ)   i t = ∀f (inForm ϕ (fs i) (bumpTerm t))
inForm (∃f ϕ)   i t = ∃f (inForm ϕ (fs i) (bumpTerm t))

syntax inForm ϕ i t = ϕ [ i := t ]

lookup : Fin m → Cxt n m → Form n
lookup fz     (Γ ◂ ϕ) = ϕ
lookup (fs i) (Γ ◂ ϕ) = lookup i Γ

movCxt : Cxt n k → (Fin n → Fin m) → Cxt m k
movCxt ∅       f = ∅
movCxt (Γ ◂ ϕ) f = (movCxt Γ f) ◂ (movForm ϕ f)

punchInTerm : Term n → Fin (suc n) → Term (suc n)
punchInTerm t i = movTerm t (punchIn i)

punchInCxt : Cxt n k → Fin (suc n) → Cxt (suc n) k
punchInCxt Γ i = movCxt Γ (punchIn i)

bumpCxt : Cxt n m → Cxt (suc n) m
bumpCxt Γ = movCxt Γ fs

inCxt : Cxt (suc n) m → Fin (suc n) → Term n → Cxt n m
inCxt ∅       i t = ∅
inCxt (Γ ◂ ϕ) i t = inCxt Γ i t ◂ inForm ϕ i t

insCxt : Fin (suc m) → Cxt n m → Form n → Cxt n (suc m)
insCxt fz     Γ       ϕ = Γ ◂ ϕ
insCxt (fs i) (Γ ◂ ψ) ϕ = insCxt i Γ ϕ ◂ ψ

-- entailment
-- follows the book ``Sets, Models and Proofs'' to an extent
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
  subs : n , Γ ⊢ t ＝ s
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
  pair : n , Γ ⊢ ∀f ∀f ∀f 𝕧 (# 0) ∈ (𝕧 (# 2) ⹁ 𝕧 (# 1)) ⇔ (𝕧 (# 0) ＝ 𝕧 (# 2) ∨ 𝕧 (# 0) ＝ 𝕧 (# 1))

  -- separation
  sep : ∀ ϕ → n , Γ ⊢ ∀f ∃f ∀f 𝕧 (# 0) ∈ 𝕧 (# 1) ⇔ (𝕧 (# 0) ∈ 𝕧 (# 2) ∧ punchInForm ϕ (# 1))

  -- union
  uni : n , Γ ⊢ ∀f ∀f 𝕧 (# 0) ∈ ⋃ (𝕧 (# 1)) ⇔ (∃f 𝕧 (# 0) ∈ 𝕧 (# 2) ∧ 𝕧 (# 1) ∈ 𝕧 (# 0))

  -- power
  pow : n , Γ ⊢ ∀f ∀f 𝕧 (# 0) ∈ 𝒫 (𝕧 (# 1)) ⇔ 𝕧 # 0 ⊂ 𝕧 # 1

  -- infinity
  inf : n , Γ ⊢ ∅ ∈ Ω ∧ (∀f 𝕧 # 0 ∈ Ω ∧ ⋃ (𝕧 # 0 ⹁ [ 𝕧 # 0 ]) ∈ Ω) 

  -- replacement
  rep : ∀ ϕ → n , Γ ⊢ (∀f ∃f ∀f (ϕ ⇔ 𝕧 # 0 ＝ 𝕧 # 1)) ⇒ (∀f ∃f ∀f 𝕧 # 0 ∈ 𝕧 # 2 ⇒ (∃f 𝕧 # 0 ∈ 𝕧 # 2 ∧ punchInForm ϕ (# 2)))

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

  sub : (suc n) , Γ ⊢ ϕ
      → ∀ i t
      -----------
      → n , inCxt Γ i t ⊢ inForm ϕ i t 

  h1l : n , inCxt (bumpCxt Γ) (# 0) t ⊢ ϕ → n , Γ ⊢ ϕ
  h1r : n , Γ ⊢ ϕ → n , inCxt (bumpCxt Γ) (# 0) t ⊢ ϕ
 
  --h2l : n , Γ ⊢ punchInForm ϕ i [ i := t ] → n , Γ ⊢ ϕ
  --h2r : n , Γ ⊢ ϕ → n , Γ ⊢ punchInForm ϕ i [ i := t ]

-- the theory is all done!

-- proofs
ass : {p : Γ ▷ ϕ} → n , Γ ⊢ ϕ
ass {p = p} = 𝕧-i p -- make this play nice

-- NB: stating n , Γ ⊢ ∃f ϕ ↔ Σ[ t ∈ Term n ] (n , Γ ⊢ ϕ [ # 0 := t ]) is the same as stating that every term is constructable
-- which is generally not true

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

dne : n , Γ ⊢ ~ ~ ϕ ⇒ ϕ
dne {ϕ = ϕ} = ⇒-i (∨-e (lem ϕ) (𝕧-i ▷z) (⊥-e (~-e′ (𝕧-i (▷s ▷z)) (𝕧-i ▷z))))

-- weaker formulations
∀-e-weak : n , Γ ⊢ ∀f ϕ → ∀ t → n , Γ ⊢ ϕ [ # 0 := t ]
∀-e-weak p t = h1l (sub (∀-e p) (# 0) t)
