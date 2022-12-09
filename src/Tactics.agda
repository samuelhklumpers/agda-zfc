

{-
it : ∀ {a} {A : Set a} → {{A}} → A
it {{x}} = x

▷search : (Γ : Cxt n m) → (ϕ : Form n) → Maybe (Γ ▷ ϕ)
▷search Γ ϕ = {!Γ !} -- instant regret upon remembering decidable equality for formulas

ass : {{Γ ▷ ϕ}} → n , Γ ⊢ ϕ
ass = 𝕧-i it

punchIn-inTerm : ∀ i t → (r : Term n) → inTerm (punchInTerm t i) i r ≡ t
punchIn-inTerm i ∅ r = refl
punchIn-inTerm i ⟨ t , s ⟩ r = cong₂ ⟨_,_⟩ (punchIn-inTerm i t r) (punchIn-inTerm i s r)
punchIn-inTerm i (⋃ t) r = cong ⋃_ (punchIn-inTerm i t r)
punchIn-inTerm i (𝒫 t) r = cong 𝒫_ (punchIn-inTerm i t r)
punchIn-inTerm i Ω r   = refl
punchIn-inTerm i (𝕧 j) r with i ≟f punchIn i j
... | yes p = ⊥-elim (punchInᵢ≢i i j (sym p))
... | no ¬p = cong 𝕧_ (trans (punchOut-cong i {i≢k = ¬p} refl) (punchOut-punchIn i))

-- making things nice is torture
--ext′ : ∀ t s → n , Γ ⊢ (∀f 𝕧 (# 0) ∈ bumpTerm t ⇔ 𝕧 (# 0) ∈ bumpTerm s) → n , Γ ⊢ t ＝ s
--ext′ t s p rewrite punchIn-inTerm (# 0) s t = {!⇒-e′ (∀-ew (∀-ew ext s) t) ?!}
-}
