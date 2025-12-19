import Gardenpath.Complexity
import Mathlib.Data.ENNReal.Basic

/-!
# Binary Complexity Measure

A minimal instance proving the complexity axioms are consistent.

The binary complexity measure assigns:
- 0 to types with exactly one element (Unique)
- 1 to all other types

This is the simplest non-trivial complexity measure. It distinguishes only
between "trivial" and "non-trivial" types.
-/

universe u

namespace Gardenpath

open scoped ENNReal

/-- A type is "trivial" if it is Subsingleton and Nonempty (i.e., has exactly one element). -/
def IsTrivial (A : Type*) : Prop := Subsingleton A ∧ Nonempty A

noncomputable instance (A : Type*) : Decidable (IsTrivial A) := Classical.dec _

lemma isTrivial_of_unique (A : Type*) [Unique A] : IsTrivial A :=
  ⟨inferInstance, ⟨default⟩⟩

lemma isTrivial_iff_equiv {A B : Type*} (e : A ≃ B) : IsTrivial A ↔ IsTrivial B := by
  unfold IsTrivial
  constructor
  · intro ⟨hS, hN⟩
    haveI : Subsingleton A := hS
    exact ⟨e.symm.injective.subsingleton, hN.map e⟩
  · intro ⟨hS, hN⟩
    haveI : Subsingleton B := hS
    exact ⟨e.injective.subsingleton, hN.map e.symm⟩

lemma isTrivial_prod {A B : Type*} : IsTrivial (A × B) ↔ IsTrivial A ∧ IsTrivial B := by
  unfold IsTrivial
  constructor
  · intro ⟨hS, ⟨a, b⟩⟩
    haveI : Subsingleton (A × B) := hS
    constructor
    · constructor
      · constructor
        intro x y
        have := Subsingleton.elim (a := (x, b)) (b := (y, b))
        exact Prod.mk.inj this |>.1
      · exact ⟨a⟩
    · constructor
      · constructor
        intro x y
        have := Subsingleton.elim (a := (a, x)) (b := (a, y))
        exact Prod.mk.inj this |>.2
      · exact ⟨b⟩
  · intro ⟨⟨hSA, ⟨a⟩⟩, ⟨hSB, ⟨b⟩⟩⟩
    haveI : Subsingleton A := hSA
    haveI : Subsingleton B := hSB
    exact ⟨inferInstance, ⟨(a, b)⟩⟩

/-- Binary complexity: 0 if trivial (exactly one element), 1 otherwise. -/
noncomputable def binaryComplexity (A : Type u) : ℝ≥0∞ :=
  if IsTrivial A then 0 else 1

lemma binaryComplexity_unique (A : Type u) [Unique A] :
    binaryComplexity A = 0 := by
  simp only [binaryComplexity, isTrivial_of_unique, ↓reduceIte]

lemma binaryComplexity_congr {A B : Type u} (e : A ≃ B) :
    binaryComplexity A = binaryComplexity B := by
  simp only [binaryComplexity, isTrivial_iff_equiv e]

lemma binaryComplexity_prod_le (A B : Type u) :
    binaryComplexity (A × B) ≤ binaryComplexity A + binaryComplexity B := by
  simp only [binaryComplexity]
  by_cases hAB : IsTrivial (A × B)
  · simp only [hAB, ↓reduceIte, zero_le]
  · simp only [hAB, ↓reduceIte]
    -- LHS = 1, need 1 ≤ binaryComplexity A + binaryComplexity B
    -- Since A×B is not trivial, at least one of A, B is not trivial
    by_cases hA : IsTrivial A <;> by_cases hB : IsTrivial B
    · -- Both trivial means product trivial, contradiction
      exact absurd (isTrivial_prod.mpr ⟨hA, hB⟩) hAB
    · -- A trivial, B not trivial
      simp only [hA, hB, ↓reduceIte, zero_add, le_refl]
    · -- A not trivial, B trivial
      simp only [hA, hB, ↓reduceIte, add_zero, le_refl]
    · -- Neither trivial
      simp only [hA, hB, ↓reduceIte]
      exact le_add_right le_rfl

lemma binaryComplexity_sigma_le (D : Type u) (P : D → Type u) :
    binaryComplexity (Σ d, P d) ≤ binaryComplexity D + ⨆ d, binaryComplexity (P d) := by
  simp only [binaryComplexity]
  by_cases hSigma : IsTrivial (Σ d, P d)
  · simp only [hSigma, ↓reduceIte, zero_le]
  · simp only [hSigma, ↓reduceIte]
    -- LHS = 1, need 1 ≤ binaryComplexity D + sup binaryComplexity (P d)
    by_cases hD : IsTrivial D
    · -- D is trivial, so some fiber must be non-trivial
      simp only [hD, ↓reduceIte, zero_add]
      -- Need to show 1 ≤ sup, i.e., some fiber has binaryComplexity = 1
      obtain ⟨hDsub, ⟨d₀⟩⟩ := hD
      haveI : Subsingleton D := hDsub
      -- If all fibers were trivial, then Sigma would be trivial
      by_contra h_sup
      push_neg at h_sup
      apply hSigma
      -- Show Sigma is trivial
      have all_fibers_trivial : ∀ d, IsTrivial (P d) := by
        intro d
        by_contra hP
        have h1 : (1 : ℝ≥0∞) ≤ ⨆ d', if IsTrivial (P d') then 0 else 1 := by
          apply le_iSup_of_le d
          simp only [hP, ↓reduceIte, le_refl]
        exact h_sup.not_ge h1
      constructor
      · -- Sigma is Subsingleton
        constructor
        intro ⟨d₁, p₁⟩ ⟨d₂, p₂⟩
        have heq : d₁ = d₂ := Subsingleton.elim d₁ d₂
        subst heq
        congr 1
        exact (all_fibers_trivial d₁).1.elim p₁ p₂
      · -- Sigma is Nonempty
        exact ⟨⟨d₀, (all_fibers_trivial d₀).2.some⟩⟩
    · -- D is not trivial
      simp only [hD, ↓reduceIte]
      -- LHS = 1 ≤ 1 + sup = RHS
      exact le_add_right le_rfl

/-- The binary complexity measure instance.

This proves the `SigmaComplexity` axioms are consistent (non-vacuous). -/
noncomputable instance : SigmaComplexity ℝ≥0∞ where
  C := binaryComplexity
  unique_zero := binaryComplexity_unique
  congr := binaryComplexity_congr
  prod_le := binaryComplexity_prod_le
  sigma_le := binaryComplexity_sigma_le

end Gardenpath
