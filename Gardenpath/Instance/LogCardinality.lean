import Gardenpath.Complexity
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Log-Cardinality Complexity Measure

The "hero instance" demonstrating AdditiveComplexity.

For finite types, complexity is the logarithm of cardinality:
  `C(A) = log |A|`

This captures "bits needed to specify an element" - the Shannon entropy
of a uniform distribution.

## Key Properties

- **Additivity**: `C(A × B) = log(|A| · |B|) = log|A| + log|B| = C(A) + C(B)`
- **Sigma bound**: `C(Σ d, P d) = log(Σ|P d|) ≤ log(|D| · max|P d|) = C(D) + sup C(P d)`

This demonstrates structural economy under scarcity:
with additive complexity, shared structure genuinely saves bits.
-/

universe u

namespace Gardenpath

open scoped ENNReal

/-- Log-cardinality complexity for finite types.
    Returns log(card A) as an extended non-negative real. -/
noncomputable def logCardinality (A : Type*) [Fintype A] : ℝ≥0∞ :=
  ENNReal.ofReal (Real.log (Fintype.card A))

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Unique types have cardinality 1, so log-complexity 0. -/
lemma logCardinality_unique [Unique A] : logCardinality A = 0 := by
  simp only [logCardinality, Fintype.card_unique, Nat.cast_one, Real.log_one, ENNReal.ofReal_zero]

/-- Equivalent finite types have the same log-cardinality. -/
lemma logCardinality_congr (e : A ≃ B) : logCardinality A = logCardinality B := by
  simp only [logCardinality, Fintype.card_congr e]

/-- Product cardinality is multiplicative, so log-complexity is additive.
    This is the key property: under scarcity, costs add up exactly. -/
lemma logCardinality_prod [Nonempty A] [Nonempty B] :
    logCardinality (A × B) = logCardinality A + logCardinality B := by
  simp only [logCardinality, Fintype.card_prod]
  have hA : 0 < Fintype.card A := Fintype.card_pos
  have hB : 0 < Fintype.card B := Fintype.card_pos
  have hA' : (1 : ℝ) ≤ Fintype.card A := Nat.one_le_cast.mpr hA
  have hB' : (1 : ℝ) ≤ Fintype.card B := Nat.one_le_cast.mpr hB
  have hApos : (0 : ℝ) < Fintype.card A := Nat.cast_pos.mpr hA
  have hBpos : (0 : ℝ) < Fintype.card B := Nat.cast_pos.mpr hB
  rw [Nat.cast_mul, Real.log_mul (ne_of_gt hApos) (ne_of_gt hBpos)]
  rw [ENNReal.ofReal_add (Real.log_nonneg hA') (Real.log_nonneg hB')]

/-- Product subadditivity: holds as equality for nonempty types. -/
lemma logCardinality_prod_le :
    logCardinality (A × B) ≤ logCardinality A + logCardinality B := by
  by_cases hA : Nonempty A <;> by_cases hB : Nonempty B
  · exact le_of_eq logCardinality_prod
  · have : IsEmpty B := not_nonempty_iff.mp hB
    simp only [logCardinality, Fintype.card_eq_zero, Nat.cast_zero, Real.log_zero,
               ENNReal.ofReal_zero, zero_le]
  · have : IsEmpty A := not_nonempty_iff.mp hA
    simp only [logCardinality, Fintype.card_eq_zero, Nat.cast_zero, Real.log_zero,
               ENNReal.ofReal_zero, zero_le]
  · have : IsEmpty A := not_nonempty_iff.mp hA
    simp only [logCardinality, Fintype.card_eq_zero, Nat.cast_zero, Real.log_zero,
               ENNReal.ofReal_zero, zero_le]

/-!
## The Sigma Bound

The critical lemma connecting log-cardinality to the abstract SigmaComplexity.
-/

/-- **The Sigma Bound**: log-cardinality satisfies the capacity bound axiom.

This validates that log-cardinality is a valid SigmaComplexity measure. -/
lemma logCardinality_sigma_le {D : Type*} [Fintype D] [Nonempty D]
    (P : D → Type*) [∀ d, Fintype (P d)] :
    logCardinality (Σ d, P d) ≤ logCardinality D + ⨆ d, logCardinality (P d) := by
  simp only [logCardinality]
  -- Handle empty sigma case (all fibers empty)
  by_cases hsum : Fintype.card (Σ d, P d) = 0
  · simp only [hsum, Nat.cast_zero, Real.log_zero, ENNReal.ofReal_zero, zero_le]
  -- Sigma is nonempty
  have hD : 0 < Fintype.card D := Fintype.card_pos
  have hDpos : (0 : ℝ) < Fintype.card D := Nat.cast_pos.mpr hD
  have hD' : (1 : ℝ) ≤ Fintype.card D := Nat.one_le_cast.mpr hD
  -- Get the maximum fiber cardinality
  let maxCard : ℕ := Finset.univ.sup' Finset.univ_nonempty fun d => Fintype.card (P d)
  have hmaxpos : 0 < maxCard := by
    have hne : Nonempty (Σ d, P d) := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hsum)
    obtain ⟨d₀, p₀⟩ := hne
    have hpos : 0 < Fintype.card (P d₀) := Fintype.card_pos_iff.mpr ⟨p₀⟩
    have hle := Finset.le_sup' (fun d => Fintype.card (P d)) (Finset.mem_univ d₀)
    exact Nat.lt_of_lt_of_le hpos hle
  have hmaxpos' : (0 : ℝ) < maxCard := Nat.cast_pos.mpr hmaxpos
  have hmax' : (1 : ℝ) ≤ maxCard := Nat.one_le_cast.mpr hmaxpos
  -- Key inequality: sum ≤ count × max
  have sum_le : (Fintype.card (Σ d, P d) : ℝ) ≤ Fintype.card D * maxCard := by
    have h1 : Fintype.card (Σ d, P d) = ∑ d, Fintype.card (P d) := Fintype.card_sigma
    have h2 : (∑ d, Fintype.card (P d) : ℕ) ≤ Fintype.card D * maxCard := by
      calc ∑ d, Fintype.card (P d)
          ≤ ∑ _d : D, maxCard := Finset.sum_le_sum fun d _ =>
              Finset.le_sup' (fun d => Fintype.card (P d)) (Finset.mem_univ d)
        _ = Fintype.card D * maxCard := by simp [Finset.sum_const, Finset.card_univ]
    calc (Fintype.card (Σ d, P d) : ℝ)
        = ((Fintype.card (Σ d, P d) : ℕ) : ℝ) := rfl
      _ = ((∑ d, Fintype.card (P d) : ℕ) : ℝ) := by rw [h1]
      _ ≤ ((Fintype.card D * maxCard : ℕ) : ℝ) := Nat.cast_le.mpr h2
      _ = (Fintype.card D : ℝ) * (maxCard : ℝ) := Nat.cast_mul _ _
  -- Apply log monotonicity and product rule
  have hsum_pos : (0 : ℝ) < Fintype.card (Σ d, P d) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero hsum)
  calc ENNReal.ofReal (Real.log (Fintype.card (Σ d, P d)))
      ≤ ENNReal.ofReal (Real.log (Fintype.card D * maxCard)) := by
          apply ENNReal.ofReal_le_ofReal
          exact Real.log_le_log hsum_pos sum_le
    _ = ENNReal.ofReal (Real.log (Fintype.card D) + Real.log maxCard) := by
          rw [Real.log_mul (ne_of_gt hDpos) (ne_of_gt hmaxpos')]
    _ = ENNReal.ofReal (Real.log (Fintype.card D)) + ENNReal.ofReal (Real.log maxCard) := by
          rw [ENNReal.ofReal_add (Real.log_nonneg hD') (Real.log_nonneg hmax')]
    _ ≤ ENNReal.ofReal (Real.log (Fintype.card D)) +
        ⨆ d, ENNReal.ofReal (Real.log (Fintype.card (P d))) := by
          gcongr
          -- The max is achieved by some d₀, and log is monotone
          obtain ⟨d₀, _, hd₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
              (fun d => Fintype.card (P d))
          have hmaxeq : maxCard = Fintype.card (P d₀) := hd₀
          rw [hmaxeq]
          -- Show log(card P d₀) ≤ sup_d log(card P d)
          -- BddAbove witness: all log-cardinalities bounded by log(maxCard)
          have hbdd : BddAbove
              (Set.range fun d => ENNReal.ofReal (Real.log (Fintype.card (P d)))) := by
            use ENNReal.ofReal (Real.log maxCard)
            intro x ⟨d, hd⟩
            simp only [← hd]
            by_cases hcard : Fintype.card (P d) = 0
            · simp only [hcard, Nat.cast_zero, Real.log_zero, ENNReal.ofReal_zero, zero_le]
            · apply ENNReal.ofReal_le_ofReal
              apply Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard))
              have hle := Finset.le_sup' (fun d => Fintype.card (P d)) (Finset.mem_univ d)
              exact Nat.cast_le.mpr hle
          exact le_ciSup_of_le hbdd d₀ le_rfl

/-!
## The Savings Theorem

For log-cardinality (additive complexity), the refactoring bound implies genuine savings.

The key comparison:
- **Product**: `C(A × B) = C(A) + C(B)`
- **Pullback**: `C(A ×_D B) ≤ C(D) + sup C(Fiber_f) + sup C(Fiber_g)`

When A and B both "contain" D (via f : A → D and g : B → D), we expect:
- `C(A) ≈ C(D) + C(Fiber_f)`
- `C(B) ≈ C(D) + C(Fiber_g)`

So:
- `C(A × B) ≈ 2·C(D) + C(Fiber_f) + C(Fiber_g)`
- `C(Pullback) ≤ C(D) + C(Fiber_f) + C(Fiber_g)`

**Savings**: `C(D)` - exactly the complexity of the shared base.

This is the "gravity" of structural economy: under scarcity (additivity),
sharing structure saves exactly the cost of the shared component.
-/

/-- When the base D is shared exactly (uniform fibers), savings equals C(D).

For uniform fiber decompositions:
- `|A| = |D| · |Fiber_f|`
- `|B| = |D| · |Fiber_g|`
- `|Pullback| = |D| · |Fiber_f| · |Fiber_g|`

So:
- `C(A × B) = log(|D|²·|F|·|G|) = 2·log|D| + log|F| + log|G|`
- `C(Pullback) = log(|D|·|F|·|G|) = log|D| + log|F| + log|G|`

Savings: `log|D| = C(D)`. -/
theorem savings_uniform {D F G : Type*} [Fintype D] [Fintype F] [Fintype G]
    [hD : Nonempty D] [hF : Nonempty F] [hG : Nonempty G] :
    logCardinality (D × F) + logCardinality (D × G) =
    logCardinality (D × F × G) + logCardinality D := by
  haveI : Nonempty (D × F) := inferInstance
  haveI : Nonempty (F × G) := inferInstance
  have hDF : logCardinality (D × F) = logCardinality D + logCardinality F := logCardinality_prod
  have hDG : logCardinality (D × G) = logCardinality D + logCardinality G := logCardinality_prod
  -- D × F × G is D × (F × G) by Lean's right-associativity
  have hDFG : logCardinality (D × F × G) =
      logCardinality D + logCardinality F + logCardinality G := by
    have hFG : logCardinality (F × G) = logCardinality F + logCardinality G := logCardinality_prod
    calc logCardinality (D × F × G)
        = logCardinality D + logCardinality (F × G) := logCardinality_prod
      _ = logCardinality D + (logCardinality F + logCardinality G) := by rw [hFG]
      _ = logCardinality D + logCardinality F + logCardinality G := by ring
  rw [hDF, hDG, hDFG]
  ring

end Gardenpath
