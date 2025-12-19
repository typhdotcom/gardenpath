import Gardenpath.Complexity
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv

/-!
# Dynamics of Structural Economy

The **Directed Bounded Category (DBC)** framework.

While `Complexity.lean` describes the *statics* (the weight of configurations),
this module describes the *dynamics* (the cost of transitions).

## The Three Axioms

1. **Direction**: Morphisms (transitions) are not freely invertible.
2. **Bounded Additive Cost**: Transitions have additive cost under finite capacity.
3. **Retraction Asymmetry**: Undoing costs strictly more than doing.

## Main Results

- `ratchet`: Once you've spent > K/2 on a non-invertible transition, you can't return.
- `GardenPath`: A cheap transition with expensive retraction.

## Interpretation

- **Landauer's Principle**: Erasure (retraction) has thermodynamic cost.
- **Legacy Code**: Configurations where retraction cost exceeds capacity K.
- **Garden Path**: A cheap transition you can't afford to undo.
-/

universe u

namespace Gardenpath

open scoped ENNReal

/-!
## Core Definitions

We work with ℝ≥0∞ as the cost type for consistency with the statics.
-/

/-- A retraction of f : A → B is a function r : B → A with r ∘ f = id. -/
def IsRetraction {A B : Type u} (f : A → B) (r : B → A) : Prop := r ∘ f = id

/-- A function is an equivalence if it has a two-sided inverse. -/
def IsEquiv {A B : Type u} (f : A → B) : Prop :=
  ∃ g : B → A, f ∘ g = id ∧ g ∘ f = id

/-- Equivalences are retractions. -/
lemma IsEquiv.isRetraction {A B : Type u} {f : A → B} (h : IsEquiv f) :
    ∃ r, IsRetraction f r := by
  obtain ⟨g, _, hgf⟩ := h
  exact ⟨g, hgf⟩

/-!
## Transition Cost Structure

Axioms 1 and 2: Directed transitions with additive bounded cost.
-/

/-- A transition cost structure on types.
    T(f) measures the cost of transitioning via f. -/
structure TransitionCostData where
  /-- The cost of a transition. -/
  T : {A B : Type u} → (A → B) → ℝ≥0∞
  /-- Identity transitions are free. -/
  T_id : ∀ (A : Type u), T (id : A → A) = 0
  /-- Sequential transitions have additive cost. -/
  T_comp : ∀ {A B C : Type u} (f : A → B) (g : B → C), T (g ∘ f) = T f + T g
  /-- The capacity bound. -/
  K : ℝ≥0∞
  /-- Positive capacity (non-degenerate universe). -/
  K_pos : 0 < K

namespace TransitionCostData

variable (tc : TransitionCostData)

/-- A transition is realizable if its cost doesn't exceed capacity. -/
def Realizable {A B : Type u} (f : A → B) : Prop := tc.T f ≤ tc.K

/-- Identity is always realizable. -/
lemma realizable_id (A : Type u) : tc.Realizable (id : A → A) := by
  simp only [Realizable, tc.T_id]
  exact le_of_lt tc.K_pos

/-- Composition of realizable transitions may exceed capacity. -/
lemma realizable_comp_cost {A B C : Type u} (f : A → B) (g : B → C) :
    tc.T (g ∘ f) = tc.T f + tc.T g := tc.T_comp f g

end TransitionCostData

/-!
## Retraction Asymmetry (Axiom 3)

The key axiom: undoing a non-trivial transition costs strictly more than doing it.
-/

/-- Axiom 3: Retraction asymmetry.
    For non-equivalences, any retraction costs strictly more than the forward map. -/
structure RetractionAsymmetry (tc : TransitionCostData) where
  /-- The premium paid to undo a non-equivalence. -/
  retraction_premium : ∀ {A B : Type u} (f : A → B) (r : B → A),
    IsRetraction f r → ¬IsEquiv f → tc.T r > tc.T f

/-!
## The Ratchet Lemma

Once you've spent more than half your capacity on a non-equivalence,
you cannot afford to return.
-/

/-- **The Ratchet Lemma**: Beyond the halfway point, the round trip exceeds capacity.

If T(f) > K/2 and f is not an equivalence, then T(f) + T(r) > K for any retraction r.
You can walk in, but you can't complete the round trip. -/
theorem ratchet (tc : TransitionCostData) (ra : RetractionAsymmetry tc)
    {A B : Type u} (f : A → B) (r : B → A)
    (hret : IsRetraction f r) (hne : ¬IsEquiv f)
    (hcost : tc.K / 2 < tc.T f) :
    tc.K < tc.T f + tc.T r := by
  have hprem := ra.retraction_premium f r hret hne
  -- T(f) + T(r) > T(f) + T(f) > K/2 + K/2 = K
  have h1 : tc.K / 2 + tc.K / 2 = tc.K := ENNReal.add_halves tc.K
  -- Need T(f) ≠ ⊤ for add_lt_add lemmas
  have hf_finite : tc.T f ≠ ⊤ := by
    intro hf_top
    -- If T(f) = ⊤, then T(r) > T(f) = ⊤ is impossible (nothing exceeds ⊤)
    rw [hf_top] at hprem
    exact not_top_lt hprem
  have h2 : tc.K / 2 + tc.K / 2 < tc.T f + tc.T f := by
    apply ENNReal.add_lt_add hcost hcost
  have h3 : tc.T f + tc.T f < tc.T f + tc.T r := by
    exact ENNReal.add_lt_add_left hf_finite hprem
  calc tc.K = tc.K / 2 + tc.K / 2 := h1.symm
    _ < tc.T f + tc.T f := h2
    _ < tc.T f + tc.T r := h3

/-- Corollary: Beyond the halfway point, transitions become irreversible. -/
theorem irreversible_beyond_half (tc : TransitionCostData) (ra : RetractionAsymmetry tc)
    {A B : Type u} (f : A → B) (hne : ¬IsEquiv f) (hcost : tc.K / 2 < tc.T f) :
    ∀ r : B → A, IsRetraction f r → tc.K < tc.T f + tc.T r :=
  fun r hret => ratchet tc ra f r hret hne hcost

/-!
## Garden Paths

A garden path is a cheap transition with expensive retraction.
You can afford to walk in; you can't afford to walk out.
-/

/-- A transition is a garden path if it's cheap but the round trip exceeds capacity. -/
structure GardenPath (tc : TransitionCostData) {A B : Type u} (f : A → B) where
  /-- The forward transition is affordable. -/
  affordable : tc.Realizable f
  /-- But any retraction makes the round trip unaffordable. -/
  trapped : ∀ r : B → A, IsRetraction f r → tc.K < tc.T f + tc.T r

/-- Non-equivalences beyond the halfway point are garden paths. -/
theorem gardenPath_of_half (tc : TransitionCostData) (ra : RetractionAsymmetry tc)
    {A B : Type u} (f : A → B)
    (hne : ¬IsEquiv f) (hreal : tc.Realizable f) (hcost : tc.K / 2 < tc.T f) :
    GardenPath tc f :=
  ⟨hreal, irreversible_beyond_half tc ra f hne hcost⟩

/-!
## Void Fragility and the Motor

The void (Unique type) is unstable: any non-identity transition creates structure
that costs to undo.

### The Motor

The "motor" driving structure accumulation is not a separate axiom but emerges from
what we already have:

1. **K_pos**: `0 < K` means the system has capacity to explore. A system with
   positive capacity is *live* - it is not frozen at absolute zero.

2. **Retraction Asymmetry**: Forward transitions cost less than their reversals.

Together, these create a **statistical ratchet**: the system explores (because K > 0),
and exploration accumulates structure (because return costs more than departure).

This is the Second Law of Thermodynamics applied to information: fluctuations
don't cancel because the system acts as a diode for complexity.
-/

/-- Any non-equivalence has expensive retraction. -/
theorem retraction_expensive (tc : TransitionCostData) (ra : RetractionAsymmetry tc)
    {A B : Type u} (f : A → B) (hne : ¬IsEquiv f) :
    ∀ r : B → A, IsRetraction f r → tc.T r > tc.T f :=
  fun r hret => ra.retraction_premium f r hret hne

/-- **Void Instability**: From the void, any non-equivalence is a one-way door.

The round trip costs strictly more than twice the departure, so fluctuations
out of the void accumulate rather than cancel. This is the motor in action:
K_pos allows departure, retraction asymmetry prevents return. -/
theorem void_roundtrip_asymmetry (tc : TransitionCostData) (ra : RetractionAsymmetry tc)
    {A B : Type u} (f : A → B) (r : B → A)
    (hret : IsRetraction f r) (hne : ¬IsEquiv f) :
    tc.T f + tc.T r > tc.T f + tc.T f := by
  have hprem := ra.retraction_premium f r hret hne
  have hf_finite : tc.T f ≠ ⊤ := by
    intro hf_top
    rw [hf_top] at hprem
    exact not_top_lt hprem
  exact ENNReal.add_lt_add_left hf_finite hprem

/-- The void is a repeller: leaving is always cheaper than the round trip.

For any realizable non-equivalence from Unique, departure succeeds but
return exceeds the departure cost. Structure accumulates. -/
theorem void_is_repeller (tc : TransitionCostData) (ra : RetractionAsymmetry tc)
    {A : Type u} [Unique A] {B : Type u} (f : A → B) (hne : ¬IsEquiv f) :
    ∀ r : B → A, IsRetraction f r → tc.T r > tc.T f :=
  retraction_expensive tc ra f hne

/-!
## Connection to Static Complexity

The statics (ComplexityMeasure) tells us which configurations are cheap to maintain.
The dynamics (TransitionCostData) tells us which transitions trap us.

**Pullbacks**: Low static cost (efficient), reachable by design.
**Products**: High static cost (wasteful), easy to fall into, hard to escape.

The goal: design transitions that land in pullback configurations,
avoiding the garden paths that lead to product configurations.
-/

/-- A transition is "structure-preserving" if it doesn't increase complexity. -/
def StructurePreserving [inst : ComplexityMeasure ℝ≥0∞] {A B : Type u} (_f : A → B) : Prop :=
  inst.C B ≤ inst.C A

/-- A transition is "structure-creating" if it increases complexity. -/
def StructureCreating [inst : ComplexityMeasure ℝ≥0∞] {A B : Type u} (_f : A → B) : Prop :=
  inst.C B > inst.C A

/-!
## The Full Picture

**Statics** (Complexity.lean): C(A) measures configuration weight.
- Pullbacks have lower C than products.
- Shared structure reduces maintenance cost.

**Dynamics** (this file): T(f) measures transition cost.
- Creating structure is cheap: T(f) can be small.
- Removing structure is expensive: T(r) > T(f) for non-equivalences.
- Beyond K/2, transitions become irreversible.

**Together**: You will fall into structure.
The question is *which* structure.
Design for pullbacks, or get trapped in products.
-/

end Gardenpath
