import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Unique
import Mathlib.Data.Set.Image
import Mathlib.Tactic.Abel
import Gardenpath.Pullback

/-!
# Complexity Measures on Types

A complexity measure assigns a non-negative "cost" to types, satisfying axioms that
capture information-theoretic intuitions:

1. **Triviality**: Types with unique inhabitants have zero complexity
2. **Invariance**: Equivalent types have equal complexity
3. **Subadditivity**: Products and sigma types cost at most the sum of their parts

These axioms formalize the "Efficiency of Dependency" principle: shared structure
(fiber products) enables tighter capacity bounds than independent specification.

## Main definitions

* `ComplexityMeasure` - The typeclass capturing complexity axioms
* `SigmaComplexity` - Extended with sigma subadditivity

## Main results

* `refactoring_bound` - Pullback complexity bounded by shared base + fiber sups
-/

universe u v w

/-- A complexity measure on types.

This captures the abstract structure needed for the Structural Economy framework.
The codomain `M` is typically `ℝ≥0∞`. -/
class ComplexityMeasure (M : Type*) [AddCommMonoid M] [PartialOrder M] where
  /-- The complexity of a type. -/
  C : Type u → M
  /-- Unique types (singletons) have zero complexity.
      These are the "trivial" types with no information content. -/
  unique_zero : ∀ (A : Type u) [Unique A], C A = 0
  /-- Equivalent types have equal complexity.
      Complexity is a property of the type up to equivalence. -/
  congr : ∀ {A B : Type u}, A ≃ B → C A = C B
  /-- Product subadditivity: combining independent systems costs at most
      the sum of their individual costs. -/
  prod_le : ∀ (A B : Type u), C (A × B) ≤ C A + C B

namespace ComplexityMeasure

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [inst : ComplexityMeasure M]

/-- Swapping product components preserves complexity. -/
lemma prod_comm (A B : Type u) : inst.C (A × B) = inst.C (B × A) :=
  inst.congr (Equiv.prodComm A B)

/-- Product associativity preserves complexity. -/
lemma prod_assoc (A B C : Type u) : inst.C ((A × B) × C) = inst.C (A × (B × C)) :=
  inst.congr (Equiv.prodAssoc A B C)

/-- Unit is a neutral element for products (up to complexity). -/
lemma prod_punit (A : Type u) : inst.C (A × PUnit) = inst.C A :=
  inst.congr (Equiv.prodPUnit A)

/-- PUnit has zero complexity. -/
lemma punit_zero : inst.C (PUnit : Type u) = 0 := inst.unique_zero PUnit

end ComplexityMeasure

/-!
## Sigma-Type Complexity

The key axiom is **sigma subadditivity**:
  `C(Σ d : D, P d) ≤ C(D) + sup_d C(P d)`

This is a capacity bound: a dependent sum requires at most the base capacity
plus the worst-case fiber capacity.

Note: This is an *inequality*, not an equality. The equality form
`C(Σ d, P d) = C(D) + sup C(P d)` is inconsistent (forces C(D) = 0 for all D).
-/

/-- Extended complexity measure with sigma decomposition.

This adds the crucial axiom bounding sigma types by base + sup of fibers. -/
class SigmaComplexity (M : Type*) [AddCommMonoid M] [PartialOrder M] [SupSet M]
    extends ComplexityMeasure (M := M) where
  /-- Sigma subadditivity: the complexity of a sigma type is bounded by
      the base plus the supremum of fiber complexities. -/
  sigma_le : ∀ (D : Type u) (P : D → Type u),
    C (Σ d, P d) ≤ C D + ⨆ (d : D), C (P d)

/-!
## Additive Complexity (Scarcity)

In universes with **scarcity**, information is rivalrous: knowing something twice
costs twice as much. This is captured by product **equality** rather than inequality.

The key insight: structural economy ("gravity") only emerges under scarcity.
With saturation (BinaryComplexity), there's no pressure to optimize.
With additivity (LogCardinality), redundancy hurts, driving standardization.
-/

/-- Additive complexity measure: products cost exactly the sum of parts.

This models "scarce" universes where information is rivalrous.
The "force of structure" only exists under additivity. -/
class AdditiveComplexity (M : Type*) [AddCommMonoid M] [PartialOrder M] [SupSet M]
    extends SigmaComplexity (M := M) where
  /-- Product additivity: combining independent systems costs exactly the sum. -/
  prod_eq : ∀ (A B : Type u), C (A × B) = C A + C B

namespace AdditiveComplexity

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [SupSet M]
variable [inst : AdditiveComplexity M]

/-- Additivity implies the weaker subadditivity. -/
lemma prod_le_of_eq (A B : Type u) : inst.C (A × B) ≤ inst.C A + inst.C B :=
  le_of_eq (inst.prod_eq A B)

/-- Triple products decompose additively. -/
lemma prod_triple (A B C : Type u) :
    inst.C (A × B × C) = inst.C A + inst.C B + inst.C C := by
  rw [inst.prod_eq, inst.prod_eq, add_assoc]

end AdditiveComplexity

/-!
## The Refactoring Bound

The main theorem: pullback complexity is bounded by shared base + fiber sups.

Given `f : A → D` and `g : B → D`, the pullback `A ×_D B` factors through `D`.
Its complexity is bounded by `C(D) + sup(Fiber f) + sup(Fiber g)`.

Compare to the product bound: `C(A × B) ≤ C(A) + C(B)`, where each of
`C(A)` and `C(B)` may include a `C(D)` component. The pullback representation
counts `C(D)` once instead of twice.
-/

section RefactoringBound

variable {M : Type*} [ConditionallyCompleteLattice M] [AddCommMonoid M] [IsOrderedAddMonoid M]
variable [inst : SigmaComplexity M]
variable {A B D : Type u} (f : A → D) (g : B → D)

omit [IsOrderedAddMonoid M] in
/-- The complexity of the pullback, expressed via the sigma-fiber equivalence. -/
lemma pullback_complexity_eq :
    inst.C (f.Pullback g) = inst.C (Σ d : D, FiberProd f g d) :=
  inst.congr Function.Pullback.equivSigmaFiber

omit [IsOrderedAddMonoid M] in
/-- Fiber products have bounded complexity. -/
lemma fiberProd_le (d : D) :
    inst.C (FiberProd f g d) ≤ inst.C (Fiber f d) + inst.C (Fiber g d) :=
  inst.prod_le (Fiber f d) (Fiber g d)

/-- **The Refactoring Bound**:
    Pullback complexity is bounded by shared base + independent fiber sups.

    C(A ×_D B) ≤ C(D) + sup_d C(Fiber f d) + sup_d C(Fiber g d)

    This captures structural economy: the pullback representation factors
    through the shared dependency D, avoiding redundant representation. -/
theorem refactoring_bound
    (hf : BddAbove (Set.range fun d => inst.C (Fiber f d)))
    (hg : BddAbove (Set.range fun d => inst.C (Fiber g d)))
    (hne : Nonempty D) :
    inst.C (f.Pullback g) ≤ inst.C D + (⨆ d, inst.C (Fiber f d)) + (⨆ d, inst.C (Fiber g d)) := by
  -- 1. Decompose pullback via sigma-fiber equivalence
  rw [pullback_complexity_eq]
  -- 2. Apply sigma subadditivity
  have key : ⨆ d, inst.C (FiberProd f g d) ≤
             (⨆ d, inst.C (Fiber f d)) + (⨆ d, inst.C (Fiber g d)) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨d, rfl⟩
    calc inst.C (FiberProd f g d)
        ≤ inst.C (Fiber f d) + inst.C (Fiber g d) := fiberProd_le f g d
      _ ≤ (⨆ d, inst.C (Fiber f d)) + (⨆ d, inst.C (Fiber g d)) :=
          add_le_add (le_csSup hf (Set.mem_range_self d))
                     (le_csSup hg (Set.mem_range_self d))
  calc inst.C (Σ d, FiberProd f g d)
      ≤ inst.C D + ⨆ d, inst.C (FiberProd f g d) := inst.sigma_le D _
    _ ≤ inst.C D + ((⨆ d, inst.C (Fiber f d)) + (⨆ d, inst.C (Fiber g d))) :=
        add_le_add_right key _
    _ = inst.C D + (⨆ d, inst.C (Fiber f d)) + (⨆ d, inst.C (Fiber g d)) := by abel

end RefactoringBound

/-!
## Triviality and Structure

A type is **trivial** if it is `Unique` (contractible/singleton).
Trivial types have zero complexity by the `unique_zero` axiom.

When the shared base `D` is trivial, the pullback degenerates to the product
and the refactoring bound provides no improvement over the product bound.
-/

section Triviality

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [inst : ComplexityMeasure M]

/-- Unique types have zero complexity. -/
lemma complexity_unique (A : Type u) [Unique A] : inst.C A = 0 := inst.unique_zero A

/-- PUnit has zero complexity. -/
lemma complexity_punit : inst.C (PUnit : Type u) = 0 := inst.unique_zero PUnit

/-- Equivalent types have equal complexity. -/
lemma complexity_equiv {A B : Type u} (e : A ≃ B) : inst.C A = inst.C B := inst.congr e

/-- Products with a unique factor simplify. -/
lemma prod_unique_right (A : Type u) (B : Type u) [Unique B] :
    inst.C (A × B) = inst.C A :=
  inst.congr (Equiv.prodUnique A B)

/-- Products with a unique factor simplify (left version). -/
lemma prod_unique_left (A : Type u) (B : Type u) [Unique A] :
    inst.C (A × B) = inst.C B :=
  inst.congr (Equiv.uniqueProd B A)

end Triviality

section TrivialBase

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [SupSet M]
variable [inst : SigmaComplexity M]
variable {A B D : Type u} (f : A → D) (g : B → D)

/-- When the base `D` is unique, the pullback is equivalent to the product. -/
lemma pullback_equiv_prod_of_unique [Unique D] :
    inst.C (f.Pullback g) = inst.C (A × B) :=
  inst.congr Function.Pullback.equivProdOfSubsingleton

/-- When the base is trivial, its complexity is zero. -/
lemma complexity_base_unique [Unique D] : inst.C D = 0 := inst.unique_zero D

/-- A function to a unique type has fibers equivalent to the domain. -/
lemma fiber_unique_codomain [Unique D] (d : D) : inst.C (Fiber f d) = inst.C A := by
  have : ∀ a, f a = d := fun a => Subsingleton.elim (f a) d
  exact inst.congr ⟨Subtype.val, fun a => ⟨a, this a⟩, fun _ => rfl, fun _ => rfl⟩

end TrivialBase
