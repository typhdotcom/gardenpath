# Gardenpath

A Lean 4 formalization of structural economy in Type Theory.

Under capacity constraints, shared dependency (fiber products/pullbacks) is bounded more tightly than independent specification (Cartesian products). The key insight: **decomposition is always valid** (the Refactoring Bound), but **genuine savings** requires:
1. **Scarcity** (additive complexity) - information is rivalrous
2. **Uniformity** (standardized fibers) - shared structure is actually shared

## Building

Requires Lean 4.26.0 and mathlib.

```bash
lake exe cache get  # download mathlib cache
lake build
```

## Structure

- `Gardenpath/Pullback.lean` - Fiber products and the fundamental equivalence
- `Gardenpath/Complexity.lean` - Complexity measure axioms and the Refactoring Bound
- `Gardenpath/Dynamics.lean` - Directed Bounded Category framework (transition costs)
- `Gardenpath/Instance/BinaryComplexity.lean` - Minimal consistent instance (saturation)
- `Gardenpath/Instance/LogCardinality.lean` - Additive instance demonstrating savings

## Theory

### Complexity Measures

A complexity measure assigns non-negative cost to types, satisfying:

**Base Axioms** (`ComplexityMeasure`)
1. **Triviality**: `C(A) = 0` when A is Unique (singleton/contractible)
2. **Invariance**: `A ≃ B → C(A) = C(B)` (complexity respects equivalence)
3. **Product Subadditivity**: `C(A × B) ≤ C(A) + C(B)`

**Sigma Capacity Bound** (`SigmaComplexity`)

4. **Sigma Subadditivity**: `C(Σ d : D, P d) ≤ C(D) + sup_d C(P d)`

This is a capacity bound: a dependent sum needs at most the base capacity plus the worst-case fiber capacity.

**Additivity / Scarcity** (`AdditiveComplexity`)

5. **Product Equality**: `C(A × B) = C(A) + C(B)`

Under scarcity, costs add exactly. This models universes where information is rivalrous.

### The Refactoring Bound

Given `f : A → D` and `g : B → D`, the pullback `A ×_D B = {(a,b) | f(a) = g(b)}` factors through the shared base D.

**Theorem** (`refactoring_bound`):
```
C(A ×_D B) ≤ C(D) + sup_d C(Fiber_f d) + sup_d C(Fiber_g d)
```

Compare to the product bound `C(A × B) ≤ C(A) + C(B)` where each of A and B may contain D redundantly. The pullback representation counts D once.

### When Savings Emerge

The Refactoring Bound is an *inequality*. Genuine savings requires:

**Condition 1: Scarcity (Additivity)** - Under `AdditiveComplexity`, products cost exactly the sum. Without additivity, complexity can "saturate" (like BinaryComplexity: 0 or 1). No savings is possible because there's no cost to redundancy.

**Condition 2: Uniformity (Standardization)** - When A and B decompose uniformly over D:
- `A ≃ D × F` (uniform fibers of size F)
- `B ≃ D × G` (uniform fibers of size G)

Then the pullback `A ×_D B ≃ D × F × G`.

**Theorem** (`savings_uniform`):
```
C(D × F) + C(D × G) = C(D × F × G) + C(D)
```

Rearranging: `C(product) - C(pullback) = C(D)`. Under scarcity + uniformity, savings equals exactly the complexity of the shared base.

### Instances

**BinaryComplexity** (Saturation): `C(A) = 0` if trivial, `1` otherwise. Proves axioms are consistent. Demonstrates saturation: all non-trivial types have the same cost, so no savings from sharing.

**LogCardinality** (Scarcity): For finite types, `C(A) = log(|A|)`. Captures "bits needed to specify an element". Product additivity: `log(|A × B|) = log(|A|) + log(|B|)`. This is the "hero instance" demonstrating `AdditiveComplexity` and genuine savings.

### Dynamics: The DBC Framework

The statics (above) describe configuration weight. The **Directed Bounded Category** framework describes transition cost - why you can't go back.

**The Three Axioms**
1. **Direction**: Transitions are not freely invertible. `f : A → B` doesn't give `B → A`.
2. **Additive Cost**: `T(g ∘ f) = T(f) + T(g)`, bounded by capacity `K`.
3. **Retraction Asymmetry**: For non-equivalences, `T(retraction) > T(forward)`.

**Ratchet Lemma** (`ratchet`): If `T(f) > K/2` and f is not an equivalence, then `T(f) + T(r) > K` for any retraction r. You can walk in; you can't complete the round trip.

**Garden Path**: A transition that's affordable forward but traps you:
- `Realizable f` (can afford to walk in)
- `∀ r, T(f) + T(r) > K` (can't afford to walk out)

## Interpretations

### As a Model of Software Engineering

Types are **states of a codebase**. Complexity is **maintenance cost** - the cognitive load and effort to keep things working.

A **product** is copy-paste. Two modules that each contain their own copy of shared logic. A **pullback** is proper factoring - both modules import from a shared dependency.

The **Refactoring Bound** says: extracting shared code into a common dependency is never worse than leaving copies everywhere. You pay for the shared module once, then each consumer only pays for what's unique to them.

But refactoring only *saves* effort when:
- **Scarcity**: You actually pay for duplication. If code review is free and servers are infinite, who cares about redundancy? In reality, attention is limited and bugs in duplicated code must be fixed twice.
- **Uniformity**: The shared part is actually the same. If every "copy" has diverged, there's nothing to factor out.

The **dynamics** explain why legacy code accumulates. Quick hacks are cheap to write but expensive to undo. Once you've burned half your sprint on a shortcut, you can't afford the refactor to escape it. The codebase walks down garden paths - easy to enter, trapped inside.

This is why greenfield feels liberating and maintenance feels like mud. You're not imagining it. The math says: structure accumulates because creating it costs less than removing it. Every expedient decision is a one-way door.

### As a Model of Reality

Types are **configurations** - possible states of a physical system. Complexity is **entropy** - the information needed to specify which state you're in.

A **product** is independent specification: to describe two particles, list all properties of each. A **pullback** is correlated specification: if both particles share a reference frame, you specify the frame once.

The **Refactoring Bound** is a statement about information: correlated descriptions are never more expensive than independent ones. Shared structure compresses.

**Scarcity** is thermodynamics. Information is physical - storing a bit requires energy, erasing a bit releases heat (Landauer's principle). In a universe with finite energy, redundant encoding has real cost.

**Retraction asymmetry** is the Second Law. You can scramble an egg cheaply; unscrambling costs more than the universe can pay. Forward transitions (creating structure, entangling systems) are cheap. Reverse transitions (erasing structure, disentangling) cost strictly more.

The **ratchet** is irreversibility. Once a system has evolved far enough from equilibrium, it cannot return - the round trip exceeds available free energy. This is why time has a direction.

The **void as repeller** explains why the universe isn't empty. A fluctuation out of nothing costs little; returning costs more. Fluctuations accumulate rather than cancel. Structure is the attractor because emptiness is unstable.

This isn't metaphor - it's the same math. Whether the "capacity" is engineer-hours or free energy, whether "complexity" is technical debt or entropy, the structure of the problem is identical. Gardenpath formalizes the pattern.
