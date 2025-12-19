import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Set.Prod

/-!
# Pullback Infrastructure for Structural Economy

This module builds on mathlib's `Function.Pullback` to provide the key equivalence
needed for the Refactoring Inequality: the pullback factors through sigma of fiber products.

We use:
- `Function.Pullback f g` from mathlib (the fiber product `{p : A × B // f p.1 = g p.2}`)
- `Equiv.sigmaFiberEquiv` from mathlib (the fiber decomposition `Σ b, {a // f a = b} ≃ A`)

## Main definitions

* `Fiber f b` - Abbreviation for the fiber `{a // f a = b}`
* `FiberProd f g d` - The product of fibers over a common base point

## Main results

* `Function.Pullback.equivSigmaFiber` - The pullback is equivalent to `Σ d, Fiber f d × Fiber g d`
* `Function.Pullback.equivProdOfSubsingleton` - When `D` is trivial, pullback ≃ product
-/

universe u v w

/-- The fiber of a function over a point. This is an abbreviation for the subtype. -/
abbrev Fiber {A : Type u} {B : Type v} (f : A → B) (b : B) : Type u :=
  { a : A // f a = b }

/-- The product of fibers over a common base point. -/
abbrev FiberProd {A : Type u} {B : Type v} {D : Type w}
    (f : A → D) (g : B → D) (d : D) : Type (max u v) :=
  Fiber f d × Fiber g d

namespace Function.Pullback

variable {A : Type u} {B : Type v} {D : Type w} {f : A → D} {g : B → D}

/-- The shared value in `D` that both projections map to. -/
def base (p : f.Pullback g) : D := f p.fst

lemma base_eq_fst (p : f.Pullback g) : p.base = f p.fst := rfl

lemma base_eq_snd (p : f.Pullback g) : p.base = g p.snd := p.2

/-- Construct a pullback element from components. -/
def mk (a : A) (b : B) (h : f a = g b) : f.Pullback g := ⟨(a, b), h⟩

@[simp] lemma fst_mk (a : A) (b : B) (h : f a = g b) : (mk a b h).fst = a := rfl
@[simp] lemma snd_mk (a : A) (b : B) (h : f a = g b) : (mk a b h).snd = b := rfl
@[simp] lemma base_mk (a : A) (b : B) (h : f a = g b) : (mk a b h).base = f a := rfl

@[ext]
lemma ext' {p q : f.Pullback g} (h1 : p.fst = q.fst) (h2 : p.snd = q.snd) : p = q := by
  obtain ⟨⟨a₁, b₁⟩, _⟩ := p
  obtain ⟨⟨a₂, b₂⟩, _⟩ := q
  simp only [fst, snd] at h1 h2
  subst h1 h2
  rfl

/-!
## The Fundamental Equivalence

The pullback `f.Pullback g` is equivalent to `Σ d : D, Fiber f d × Fiber g d`.

This shows that the pullback "factors through" the shared dependency `D`:
- First, pick a point `d : D`
- Then, pick elements in the fibers over `d`

This is more efficient than `A × B` when `D` carries non-trivial structure,
because `D` is represented once rather than redundantly in both `A` and `B`.
-/

/-- Forward direction: pullback to sigma of fiber products. -/
def toSigmaFiber (p : f.Pullback g) : Σ d : D, FiberProd f g d :=
  ⟨p.base, ⟨p.fst, rfl⟩, ⟨p.snd, p.base_eq_snd.symm⟩⟩

/-- Backward direction: sigma of fiber products to pullback. -/
def ofSigmaFiber (x : Σ d : D, FiberProd f g d) : f.Pullback g :=
  mk x.2.1.val x.2.2.val (x.2.1.property.trans x.2.2.property.symm)

/-- **The Fundamental Equivalence**: The pullback factors through the base.

This is the core mathematical fact underlying structural economy:
the pullback representation makes the shared structure `D` explicit. -/
def equivSigmaFiber : f.Pullback g ≃ Σ d : D, FiberProd f g d where
  toFun := toSigmaFiber
  invFun := ofSigmaFiber
  left_inv p := Subtype.ext rfl
  right_inv := fun ⟨_, ⟨_, ha⟩, ⟨_, hb⟩⟩ => by subst ha; rfl

/-!
## Relationship to Products

When `D` is a subsingleton (trivial), the pullback is equivalent to the full product.
This is the base case: no shared structure means no savings.
-/

/-- When `D` is a subsingleton, the pullback is equivalent to the product. -/
def equivProdOfSubsingleton [Subsingleton D] : f.Pullback g ≃ A × B where
  toFun p := (p.fst, p.snd)
  invFun p := mk p.1 p.2 (Subsingleton.elim _ _)
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

/-- The canonical inclusion from pullback to product. -/
def toProd : f.Pullback g → A × B := fun p => (p.fst, p.snd)

lemma toProd_injective : Function.Injective (toProd (f := f) (g := g)) := by
  intro p q h
  simp only [toProd, Prod.mk.injEq] at h
  exact ext' h.1 h.2

/-- The pullback embeds into the product. -/
def embeddingToProd : f.Pullback g ↪ A × B :=
  ⟨toProd, toProd_injective⟩

end Function.Pullback
