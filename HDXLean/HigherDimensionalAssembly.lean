import HDXLean.BinaryCoordinates
import HDXLean.Families
import HDXLean.WeightedLiftAsymptotics
import HDXLean.WeightedLiftCaseBounds
import HDXLean.WeightedLiftLinks
import HDXLean.WeightedLiftTranslation

/-!
# Legacy assembly of the former higher-dimensional family

This module assembles Section 5.2 of the previous draft after importing the
complete conditioned-link calculation.  It remains as a checked result, but
the current Theorem 1.2 uses `HDXLean.GolowichProduct` instead.
-/

namespace HDXLean

namespace HigherDimensionalAssembly

/-- A convenient fixed binary fiber rank for dimension `d`. -/
def fiberRank (d : ℕ) : ℕ := 2 * d

/-- The concrete power-of-two fiber used by the lift. -/
abbrev Fiber (d : ℕ) := Fin (fiberRank d) → F₂

theorem card_fiber (d : ℕ) :
    Fintype.card (Fiber d) = 2 ^ (2 * d) := by
  change Fintype.card (Fin (2 * d) → F₂) = binaryVertexCount (2 * d)
  exact binaryVertexCount_card (2 * d)

/-- This fixed fiber has at least the `2d` labels required by Theorem 5.1. -/
theorem fiber_capacity (d : ℕ) :
    2 * d ≤ Fintype.card (Fiber d) := by
  rw [card_fiber]
  exact (2 * d).lt_two_pow_self.le

/-- The weighted lift before replacing the product group by a single
coordinate space. -/
noncomputable def rawLiftAt {lambda : ℝ}
    (base : TwoDimensionalFamily lambda) (d : ℕ) (hd : 3 ≤ d) (r : ℕ) :
    CayleyComplex
      (V := (Fin (base.ambientDimension r) → F₂) × Fiber d) :=
  WeightedLift.cayleyComplex (A := Fiber d) (base.complex r) d
    (base.dimension_eq r) (by omega) (fiber_capacity d)

/-- The same lift transported to `F₂^(n+2d)`. -/
noncomputable def coordinateLiftAt {lambda : ℝ}
    (base : TwoDimensionalFamily lambda) (d : ℕ) (hd : 3 ≤ d) (r : ℕ) :
    CayleyComplex (V := Fin (base.ambientDimension r + fiberRank d) → F₂) :=
  (rawLiftAt base d hd r).relabel
    (binaryProductEquiv (base.ambientDimension r) (fiberRank d))

@[simp]
theorem coordinateLift_dimension {lambda : ℝ}
    (base : TwoDimensionalFamily lambda) (d : ℕ) (hd : 3 ≤ d) (r : ℕ) :
    (coordinateLiftAt base d hd r).complex.dim = d :=
  rfl

theorem coordinateLift_degree {lambda : ℝ}
    (base : TwoDimensionalFamily lambda) (d : ℕ) (hd : 3 ≤ d) (r : ℕ) :
    (coordinateLiftAt base d hd r).cayley.degree =
      Fintype.card (Fiber d) * ((base.complex r).cayley.degree + 1) - 1 := by
  rw [coordinateLiftAt, CayleyComplex.relabel_degree]
  exact WeightedLift.cayley_degree (A := Fiber d) (base.complex r) d
    (base.dimension_eq r) (by omega) (fiber_capacity d)

/-- The codimension-two interface consumed by the original family assembly.
It is discharged below by the complete conditioned-link proof. -/
def LiftedCodimensionTwoBound {lambda : ℝ}
    (base : TwoDimensionalFamily lambda) (d : ℕ) (hd : 3 ≤ d) : Prop :=
  ∀ r, (rawLiftAt base d hd r).complex.CodimensionTwoBound (1 / (d : ℝ))

/-- The conditioned-link proof supplies the codimension-two premise for every
member of the lifted family. -/
theorem provedLiftedCodimensionTwoBound
    (d : ℕ) (hd : 3 ≤ d)
    (base : TwoDimensionalFamily (1 / (d : ℝ))) :
    LiftedCodimensionTwoBound base d hd := by
  intro r
  change MeasuredComplex.CodimensionTwoBound
    (WeightedLift.measuredComplex (A := Fiber d) (base.complex r).complex d
      (base.dimension_eq r) (by omega) (fiber_capacity d))
    (1 / (d : ℝ))
  exact WeightedLift.lifted_codimensionTwoBound
    (A := Fiber d) (base.complex r) d (base.dimension_eq r) hd
      (fiber_capacity d) (base.localExpansion r).2

/-- Once the conditioned-link calculation is supplied, the concrete lifts
form the complete family asserted by the previous version of Theorem 1.2. -/
noncomputable def toHigherDimensionalFamily
    (d : ℕ) (hd : 3 ≤ d)
    (base : TwoDimensionalFamily (1 / (d : ℝ)))
    (hspectral : LiftedCodimensionTwoBound base d hd) :
    HigherDimensionalFamily d where
  ambientDimension := fun r ↦ base.ambientDimension r + fiberRank d
  complex := coordinateLiftAt base d hd
  dimension_eq := coordinateLift_dimension base d hd
  localExpansion := fun r ↦ by
    apply MeasuredComplex.localSpectralExpander_relabel
    refine ⟨?_, hspectral r⟩
    exact WeightedLift.lifted_positiveLinksConnected
      (A := Fiber d) (base.complex r) d (base.dimension_eq r)
      (by omega) (fiber_capacity d) (base.localExpansion r).1
  ambientDimension_tendsToInfinity :=
    tendsToInfinity_liftedDimension
      base.ambientDimension_tendsToInfinity (fiberRank d)
  degree_polynomial := by
    have hdegree := PolynomiallyBounded.lifted_degree_enlarged_dimension
      base.degree_polynomial (Fintype.card (Fiber d)) (fiberRank d)
    rcases hdegree with ⟨C, k, r₀, hr₀⟩
    refine ⟨C, k, r₀, fun r hr ↦ ?_⟩
    change (coordinateLiftAt base d hd r).cayley.degree ≤
      C * ((base.ambientDimension r + fiberRank d) + 1) ^ k
    rw [coordinateLift_degree]
    exact hr₀ r hr

/-- The unconditional higher-dimensional family obtained from a
two-dimensional base family after the complete proof of Theorem 5.1. -/
noncomputable def toHigherDimensionalFamilyFromBase
    (d : ℕ) (hd : 3 ≤ d)
    (base : TwoDimensionalFamily (1 / (d : ℝ))) :
    HigherDimensionalFamily d :=
  toHigherDimensionalFamily d hd base
    (provedLiftedCodimensionTwoBound d hd base)

end HigherDimensionalAssembly

end HDXLean
