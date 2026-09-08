import HDXLean.WeightedLiftCodimensionTwo
import HDXLean.WeightedLiftOneFiberBridge
import HDXLean.WeightedLiftThreeFiberBridge
import HDXLean.WeightedLiftTwoFiberBridge

/-!
# Concrete occupancy rows for the weighted dimension lift

This module collects the three conditioned-link calculations in the exact
form consumed by `codimensionTwoBound_of_occupancy_cases`.  The three-fiber
row is unconditional here; the one- and two-fiber rows are added alongside
their concrete weight bridges.
-/

namespace HDXLean

namespace WeightedLift

variable {Gamma A : Type*}
  [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma] [DecidableEq Gamma]
  [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A]

/-- The `r(F)=3` row of the paper's conditioned-link table, packaged for the
exhaustive occupancy reduction. -/
theorem occupancyCaseBound_three
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) :
    OccupancyCaseBound (A := A) base d hdimension hd hm 3 := by
  intro F hF hFcard hsupport
  exact concreteThreeLink_twoSidedSpectralBound
    base d hdimension hd hm F hF hFcard hsupport

/-- With the one- and three-fiber rows now discharged, the complete
codimension-two estimate reduces to the concrete two-fiber row alone. -/
theorem codimensionTwoBound_of_twoFiberCase
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A)
    (hbase : base.complex.CodimensionTwoBound (1 / (d : ℝ)))
    (htwo : OccupancyCaseBound (A := A) base d hdimension hd hm 2) :
    MeasuredComplex.CodimensionTwoBound
      (measuredComplex (A := A) base.complex d hdimension (by omega) hm)
      (1 / (d : ℝ)) := by
  exact codimensionTwoBound_of_occupancy_cases
    (A := A) base d hdimension hd hm
      (occupancyCaseBound_one base d hdimension hd hm hbase)
      htwo
      (occupancyCaseBound_three base d hdimension hd hm)

/-- The full local-expansion conclusion of Theorem 5.1, reduced only to the
two-fiber edge bridge. -/
theorem localSpectralExpansion_of_twoFiberCase
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A)
    (hbase : base.complex.IsTwoSidedLocalSpectralExpander (1 / (d : ℝ)))
    (htwo : OccupancyCaseBound (A := A) base d hdimension hd hm 2) :
    MeasuredComplex.IsTwoSidedLocalSpectralExpander
      (measuredComplex (A := A) base.complex d hdimension (by omega) hm)
      (1 / (d : ℝ)) := by
  exact localSpectralExpansion_of_occupancy_cases
    (A := A) base d hdimension hd hm hbase.1
      (occupancyCaseBound_one base d hdimension hd hm hbase.2)
      htwo
      (occupancyCaseBound_three base d hdimension hd hm)

/-- Complete codimension-two conclusion of Theorem 5.1. -/
theorem lifted_codimensionTwoBound
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A)
    (hbase : base.complex.CodimensionTwoBound (1 / (d : ℝ))) :
    MeasuredComplex.CodimensionTwoBound
      (measuredComplex (A := A) base.complex d hdimension (by omega) hm)
      (1 / (d : ℝ)) := by
  exact codimensionTwoBound_of_twoFiberCase
    (A := A) base d hdimension hd hm hbase
      (occupancyCaseBound_two base d hdimension hd hm)

/-- Full weighted dimension-lift theorem (Theorem 5.1): a two-dimensional
two-sided local spectral expander lifts to dimension `d`, with bound `1/d`. -/
theorem weightedDimensionLift_localSpectralExpansion
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A)
    (hbase : base.complex.IsTwoSidedLocalSpectralExpander (1 / (d : ℝ))) :
    MeasuredComplex.IsTwoSidedLocalSpectralExpander
      (measuredComplex (A := A) base.complex d hdimension (by omega) hm)
      (1 / (d : ℝ)) := by
  exact localSpectralExpansion_of_twoFiberCase
    (A := A) base d hdimension hd hm hbase
      (occupancyCaseBound_two base d hdimension hd hm)

end WeightedLift

end HDXLean
