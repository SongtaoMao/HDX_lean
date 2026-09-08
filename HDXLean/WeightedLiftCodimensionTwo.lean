import HDXLean.WeightedLiftOccupancy

/-!
# Exhaustive reduction of the lifted codimension-two estimate

The conditioned-link calculation in Section 5 splits according to the number
of occupied base fibers.  This file records that this is an exhaustive split,
so the three concrete spectral calculations can be plugged into the global
codimension-two statement without any further combinatorics.
-/

namespace HDXLean

namespace WeightedLift

variable {Gamma A : Type*}
  [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma] [DecidableEq Gamma]
  [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A]

/-- The local estimate restricted to codimension-two faces meeting exactly
`r` base fibers. -/
def OccupancyCaseBound
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (r : ℕ) : Prop :=
  ∀ F : Finset (Gamma × A),
    (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F →
    F.card + 1 = d →
    (projectionSupport F).card = r →
    WeightedGraph.TwoSidedSpectralBound
      ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F)
      (1 / (d : ℝ))

/-- The three rows of the conditioned-link table imply the complete
codimension-two spectral bound for the lift. -/
theorem codimensionTwoBound_of_occupancy_cases
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A)
    (hone : OccupancyCaseBound (A := A) base d hdimension hd hm 1)
    (htwo : OccupancyCaseBound (A := A) base d hdimension hd hm 2)
    (hthree : OccupancyCaseBound (A := A) base d hdimension hd hm 3) :
    MeasuredComplex.CodimensionTwoBound
      (measuredComplex (A := A) base.complex d hdimension (by omega) hm)
      (1 / (d : ℝ)) := by
  intro F hF hcodim
  rcases codimensionTwo_projectionSupport_trichotomy
      (A := A) base d hdimension hd hm F hF hcodim with
    honeSupport | htwoSupport | hthreeSupport
  · exact hone F hF hcodim honeSupport
  · exact htwo F hF hcodim htwoSupport
  · exact hthree F hF hcodim hthreeSupport

/-- Once the three conditioned-link calculations are available, all of
Theorem 5.1's local-expansion conclusion follows: positive-dimensional links
are connected by the combinatorial lift argument, and codimension-two links
are controlled by the exhaustive occupancy split. -/
theorem localSpectralExpansion_of_occupancy_cases
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A)
    (hbaseConnected : base.complex.PositiveLinksConnected)
    (hone : OccupancyCaseBound (A := A) base d hdimension hd hm 1)
    (htwo : OccupancyCaseBound (A := A) base d hdimension hd hm 2)
    (hthree : OccupancyCaseBound (A := A) base d hdimension hd hm 3) :
    MeasuredComplex.IsTwoSidedLocalSpectralExpander
      (measuredComplex (A := A) base.complex d hdimension (by omega) hm)
      (1 / (d : ℝ)) := by
  refine ⟨?_, codimensionTwoBound_of_occupancy_cases
    (A := A) base d hdimension hd hm hone htwo hthree⟩
  exact lifted_positiveLinksConnected (A := A) base d hdimension
    (by omega) hm hbaseConnected

end WeightedLift

end HDXLean
