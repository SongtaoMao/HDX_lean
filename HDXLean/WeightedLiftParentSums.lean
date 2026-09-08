import HDXLean.WeightedLiftMeasure
import HDXLean.WeightedLiftOccupancy

/-!
# Compatible-parent sums in the weighted lift

When a lifted face meets all three base fibers, its compatible parent triangle
is unique.  These lemmas collapse the parent sum in (5.1) to one summand and
are used by the concrete three-fiber link calculation.
-/

namespace HDXLean

namespace WeightedLift

variable {Gamma A : Type*}
  [Fintype Gamma] [DecidableEq Gamma]
  [Fintype A] [DecidableEq A]

/-- Projection support is contained in every compatible parent. -/
theorem projectionSupport_subset_of_compatible
    {tau : Finset Gamma} {F : Finset (Gamma × A)}
    (hcompatible : CompatibleParent (A := A) tau F) :
    projectionSupport F ⊆ tau := by
  intro x hx
  obtain ⟨a, ha⟩ := mem_projectionSupport.mp hx
  exact mem_fibersAbove.mp (hcompatible ha)

/-- A three-point projection support determines its three-point parent. -/
theorem compatibleParent_eq_projectionSupport_of_card_three
    {tau : Finset Gamma} {F : Finset (Gamma × A)}
    (htau : tau.card = 3)
    (hsupport : (projectionSupport F).card = 3)
    (hcompatible : CompatibleParent (A := A) tau F) :
    tau = projectionSupport F := by
  exact (Finset.eq_of_subset_of_card_le
    (projectionSupport_subset_of_compatible hcompatible)
    (by rw [htau, hsupport])).symm

/-- For a lifted top face meeting all three base fibers, equation (5.1) has
exactly one compatible-parent summand. -/
theorem rawTopWeight_eq_parentWeight_projectionSupport
    (X : MeasuredComplex Gamma) (d : ℕ) (hdimension : X.dim = 2)
    {T : Finset (Gamma × A)} (hT : T ∈ topFaces (A := A) X d)
    (hsupport : (projectionSupport T).card = 3) :
    rawTopWeight (A := A) X d T =
      parentWeight (A := A) X d (projectionSupport T) T := by
  obtain ⟨_hcard, tau, htau, hcompatible⟩ := mem_topFaces.mp hT
  have htauCard : tau.card = 3 := by
    simpa [hdimension] using X.top_card tau htau
  have hparent := compatibleParent_eq_projectionSupport_of_card_three
    (A := A) htauCard hsupport hcompatible
  subst tau
  unfold rawTopWeight
  rw [Finset.sum_eq_single (projectionSupport T)]
  · rw [if_pos hcompatible]
  · intro sigma hsigma hne
    by_cases hsigmaCompatible : CompatibleParent (A := A) sigma T
    · have hsigmaCard : sigma.card = 3 := by
        simpa [hdimension] using X.top_card sigma hsigma
      have heq := compatibleParent_eq_projectionSupport_of_card_three
        (A := A) hsigmaCard hsupport hsigmaCompatible
      exact (hne heq).elim
    · rw [if_neg hsigmaCompatible]
  · exact fun hnot ↦ (hnot htau).elim

end WeightedLift

end HDXLean
