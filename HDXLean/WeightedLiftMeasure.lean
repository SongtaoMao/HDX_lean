import HDXLean.WeightedLiftTopFaces
import HDXLean.WeightedLiftWeights
import Mathlib.Algebra.BigOperators.Field

/-!
# The top-face measure of the weighted dimension lift

This file implements equation (5.1) as a normalized finite sum over every
compatible parent triangle.  Consequently a lifted face with several parent
triangles receives every contribution, exactly as specified in the paper.
-/

namespace HDXLean

open scoped BigOperators

namespace WeightedLift

variable {Gamma A : Type*}
  [Fintype Gamma] [DecidableEq Gamma]
  [Fintype A] [DecidableEq A]

/-- The contribution of one compatible base triangle before global
normalization. -/
noncomputable def parentWeight (X : MeasuredComplex Gamma) (d : ℕ)
    (tau : Finset Gamma) (T : Finset (Gamma × A)) : ℝ :=
  X.topWeight tau * gamma d (occupiedSupport (A := A) tau T).card *
    ∏ x ∈ occupiedSupport (A := A) tau T, g (Fintype.card A) (occupancy T x)

/-- Equation (5.1) without its common normalizing factor. -/
noncomputable def rawTopWeight (X : MeasuredComplex Gamma) (d : ℕ)
    (T : Finset (Gamma × A)) : ℝ := by
  classical
  exact ∑ tau ∈ X.topFaces,
    if CompatibleParent (A := A) tau T then parentWeight (A := A) X d tau T else 0

/-- The explicit finite normalizer.  This is the `Z_d` of equation (5.1). -/
noncomputable def normalizer (X : MeasuredComplex Gamma) (d : ℕ) : ℝ :=
  ∑ T ∈ topFaces (A := A) X d, rawTopWeight (A := A) X d T

/-- The probability assigned to an individual lifted top face. -/
noncomputable def liftedTopWeight (X : MeasuredComplex Gamma) (d : ℕ)
    (T : Finset (Gamma × A)) : ℝ :=
  if T ∈ topFaces (A := A) X d then
    rawTopWeight (A := A) X d T / normalizer (A := A) X d
  else 0

/-- Every parent contribution is nonnegative. -/
theorem parentWeight_nonneg (X : MeasuredComplex Gamma) (d : ℕ)
    {tau : Finset Gamma} (htau : tau ∈ X.topFaces)
    (T : Finset (Gamma × A)) :
    0 ≤ parentWeight (A := A) X d tau T := by
  unfold parentWeight
  exact mul_nonneg
    (mul_nonneg (le_of_lt (X.topWeight_pos tau htau))
      (gamma_nonneg d (occupiedSupport (A := A) tau T).card))
    (Finset.prod_nonneg fun x hx ↦ g_nonneg (Fintype.card A) (occupancy T x))

/-- A compatible parent contributes strictly positive mass to a lifted top
face. -/
theorem parentWeight_pos (X : MeasuredComplex Gamma) (d : ℕ)
    (hd : 2 ≤ d) {tau : Finset Gamma} (htau : tau ∈ X.topFaces)
    {T : Finset (Gamma × A)} (hcard : T.card = d + 1)
    (hcompatible : CompatibleParent (A := A) tau T) :
    0 < parentWeight (A := A) X d tau T := by
  have hTnonempty : T.Nonempty := Finset.card_pos.mp (by omega)
  have hsupportNonempty :=
    occupiedSupport_nonempty (A := A) hcompatible hTnonempty
  have hsupport : 1 ≤ (occupiedSupport (A := A) tau T).card :=
    Finset.card_pos.mpr hsupportNonempty
  have hproduct :
      0 < ∏ x ∈ occupiedSupport (A := A) tau T,
        g (Fintype.card A) (occupancy T x) := by
    apply Finset.prod_pos
    intro x hx
    have hxPositive : 0 < occupancy T x :=
      (Finset.mem_filter.mp hx).2
    exact g_pos hxPositive (occupancy_le_card T x)
  unfold parentWeight
  exact mul_pos
    (mul_pos (X.topWeight_pos tau htau) (gamma_pos hd hsupport))
    hproduct

/-- The unnormalized mass is nonnegative on every set. -/
theorem rawTopWeight_nonneg (X : MeasuredComplex Gamma) (d : ℕ)
    (T : Finset (Gamma × A)) :
    0 ≤ rawTopWeight (A := A) X d T := by
  unfold rawTopWeight
  apply Finset.sum_nonneg
  intro tau htau
  split_ifs
  · exact parentWeight_nonneg X d htau T
  · exact le_rfl

/-- Every lifted top face has strictly positive unnormalized mass. -/
theorem rawTopWeight_pos (X : MeasuredComplex Gamma) (d : ℕ)
    (hd : 2 ≤ d) {T : Finset (Gamma × A)}
    (hT : T ∈ topFaces (A := A) X d) :
    0 < rawTopWeight (A := A) X d T := by
  obtain ⟨hcard, tau, htau, hcompatible⟩ := mem_topFaces.mp hT
  unfold rawTopWeight
  apply Finset.sum_pos'
  · intro tau' htau'
    split_ifs
    · exact parentWeight_nonneg X d htau' T
    · exact le_rfl
  · refine ⟨tau, htau, ?_⟩
    rw [if_pos hcompatible]
    exact parentWeight_pos X d hd htau hcard hcompatible

/-- The normalizer is strictly positive. -/
theorem normalizer_pos (X : MeasuredComplex Gamma) (d : ℕ)
    (hdimension : X.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) :
    0 < normalizer (A := A) X d := by
  obtain ⟨T, hT⟩ := topFaces_nonempty (A := A) X d hdimension (by omega) hm
  unfold normalizer
  apply Finset.sum_pos'
  · intro T' hT'
    exact rawTopWeight_nonneg X d _
  · exact ⟨T, hT, rawTopWeight_pos X d hd hT⟩

/-- Formula (5.1) for a top face. -/
theorem liftedTopWeight_eq (X : MeasuredComplex Gamma) (d : ℕ)
    {T : Finset (Gamma × A)} (hT : T ∈ topFaces (A := A) X d) :
    liftedTopWeight (A := A) X d T =
      rawTopWeight (A := A) X d T / normalizer (A := A) X d := by
  simp [liftedTopWeight, hT]

/-- The lifted top-face weights sum to one. -/
theorem liftedTopWeight_sum (X : MeasuredComplex Gamma) (d : ℕ)
    (hdimension : X.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) :
    ∑ T ∈ topFaces (A := A) X d, liftedTopWeight (A := A) X d T = 1 := by
  have hZ := normalizer_pos (A := A) X d hdimension hd hm
  calc
    ∑ T ∈ topFaces (A := A) X d, liftedTopWeight (A := A) X d T =
        ∑ T ∈ topFaces (A := A) X d,
          rawTopWeight (A := A) X d T / normalizer (A := A) X d := by
      apply Finset.sum_congr rfl
      intro T hT
      exact liftedTopWeight_eq X d hT
    _ = normalizer (A := A) X d / normalizer (A := A) X d := by
      rw [← Finset.sum_div]
      rfl
    _ = 1 := div_self hZ.ne'

/-- The measured simple pure complex underlying the weighted lift. -/
noncomputable def measuredComplex (X : MeasuredComplex Gamma) (d : ℕ)
    (hdimension : X.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) : MeasuredComplex (Gamma × A) where
  dim := d
  topFaces := topFaces (A := A) X d
  top_card := fun T hT ↦ topFace_card T hT
  topWeight := liftedTopWeight (A := A) X d
  topWeight_pos := fun T hT ↦ by
    rw [liftedTopWeight_eq X d hT]
    exact div_pos (rawTopWeight_pos X d hd hT)
      (normalizer_pos (A := A) X d hdimension hd hm)
  topWeight_zero := fun T hT ↦ by simp [liftedTopWeight, hT]
  topWeight_sum := liftedTopWeight_sum (A := A) X d hdimension hd hm

end WeightedLift

end HDXLean
