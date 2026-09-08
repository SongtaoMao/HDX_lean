import HDXLean.GolowichProduct
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-! Arithmetic of the newly added global-gap formula.
The identification of the actual graph gap with this formula is Golowich's
cited Theorem 18 plus the skeleton-walk identification, not asserted here. -/
namespace HDXLean.GolowichProduct
open scoped BigOperators

noncomputable def harmonicFactor (d : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (2 * d), (1 : ℝ) / ((j : ℝ) + 1)

theorem harmonicFactor_pos (d : ℕ) (hd : 1 ≤ d) : 0 < harmonicFactor d := by
  have hterm : (1 : ℝ) ≤ harmonicFactor d := by
    have h := Finset.single_le_sum
      (f := fun j : ℕ ↦ (1 : ℝ) / ((j : ℝ) + 1))
      (fun j _ ↦ by positivity)
      (show 0 ∈ Finset.range (2 * d) by simp; omega)
    simpa [harmonicFactor] using h
  linarith

noncomputable def productGlobalGap (d k : ℕ) : ℝ :=
  2 / ((k : ℝ) * harmonicFactor d)

/-- The formula in the revised Section 5 tends to zero as cube dimension
increases, in an explicit epsilon-threshold formulation. -/
theorem productGlobalGap_tendsToZero (d : ℕ) (hd : 2 ≤ d) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      0 < productGlobalGap d k ∧ productGlobalGap d k < ε := by
  intro ε hε
  have hH := harmonicFactor_pos d (by omega)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / (ε * harmonicFactor d) + 1)
  refine ⟨N, fun k hk ↦ ?_⟩
  have hkR : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hquot : 0 < 2 / (ε * harmonicFactor d) := div_pos (by norm_num) (mul_pos hε hH)
  have hkpos : (0 : ℝ) < k := by linarith
  have hsmall : 2 / (ε * harmonicFactor d) < (k : ℝ) := by linarith
  have hcross := (div_lt_iff₀ (mul_pos hε hH)).mp hsmall
  constructor
  · exact div_pos (by norm_num) (mul_pos hkpos hH)
  · apply (div_lt_iff₀ (mul_pos hkpos hH)).mpr
    nlinarith

end HDXLean.GolowichProduct
