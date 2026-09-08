import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Spectral arithmetic

This file isolates the elementary real inequalities used in the spectral estimates in Sections 3
and 5 of the paper.  Denominator positivity is made explicit in each proof.
-/

namespace HDXLean

section RelationMatrix

/-- The main upper-endpoint estimate used in the proof of Lemma 2.3. -/
theorem sectionThree_ratio_lt_four_div_sub_two {q : ℝ} (hq : 8 ≤ q) :
    (3 * q ^ 2 - q + 2) / ((q ^ 2 - 1) * (q - 2)) < 4 / (q - 2) := by
  have hqSubTwo : 0 < q - 2 := by linarith
  have hqSqSubOne : 0 < q ^ 2 - 1 := by
    have hprod : 0 < (q - 1) * (q + 1) := mul_pos (by linarith) (by linarith)
    nlinarith
  have hden : 0 < (q ^ 2 - 1) * (q - 2) := mul_pos hqSqSubOne hqSubTwo
  apply (div_lt_div_iff₀ hden hqSubTwo).2
  have hfactor : 0 < (q - 2) * (q - 2) * (q + 3) :=
    mul_pos (mul_pos hqSubTwo hqSubTwo) (by linarith)
  nlinarith

/-- The negative-endpoint estimate used in the proof of Lemma 2.3. -/
theorem sectionThree_one_div_sq_sub_two_lt_four_div_sub_two {q : ℝ} (hq : 8 ≤ q) :
    1 / (q ^ 2 - 2) < 4 / (q - 2) := by
  have hqSubTwo : 0 < q - 2 := by linarith
  have hqSqSubTwo : 0 < q ^ 2 - 2 := by
    have hprod : 0 < (q - 2) * (q + 2) := mul_pos hqSubTwo (by linarith)
    nlinarith
  apply (div_lt_div_iff₀ hqSqSubTwo hqSubTwo).2
  have hfactor : 0 < (q - 2) * (4 * q + 7) :=
    mul_pos hqSubTwo (by linarith)
  nlinarith

end RelationMatrix

section WeightedLift

/-- The quotient eigenvalue `1 / d`, including the between-third-fibers eigenvalue, is admissible. -/
theorem lift_quotient_one_div_bound {d : ℝ} (hd : 3 ≤ d) : |1 / d| ≤ 1 / d := by
  have hdPos : 0 < d := by linarith
  rw [abs_of_pos (one_div_pos.mpr hdPos)]

/-- The quotient eigenvalue `1 / (d + 1)` is bounded by `1 / d`. -/
theorem lift_quotient_one_div_add_one_bound {d : ℝ} (hd : 3 ≤ d) :
    |1 / (d + 1)| ≤ 1 / d := by
  have hdPos : 0 < d := by linarith
  have hdAddOnePos : 0 < d + 1 := by linarith
  rw [abs_of_pos (one_div_pos.mpr hdAddOnePos)]
  apply (div_le_div_iff₀ hdAddOnePos hdPos).2
  nlinarith

/-- The quotient eigenvalue `1 / (d * (d + 1))` is bounded by `1 / d`. -/
theorem lift_quotient_one_div_mul_add_one_bound {d : ℝ} (hd : 3 ≤ d) :
    |1 / (d * (d + 1))| ≤ 1 / d := by
  have hdPos : 0 < d := by linarith
  have hdAddOnePos : 0 < d + 1 := by linarith
  have hdenPos : 0 < d * (d + 1) := mul_pos hdPos hdAddOnePos
  rw [abs_of_pos (one_div_pos.mpr hdenPos)]
  apply (div_le_div_iff₀ hdenPos hdPos).2
  have hcross : d * 1 ≤ d * (d + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hdPos.le
  simpa [mul_comm] using hcross

/-- The eigenvalues inherited from a base vertex link remain bounded by `1 / d`. -/
theorem lift_base_link_eigenvalue_bound {d theta : ℝ} (hd : 3 ≤ d)
    (htheta : |theta| ≤ 1 / d) : |(1 + theta) / (d + 1)| ≤ 1 / d := by
  have hdPos : 0 < d := by linarith
  have hdAddOnePos : 0 < d + 1 := by linarith
  rw [abs_div, abs_of_pos hdAddOnePos, div_le_iff₀ hdAddOnePos]
  have hadd : |1 + theta| ≤ 1 + |theta| := by
    simpa using abs_add_le (1 : ℝ) theta
  calc
    |1 + theta| ≤ 1 + |theta| := hadd
    _ ≤ 1 + 1 / d := add_le_add (le_refl 1) htheta
    _ = (1 / d) * (d + 1) := by field_simp [ne_of_gt hdPos]

/-- A common reduction for all negative within-fiber eigenvalues. -/
private theorem abs_neg_div_le_one_div {x denominator d : ℝ} (hx : 0 ≤ x)
    (hdenominator : 0 < denominator) (hd : 0 < d) (hcross : d * x ≤ denominator) :
    |(-x) / denominator| ≤ 1 / d := by
  rw [abs_div, abs_neg, abs_of_nonneg hx, abs_of_pos hdenominator]
  apply (div_le_div_iff₀ hdenominator hd).2
  simpa [mul_comm] using hcross

/-- Within-fiber bound when the conditioned face meets all three base fibers. -/
theorem lift_three_fiber_within_bound {d m a : ℝ} (hd : 3 ≤ d) (hm : 2 * d ≤ m)
    (haNonneg : 0 ≤ a) (ha : a ≤ d - 3) :
    |(-(a + 1)) / (d * (m - a - 1))| ≤ 1 / d := by
  have hdPos : 0 < d := by linarith
  have htailPos : 0 < m - a - 1 := by linarith
  have hcompare : a + 1 ≤ m - a - 1 := by linarith
  have hcross : d * (a + 1) ≤ d * (m - a - 1) :=
    mul_le_mul_of_nonneg_left hcompare hdPos.le
  exact abs_neg_div_le_one_div (by linarith) (mul_pos hdPos htailPos) hdPos hcross

/-- Within-fiber bound for either occupied fiber when the conditioned face meets two fibers. -/
theorem lift_two_fiber_occupied_within_bound {d m a : ℝ} (hd : 3 ≤ d)
    (hm : 2 * d ≤ m) (haNonneg : 0 ≤ a) (ha : a ≤ d - 2) :
    |(-(a + 1)) / ((d + 1) * (m - a - 1))| ≤ 1 / d := by
  have hdPos : 0 < d := by linarith
  have hdAddOneNonneg : 0 ≤ d + 1 := by linarith
  have htailPos : 0 < m - a - 1 := by linarith
  have hnumLe : a + 1 ≤ d - 1 := by linarith
  have htailGe : d + 1 ≤ m - a - 1 := by linarith
  have hleft : d * (a + 1) ≤ d * (d - 1) :=
    mul_le_mul_of_nonneg_left hnumLe hdPos.le
  have hmiddle : d * (d - 1) ≤ (d + 1) * (d + 1) := by nlinarith
  have hright : (d + 1) * (d + 1) ≤ (d + 1) * (m - a - 1) :=
    mul_le_mul_of_nonneg_left htailGe hdAddOneNonneg
  have hcross : d * (a + 1) ≤ (d + 1) * (m - a - 1) :=
    hleft.trans (hmiddle.trans hright)
  exact abs_neg_div_le_one_div (by linarith) (mul_pos (by linarith) htailPos) hdPos hcross

/-- Within-fiber bound for a possible third fiber in the two-fiber case. -/
theorem lift_two_fiber_third_within_bound {d m : ℝ} (hd : 3 ≤ d) (hm : 2 * d ≤ m) :
    |(-1 : ℝ) / (d * (m - 1))| ≤ 1 / d := by
  have hdPos : 0 < d := by linarith
  have htailPos : 0 < m - 1 := by linarith
  have htail : 1 ≤ m - 1 := by linarith
  have hcross : d * 1 ≤ d * (m - 1) :=
    mul_le_mul_of_nonneg_left htail hdPos.le
  exact abs_neg_div_le_one_div (by norm_num) (mul_pos hdPos htailPos) hdPos hcross

/-- Within-fiber bound for the occupied base fiber in the one-fiber case. -/
theorem lift_one_fiber_occupied_within_bound {d m : ℝ} (hd : 3 ≤ d)
    (hm : 2 * d ≤ m) :
    |(-(d - 1)) / ((d + 1) * (m - d))| ≤ 1 / d := by
  have hdPos : 0 < d := by linarith
  have hdAddOneNonneg : 0 ≤ d + 1 := by linarith
  have htailPos : 0 < m - d := by linarith
  have htail : d ≤ m - d := by linarith
  have hmiddle : d * (d - 1) ≤ (d + 1) * d := by nlinarith
  have hright : (d + 1) * d ≤ (d + 1) * (m - d) :=
    mul_le_mul_of_nonneg_left htail hdAddOneNonneg
  have hcross : d * (d - 1) ≤ (d + 1) * (m - d) := hmiddle.trans hright
  exact abs_neg_div_le_one_div (by linarith) (mul_pos (by linarith) htailPos) hdPos hcross

/-- Within-fiber bound for every other fiber in the one-fiber case. -/
theorem lift_one_fiber_other_within_bound {d m : ℝ} (hd : 3 ≤ d)
    (hm : 2 * d ≤ m) :
    |(-1 : ℝ) / ((d + 1) * (m - 1))| ≤ 1 / d := by
  have hdPos : 0 < d := by linarith
  have hdAddOneNonneg : 0 ≤ d + 1 := by linarith
  have htailPos : 0 < m - 1 := by linarith
  have htail : 1 ≤ m - 1 := by linarith
  have hleft : d * 1 ≤ (d + 1) * 1 := by linarith
  have hright : (d + 1) * 1 ≤ (d + 1) * (m - 1) :=
    mul_le_mul_of_nonneg_left htail hdAddOneNonneg
  have hcross : d * 1 ≤ (d + 1) * (m - 1) := hleft.trans hright
  exact abs_neg_div_le_one_div (by norm_num) (mul_pos (by linarith) htailPos) hdPos hcross

end WeightedLift

end HDXLean
