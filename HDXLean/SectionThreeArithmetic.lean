import HDXLean.SpectralArithmetic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Arithmetic for the relation-matrix spectrum

This file checks the substitutions made in Section 3.3.  With field size
`q^2`, direction-set size `(q - 2)g`, and lower distance `(q - 5)g`, the
upper Fourier endpoint simplifies to the rational function displayed in the
paper.  Both upper candidates and the absolute value of the negative endpoint
are then strictly below `4 / (q - 2)` for `q ≥ 8`.
-/

namespace HDXLean

/-- Substitution of the size and distance supplied by Lemma 3.2 into the
constant-vector Fourier eigenvalue. -/
theorem sectionThree_direction_endpoint_eq {q g : ℝ}
    (hq : 8 ≤ q) (hg : 0 < g) :
    1 - q ^ 2 * ((q - 5) * g) /
        ((q ^ 2 - 1) * ((q - 2) * g)) =
      (3 * q ^ 2 - q + 2) / ((q ^ 2 - 1) * (q - 2)) := by
  have hqSubTwo : q - 2 ≠ 0 := by linarith
  have hqSqSubOne : q ^ 2 - 1 ≠ 0 := by nlinarith
  have hgNe : g ≠ 0 := ne_of_gt hg
  field_simp
  ring

/-- The small positive eigenvalue from the zero-sum part of a Fourier block
is also below the paper's common target. -/
theorem sectionThree_small_positive_lt_four_div_sub_two {q : ℝ}
    (hq : 8 ≤ q) :
    1 / ((q ^ 2 - 2) * (q ^ 2 - 1)) < 4 / (q - 2) := by
  have hqSubTwo : 0 < q - 2 := by linarith
  have hqSqSubTwo : 0 < q ^ 2 - 2 := by nlinarith
  have hqSqSubOne : 1 < q ^ 2 - 1 := by nlinarith
  have hden : 0 < (q ^ 2 - 2) * (q ^ 2 - 1) :=
    mul_pos hqSqSubTwo (by linarith)
  apply (div_lt_div_iff₀ hden hqSubTwo).2
  nlinarith [mul_pos hqSqSubTwo (sub_pos.mpr hqSqSubOne)]

/-- Both possible upper endpoints in (3.2), after the Section 3.3
substitution, are below `4/(q-2)`. -/
theorem sectionThree_max_upper_lt_four_div_sub_two {q : ℝ}
    (hq : 8 ≤ q) :
    max
        ((3 * q ^ 2 - q + 2) / ((q ^ 2 - 1) * (q - 2)))
        (1 / ((q ^ 2 - 2) * (q ^ 2 - 1))) <
      4 / (q - 2) := by
  exact max_lt
    (sectionThree_ratio_lt_four_div_sub_two hq)
    (sectionThree_small_positive_lt_four_div_sub_two hq)

/-- The interval in (3.2) is contained in the symmetric interval with radius
`4/(q-2)` after the Section 3.3 parameter substitution. -/
theorem sectionThree_interval_abs_lt_four_div_sub_two {q mu : ℝ}
    (hq : 8 ≤ q)
    (hlower : -1 / (q ^ 2 - 2) ≤ mu)
    (hupper : mu ≤ max
      ((3 * q ^ 2 - q + 2) / ((q ^ 2 - 1) * (q - 2)))
      (1 / ((q ^ 2 - 2) * (q ^ 2 - 1)))) :
    |mu| < 4 / (q - 2) := by
  rw [abs_lt]
  constructor
  · have hnegative := sectionThree_one_div_sq_sub_two_lt_four_div_sub_two hq
    calc
      -(4 / (q - 2)) < -(1 / (q ^ 2 - 2)) := neg_lt_neg hnegative
      _ = -1 / (q ^ 2 - 2) := by ring
      _ ≤ mu := hlower
  · exact hupper.trans_lt (sectionThree_max_upper_lt_four_div_sub_two hq)

/-- A spectral choice strictly larger than `4/(q-2)` bounds every number in
the interval (3.2). -/
theorem sectionThree_interval_abs_le_target {q mu lambda : ℝ}
    (hq : 8 ≤ q)
    (hchoice : 4 / (q - 2) < lambda)
    (hlower : -1 / (q ^ 2 - 2) ≤ mu)
    (hupper : mu ≤ max
      ((3 * q ^ 2 - q + 2) / ((q ^ 2 - 1) * (q - 2)))
      (1 / ((q ^ 2 - 2) * (q ^ 2 - 1)))) :
    |mu| ≤ lambda := by
  exact (sectionThree_interval_abs_lt_four_div_sub_two hq hlower hupper).le.trans
    hchoice.le

end HDXLean
