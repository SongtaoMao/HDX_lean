import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Scalar weights in the dimension lift

This file checks the cancellation identity for
`g_m(t) = 1 / (t * choose m t)` used when conditioning the lifted top-face
measure in Section 5.1.
-/

namespace HDXLean

namespace WeightedLift

/-- The per-fiber subset weight from equation (5.1). -/
noncomputable def g (m t : ℕ) : ℝ :=
  1 / ((t : ℝ) * (Nat.choose m t : ℝ))

theorem g_nonneg (m t : ℕ) : 0 ≤ g m t := by
  simp only [g, one_div]
  positivity

theorem g_pos {m t : ℕ} (ht : 0 < t) (htm : t ≤ m) :
    0 < g m t := by
  have hchoose : 0 < Nat.choose m t := Nat.choose_pos htm
  simp only [g, one_div]
  positivity

/-- The exact cancellation identity stated immediately before (5.1). -/
theorem g_succ_div_g {m t : ℕ} (ht : 0 < t) (htm : t < m) :
    g m (t + 1) / g m t = (t : ℝ) / ((m : ℝ) - t) := by
  have htLe : t ≤ m := htm.le
  have hchoose : Nat.choose m t ≠ 0 := (Nat.choose_pos htLe).ne'
  have htail : m - t ≠ 0 := (Nat.sub_pos_of_lt htm).ne'
  have hrelationNat := Nat.choose_succ_right_eq m t
  have hrelation :
      (Nat.choose m (t + 1) : ℝ) * (t + 1 : ℕ) =
        (Nat.choose m t : ℝ) * (m - t : ℕ) := by
    exact_mod_cast hrelationNat
  rw [g, g]
  have htReal : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have hchooseReal : (Nat.choose m t : ℝ) ≠ 0 := by exact_mod_cast hchoose
  have htailReal : ((m - t : ℕ) : ℝ) ≠ 0 := by exact_mod_cast htail
  have hsub : (m : ℝ) - t = (m - t : ℕ) := by
    exact (Nat.cast_sub htLe).symm
  rw [hsub]
  have hsuccDen :
      ((t + 1 : ℕ) : ℝ) * (Nat.choose m (t + 1) : ℝ) =
        (Nat.choose m t : ℝ) * (m - t : ℕ) := by
    nlinarith [hrelation]
  rw [hsuccDen]
  field_simp

/-- The support-size correction from Section 5.1. -/
noncomputable def gamma (d supportSize : ℕ) : ℝ :=
  if supportSize = 1 then ((d : ℝ) - 1) / d else 1

theorem gamma_nonneg (d supportSize : ℕ) : 0 ≤ gamma d supportSize := by
  unfold gamma
  split_ifs
  · by_cases hd : d = 0
    · simp [hd]
    · have hdReal : (1 : ℝ) ≤ d := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hd)
      positivity
  · norm_num

theorem gamma_pos {d supportSize : ℕ} (hd : 2 ≤ d)
    (_hsupport : 1 ≤ supportSize) : 0 < gamma d supportSize := by
  unfold gamma
  split_ifs
  · have hdReal : (2 : ℝ) ≤ d := by exact_mod_cast hd
    apply div_pos
    · linarith
    · linarith
  · norm_num

end WeightedLift

end HDXLean
