import HDXLean.SectionThreeAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Real-exponent statements matching the revised manuscript exactly. -/
namespace HDXLean

theorem third_rpow_le_ceiling (t : ℕ) :
    (2 : ℝ) ^ ((t : ℝ) / 3) ≤ (2 ^ ((t + 2) / 3) : ℕ) := by
  have ht : t ≤ 3 * ((t + 2) / 3) := by omega
  have htR : (t : ℝ) ≤ 3 * (((t + 2) / 3 : ℕ) : ℝ) := by exact_mod_cast ht
  calc
    (2 : ℝ) ^ ((t : ℝ) / 3) ≤ (2 : ℝ) ^ (((t + 2) / 3 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = (2 ^ ((t + 2) / 3) : ℕ) := by rw [Real.rpow_natCast]; norm_cast

namespace SectionThreeFamily
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  [CharP F 2] [Algebra F₂ F]

/-- Exact revised Lemma 2.3 lower bound, with real rather than natural division. -/
theorem revised_nullity_lower_real (P : SquareFieldParameters F)
    (family : Lemma32DirectionFamily P)
    (traceInput : FiniteFieldTrace.LiteratureInput F) (r : ℕ) :
    (2 * (P.h : ℝ)) * (2 : ℝ) ^ ((family.t r : ℝ) / 3) ≤
      (ambientDimension P family r : ℝ) := by
  have hn := revised_nullity_lower P family traceInput r
  have hnR : (2 * (P.h : ℝ)) * (2 ^ ((family.t r + 2) / 3) : ℕ) ≤
      (ambientDimension P family r : ℝ) := by exact_mod_cast hn
  exact (mul_le_mul_of_nonneg_left (third_rpow_le_ceiling (family.t r))
    (by positivity)).trans hnR

/-- Exact displayed degree bound, including its `2h` denominator. -/
theorem revised_degree_bound_real (P : SquareFieldParameters F)
    (family : Lemma32DirectionFamily P)
    (traceInput : FiniteFieldTrace.LiteratureInput F) (r : ℕ) :
    (Fintype.card (Column P family r) : ℝ) ≤
      ((P.q : ℝ) ^ 2 - 1) *
        ((ambientDimension P family r : ℝ) / (2 * (P.h : ℝ))) ^ (6 * P.h) := by
  have hh : (0 : ℝ) < 2 * (P.h : ℝ) := by exact_mod_cast (by have := P.h_pos; omega : 0 < 2 * P.h)
  have hn : (2 : ℝ) ^ ((family.t r : ℝ) / 3) ≤
      (ambientDimension P family r : ℝ) / (2 * (P.h : ℝ)) := by
    apply (le_div_iff₀ hh).mpr
    simpa [mul_comm] using revised_nullity_lower_real P family traceInput r
  have hq : (P.q : ℝ) = (2 : ℝ) ^ P.h := by exact_mod_cast P.q_eq_two_pow
  have hpower : ((P.q : ℝ) ^ 2) ^ family.t r =
      ((2 : ℝ) ^ ((family.t r : ℝ) / 3)) ^ (6 * P.h) := by
    rw [hq, ← pow_mul, ← pow_mul, ← Real.rpow_natCast,
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  have hq2 : (1 : ℕ) ≤ P.q ^ 2 := by have := P.q_ge_eight; nlinarith
  rw [columnCount_formula, Nat.cast_mul, Nat.cast_sub hq2, Nat.cast_pow,
    Nat.cast_one, Nat.cast_pow, Nat.cast_pow, hpower]
  apply mul_le_mul_of_nonneg_left
  · exact pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) hn _
  · have : (1 : ℝ) ≤ (P.q : ℝ) ^ 2 := by exact_mod_cast hq2
    linarith

end SectionThreeFamily
end HDXLean
