import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order

/-!
# Choosing the square-field parameter

This file verifies the first numerical step of Lemma 2.3: every positive
target `lambda` admits a power of two `q = 2^h ≥ 8` with
`4 / (q - 2) < lambda`.
-/

namespace HDXLean

/-- A power-of-two parameter satisfying the paper's spectral choice. -/
structure SpectralFieldChoice (lambda : ℝ) where
  h : ℕ
  q : ℕ
  h_at_least_three : 3 ≤ h
  q_eq : q = 2 ^ h
  q_at_least_eight : 8 ≤ q
  spectral_inequality : 4 / ((q : ℝ) - 2) < lambda

/-- Existence of the field-size choice used in Lemma 2.3. -/
noncomputable def spectralFieldWitness {lambda : ℝ} (hlambda : 0 < lambda) :
    SpectralFieldChoice lambda := by
  let hex : ∃ n : ℕ, 4 / lambda + 2 < n := exists_nat_gt (4 / lambda + 2)
  let n : ℕ := Classical.choose hex
  have hn : 4 / lambda + 2 < (n : ℝ) := Classical.choose_spec hex
  let h := max 3 n
  have hThree : 3 ≤ h := Nat.le_max_left _ _
  have hnLe : n ≤ h := Nat.le_max_right _ _
  have hLtPow : h < 2 ^ h := by exact Nat.lt_two_pow_self
  have hnLtPow : (n : ℝ) < (2 ^ h : ℕ) := by
    exact_mod_cast hnLe.trans_lt hLtPow
  have hBig : 4 / lambda + 2 < ((2 ^ h : ℕ) : ℝ) := hn.trans hnLtPow
  have hFourDiv : (0 : ℝ) < 4 / lambda := div_pos (by norm_num) hlambda
  have hDen : (0 : ℝ) < ((2 ^ h : ℕ) : ℝ) - 2 := by linarith
  have hCross : (4 : ℝ) < lambda * (((2 ^ h : ℕ) : ℝ) - 2) := by
    have hDiv : 4 / lambda < ((2 ^ h : ℕ) : ℝ) - 2 := by linarith
    have := (div_lt_iff₀ hlambda).mp hDiv
    nlinarith
  refine
    { h := h
      q := 2 ^ h
      h_at_least_three := hThree
      q_eq := rfl
      q_at_least_eight := ?_
      spectral_inequality := ?_ }
  · calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by omega) hThree
  · apply (div_lt_iff₀ hDen).2
    nlinarith

/-- Choose the least admissible binary exponent, as in the revised paper. -/
noncomputable def chooseSpectralField {lambda : ℝ} (hlambda : 0 < lambda) :
    SpectralFieldChoice lambda := by
  let w := spectralFieldWitness hlambda
  have hex : ∃ h : ℕ, 3 ≤ h ∧ 4 / ((2 ^ h : ℕ) - (2 : ℝ)) < lambda :=
    ⟨w.h, w.h_at_least_three, by simpa [w.q_eq] using w.spectral_inequality⟩
  exact
    { h := Nat.find hex
      q := 2 ^ Nat.find hex
      h_at_least_three := (Nat.find_spec hex).1
      q_eq := rfl
      q_at_least_eight := by
        exact (show 8 = 2 ^ 3 by norm_num) ▸
          Nat.pow_le_pow_right (by omega) (Nat.find_spec hex).1
      spectral_inequality := (Nat.find_spec hex).2 }

theorem chooseSpectralField_minimal {lambda : ℝ} (hlambda : 0 < lambda)
    (h : ℕ) (hh : 3 ≤ h) (hspectral : 4 / ((2 ^ h : ℕ) - (2 : ℝ)) < lambda) :
    (chooseSpectralField hlambda).h ≤ h := by
  exact Nat.find_min' _ ⟨hh, hspectral⟩

/-- An explicit logarithmic upper bound in any integer threshold exceeding
`4/lambda + 2`; in particular the least choice has logarithmic dependence on
the inverse target parameter. -/
theorem chooseSpectralField_log_bound {lambda : ℝ} (hlambda : 0 < lambda)
    (N : ℕ) (hN : 4 / lambda + 2 < (N : ℝ)) :
    (chooseSpectralField hlambda).h ≤ max 3 (Nat.log2 N + 1) := by
  apply chooseSpectralField_minimal hlambda _ (Nat.le_max_left _ _)
  have hpow : N < 2 ^ (max 3 (Nat.log2 N + 1)) := by
    have hlog : N < 2 ^ (Nat.log2 N + 1) := by
      simpa only [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) N
    exact hlog.trans_le
      (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
  have hpowR : (N : ℝ) < (2 ^ (max 3 (Nat.log2 N + 1)) : ℕ) := by
    exact_mod_cast hpow
  have hbig : 4 / lambda < (2 ^ (max 3 (Nat.log2 N + 1)) : ℕ) - (2 : ℝ) := by
    linarith
  have hpos : (0 : ℝ) < (2 ^ (max 3 (Nat.log2 N + 1)) : ℕ) - (2 : ℝ) :=
    (div_pos (by norm_num) hlambda).trans hbig
  apply (div_lt_iff₀ hpos).mpr
  have := (div_lt_iff₀ hlambda).mp hbig
  nlinarith

/-- Logical existence form. -/
theorem exists_spectralFieldChoice {lambda : ℝ} (hlambda : 0 < lambda) :
    Nonempty (SpectralFieldChoice lambda) :=
  ⟨chooseSpectralField hlambda⟩

end HDXLean
