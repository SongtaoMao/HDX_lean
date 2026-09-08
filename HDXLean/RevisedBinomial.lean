import HDXLean.Asymptotics
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.NormNum

/-! Elementary, fully checked growth bound for the revised Section 4.
We use fixed blocks and Vandermonde instead of an asymptotic Stirling formula.
The deliberately generous threshold has no effect on the infinite family. -/
namespace HDXLean

theorem choose_product_le (m n i j : ℕ) :
    m.choose i * n.choose j ≤ (m + n).choose (i + j) := by
  rw [Nat.add_choose_eq]
  exact Finset.single_le_sum (f := fun ij : ℕ × ℕ ↦ m.choose ij.1 * n.choose ij.2)
    (fun _ _ ↦ Nat.zero_le _)
    (show (i, j) ∈ Finset.antidiagonal (i + j) by simp)

set_option maxRecDepth 2048 in
theorem revised_binomial_block : 2 ^ 270 ≤ Nat.choose 300 100 := by
  rw [Nat.choose_eq_factorial_div_factorial (by omega : 100 ≤ 300)]
  norm_num [Nat.factorial, pow_succ]

theorem revised_binomial_blocks (b : ℕ) :
    2 ^ (270 * b) ≤ Nat.choose (300 * b) (100 * b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    calc
      2 ^ (270 * (b + 1)) = 2 ^ (270 * b) * 2 ^ 270 := by
        rw [Nat.mul_add, Nat.mul_one, pow_add]
      _ ≤ Nat.choose (300 * b) (100 * b) * Nat.choose 300 100 :=
        Nat.mul_le_mul ih revised_binomial_block
      _ ≤ Nat.choose (300 * b + 300) (100 * b + 100) := choose_product_le _ _ _ _
      _ = _ := by simp only [Nat.mul_add, Nat.mul_one]

theorem revised_binomial_lower (k : ℕ) :
    2 ^ (270 * (k / 100)) ≤ Nat.choose (3 * k) k := by
  have hrem : 1 ≤ Nat.choose (3 * (k % 100)) (k % 100) :=
    Nat.choose_pos (by omega)
  calc
    2 ^ (270 * (k / 100)) ≤ Nat.choose (300 * (k / 100)) (100 * (k / 100)) :=
      revised_binomial_blocks _
    _ ≤ Nat.choose (300 * (k / 100)) (100 * (k / 100)) *
        Nat.choose (3 * (k % 100)) (k % 100) := by
      simpa using Nat.mul_le_mul_left
        (Nat.choose (300 * (k / 100)) (100 * (k / 100))) hrem
    _ ≤ Nat.choose (300 * (k / 100) + 3 * (k % 100))
        (100 * (k / 100) + k % 100) := choose_product_le _ _ _ _
    _ = Nat.choose (3 * k) k := by
      congr 1 <;> omega

/-- An integer ceiling bound, hence stronger than the paper's real power
`2^((2g+1)/3)`, for all sufficiently large genus. -/
theorem revised_genus_binomial_lower {g : ℕ} (hg : 32400 ≤ g) :
    2 ^ ((2 * g + 3) / 3) ≤ Nat.choose (3 * (g / 4)) (g / 4) := by
  apply le_trans (Nat.pow_le_pow_right (by omega : 0 < 2) ?_)
    (revised_binomial_lower (g / 4))
  omega

end HDXLean
