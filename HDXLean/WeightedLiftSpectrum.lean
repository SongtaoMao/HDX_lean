import HDXLean.SpectralArithmetic

/-!
# Numerical spectrum of the weighted dimension lift

Theorem 5.1 lists every eigenvalue arising from its three conditioned-link
cases.  This file records that list as an inductive predicate and proves, with
all side conditions explicit, that every listed value has absolute value at
most `1 / d` when `d ≥ 3` and `m ≥ 2d`.

This is deliberately separate from the later structural theorem identifying
the spectrum of each concrete link with this table.  That separation exposes
the main omitted argument in the manuscript instead of hiding it inside a
numerical estimate.
-/

namespace HDXLean

namespace WeightedLift

/-- All nonstationary eigenvalue types displayed in the table on page 15.
The occupancy variables are real-valued here because only the resulting
inequalities are at issue; concrete link occupancies will be natural numbers
whose casts satisfy these hypotheses. -/
inductive TableEigenvalue (d m : ℕ) : ℝ → Prop
  | threeFiberQuotient : TableEigenvalue d m (1 / (d : ℝ))
  | threeFiberWithin (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ (d : ℝ) - 3) :
      TableEigenvalue d m
        (-(a + 1) / ((d : ℝ) * ((m : ℝ) - a - 1)))
  | twoFiberQuotientOne : TableEigenvalue d m (1 / ((d : ℝ) + 1))
  | twoFiberQuotientTwo :
      TableEigenvalue d m (1 / ((d : ℝ) * ((d : ℝ) + 1)))
  | twoFiberAcrossThird : TableEigenvalue d m (1 / (d : ℝ))
  | twoFiberOccupiedWithin (a : ℝ) (ha0 : 0 ≤ a)
      (ha : a ≤ (d : ℝ) - 2) :
      TableEigenvalue d m
        (-(a + 1) / (((d : ℝ) + 1) * ((m : ℝ) - a - 1)))
  | twoFiberThirdWithin :
      TableEigenvalue d m (-1 / ((d : ℝ) * ((m : ℝ) - 1)))
  | oneFiberZero : TableEigenvalue d m 0
  | oneFiberBase (theta : ℝ) (htheta : |theta| ≤ 1 / (d : ℝ)) :
      TableEigenvalue d m ((1 + theta) / ((d : ℝ) + 1))
  | oneFiberOccupiedWithin :
      TableEigenvalue d m
        (-((d : ℝ) - 1) / (((d : ℝ) + 1) * ((m : ℝ) - (d : ℝ))))
  | oneFiberOtherWithin :
      TableEigenvalue d m (-1 / (((d : ℝ) + 1) * ((m : ℝ) - 1)))

/-- Every eigenvalue type in the paper's lift table satisfies the claimed
`1/d` bound. -/
theorem tableEigenvalue_bound {d m : ℕ} (hd : 3 ≤ d) (hm : 2 * d ≤ m)
    {eigenvalue : ℝ} (hvalue : TableEigenvalue d m eigenvalue) :
    |eigenvalue| ≤ 1 / (d : ℝ) := by
  have hdReal : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hmReal : (2 : ℝ) * (d : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  cases hvalue with
  | threeFiberQuotient =>
      exact lift_quotient_one_div_bound hdReal
  | threeFiberWithin a ha0 ha =>
      exact lift_three_fiber_within_bound hdReal hmReal ha0 ha
  | twoFiberQuotientOne =>
      exact lift_quotient_one_div_add_one_bound hdReal
  | twoFiberQuotientTwo =>
      exact lift_quotient_one_div_mul_add_one_bound hdReal
  | twoFiberAcrossThird =>
      exact lift_quotient_one_div_bound hdReal
  | twoFiberOccupiedWithin a ha0 ha =>
      exact lift_two_fiber_occupied_within_bound hdReal hmReal ha0 ha
  | twoFiberThirdWithin =>
      simpa only [neg_div] using
        lift_two_fiber_third_within_bound hdReal hmReal
  | oneFiberZero =>
      simp
  | oneFiberBase theta htheta =>
      exact lift_base_link_eigenvalue_bound hdReal htheta
  | oneFiberOccupiedWithin =>
      simpa only [neg_div] using
        lift_one_fiber_occupied_within_bound hdReal hmReal
  | oneFiberOtherWithin =>
      simpa only [neg_div] using
        lift_one_fiber_other_within_bound hdReal hmReal

/-- The table is monotone in the target spectral parameter. -/
theorem tableEigenvalue_bound_of_one_div_le {d m : ℕ} (hd : 3 ≤ d)
    (hm : 2 * d ≤ m) {lambda eigenvalue : ℝ}
    (hlambda : 1 / (d : ℝ) ≤ lambda)
    (hvalue : TableEigenvalue d m eigenvalue) :
    |eigenvalue| ≤ lambda :=
  (tableEigenvalue_bound hd hm hvalue).trans hlambda

end WeightedLift

end HDXLean
