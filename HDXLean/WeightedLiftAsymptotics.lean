import HDXLean.Asymptotics

/-!
# Asymptotics of the fixed-fiber dimension lift

For fixed fiber size `m = 2^r`, Theorem 5.1 replaces the base degree `s` by
`m (s + 1) - 1` and the ambient binary dimension `n` by `n + r`.  The lemmas
below verify the polynomial-growth claims used in Section 5.2.
-/

namespace HDXLean

namespace PolynomiallyBounded

/-- Enlarging the comparison sequence by a fixed additive constant preserves
a polynomial bound. -/
theorem mono_argument_add_const {f g : ℕ → ℕ}
    (h : PolynomiallyBounded f g) (c : ℕ) :
    PolynomiallyBounded f (fun r ↦ g r + c) := by
  rcases h with ⟨C, k, r₀, hr₀⟩
  refine ⟨C, k, r₀, fun r hr ↦ ?_⟩
  calc
    f r ≤ C * (g r + 1) ^ k := hr₀ r hr
    _ ≤ C * ((g r + c) + 1) ^ k := by
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_left (by omega) k

/-- Multiplying a degree by a fixed fiber size, adding the within-fiber
generators, and subtracting the forbidden zero generator preserves polynomial
growth. -/
theorem lifted_degree {degree ambientDimension : ℕ → ℕ}
    (hdegree : PolynomiallyBounded degree ambientDimension) (m : ℕ) :
    PolynomiallyBounded
      (fun r ↦ m * (degree r + 1) - 1) ambientDimension := by
  have hone : PolynomiallyBounded (fun _ ↦ 1) ambientDimension :=
    PolynomiallyBounded.const 1 ambientDimension
  have hadd : PolynomiallyBounded (fun r ↦ degree r + 1) ambientDimension :=
    PolynomiallyBounded.add hdegree hone
  have hmul : PolynomiallyBounded (fun r ↦ m * (degree r + 1)) ambientDimension :=
    PolynomiallyBounded.const_mul hadd m
  exact PolynomiallyBounded.of_eventually_le
    (Eventually.of_forall fun r ↦ Nat.sub_le _ _) hmul

/-- The same lifted degree is polynomial in the enlarged ambient dimension. -/
theorem lifted_degree_enlarged_dimension {degree ambientDimension : ℕ → ℕ}
    (hdegree : PolynomiallyBounded degree ambientDimension) (m extra : ℕ) :
    PolynomiallyBounded
      (fun r ↦ m * (degree r + 1) - 1)
      (fun r ↦ ambientDimension r + extra) :=
  (lifted_degree hdegree m).mono_argument_add_const extra

end PolynomiallyBounded

/-- Adding the fixed fiber dimension preserves divergence of the ambient
dimension. -/
theorem tendsToInfinity_liftedDimension {ambientDimension : ℕ → ℕ}
    (h : TendsToInfinity ambientDimension) (extra : ℕ) :
    TendsToInfinity (fun r ↦ ambientDimension r + extra) :=
  h.add_const extra

end HDXLean
