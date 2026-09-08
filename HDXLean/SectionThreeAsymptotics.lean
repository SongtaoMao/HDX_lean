import HDXLean.SectionThreeFamily
import HDXLean.SquareFieldDimension
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Asymptotics from the relation-matrix nullity bound

This file proves the elementary consequences at the end of Section 3.3.  The
natural-number quotient in the formal version of Lemma 3.2 is handled with an
explicit remainder factor.  Thus the binary nullity tends to infinity, the
number of columns is polynomial in the nullity, and the common column weight
is logarithmic in the nullity.
-/

namespace HDXLean

namespace SectionThreeFamily

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  [CharP F 2] [Algebra F₂ F]
variable (P : SquareFieldParameters F)

omit [DecidableEq F] [CharP F 2] [Algebra F₂ F] in
private theorem qSquare_pos : 0 < P.q ^ 2 := by
  exact pow_pos P.q_pos _

omit [DecidableEq F] [CharP F 2] [Algebra F₂ F] in
private theorem blockSize_pos : 0 < 7 * P.h := by
  exact P.seven_mul_h_pos

/-- The exponential affine-function lower bound injects into the binary
kernel, even without evaluating the binary extension degree exactly. -/
theorem power_le_ambientDimension
    (family : Lemma32DirectionFamily P)
    (traceInput : FiniteFieldTrace.LiteratureInput F) (r : ℕ) :
    (P.q ^ 2) ^ (family.t r / (7 * P.h)) ≤
      ambientDimension P family r := by
  have hfieldFinrank : 1 ≤ Module.finrank F₂ F := by
    exact Module.finrank_pos
  have hinject := AffineRelationKernel.finrank_mul_finrank_le_nullity
    traceInput (family.directions r)
  calc
    (P.q ^ 2) ^ (family.t r / (7 * P.h)) ≤
        Module.finrank F (affineFunctions F (family.directions r)) :=
      family.affineDimensionLower r
    _ = 1 * Module.finrank F (affineFunctions F (family.directions r)) := by
      simp
    _ ≤ Module.finrank F₂ F *
        Module.finrank F (affineFunctions F (family.directions r)) :=
      Nat.mul_le_mul_right _ hfieldFinrank
    _ ≤ ambientDimension P family r := hinject

/-- The binary nullities tend to infinity. -/
theorem ambientDimension_tendsToInfinity
    (family : Lemma32DirectionFamily P)
    (traceInput : FiniteFieldTrace.LiteratureInput F) :
    TendsToInfinity (ambientDimension P family) := by
  intro B
  let k := 7 * P.h
  rcases family.t_tendsToInfinity (k * B) with ⟨r₀, ht⟩
  refine ⟨r₀, fun r hr ↦ ?_⟩
  have hk : 0 < k := by simpa [k] using blockSize_pos P
  have hexponent : B ≤ family.t r / k :=
    (Nat.le_div_iff_mul_le hk).2 (by
      simpa [Nat.mul_comm] using ht r hr)
  have htwoBase : 2 ≤ P.q ^ 2 := by
    have hq : 8 ≤ P.q := P.q_ge_eight
    nlinarith
  calc
    B ≤ 2 ^ B := Nat.le_of_lt B.lt_two_pow_self
    _ ≤ (P.q ^ 2) ^ B := Nat.pow_le_pow_left htwoBase B
    _ ≤ (P.q ^ 2) ^ (family.t r / k) :=
      Nat.pow_le_pow_right (qSquare_pos P) hexponent
    _ ≤ ambientDimension P family r := by
      simpa [k] using power_le_ambientDimension P family traceInput r

/-- A quotient/remainder estimate used to turn `Q^t` into a fixed power of
`Q^(t/k)`. -/
theorem power_le_remainder_factor (Q t k : ℕ) (hQ : 0 < Q) (hk : 0 < k) :
    Q ^ t ≤ Q ^ k * (Q ^ (t / k)) ^ k := by
  have ht : t ≤ k * (t / k + 1) := (Nat.lt_mul_div_succ t hk).le
  calc
    Q ^ t ≤ Q ^ (k * (t / k + 1)) :=
      Nat.pow_le_pow_right hQ ht
    _ = Q ^ k * (Q ^ (t / k)) ^ k := by
      rw [show k * (t / k + 1) = (t / k) * k + k by ring,
        pow_add, pow_mul]
      ac_rfl

/-- The revised, ceiling-rounded nullity estimate.  The ceiling makes this
stronger than the real-exponent statement in the current Lemma 2.3. -/
theorem revised_nullity_lower
    (family : Lemma32DirectionFamily P)
    (traceInput : FiniteFieldTrace.LiteratureInput F) (r : ℕ) :
    (2 * P.h) * 2 ^ ((family.t r + 2) / 3) ≤ ambientDimension P family r := by
  exact (Nat.mul_le_mul_left (2 * P.h) (family.affineDimensionLower_ceiling r)).trans
    (AffineRelationKernel.two_mul_h_mul_affineFinrank_le_nullity P traceInput
      (family.directions r))

/-- The improved exponent `6h` follows internally from the revised bound. -/
theorem degree_bound_six_h
    (family : Lemma32DirectionFamily P)
    (traceInput : FiniteFieldTrace.LiteratureInput F) (r : ℕ) :
    Fintype.card (Column P family r) ≤
      (P.q ^ 2 - 1) * (ambientDimension P family r) ^ (6 * P.h) := by
  have hlower : 2 ^ ((family.t r + 2) / 3) ≤ ambientDimension P family r := by
    exact (Nat.le_mul_of_pos_left _ (by have := P.h_pos; omega)).trans
      (revised_nullity_lower P family traceInput r)
  rw [columnCount_formula]
  apply Nat.mul_le_mul_left
  calc
    (P.q ^ 2) ^ family.t r = 2 ^ (2 * P.h * family.t r) := by
      rw [P.q_eq_two_pow, ← pow_mul, ← pow_mul]
      congr 1
      ring
    _ ≤ 2 ^ (((family.t r + 2) / 3) * (6 * P.h)) := by
      apply Nat.pow_le_pow_right (by omega)
      have ht : family.t r ≤ 3 * ((family.t r + 2) / 3) := by omega
      have := Nat.mul_le_mul_left (2 * P.h) ht
      nlinarith
    _ = (2 ^ ((family.t r + 2) / 3)) ^ (6 * P.h) := by rw [pow_mul]
    _ ≤ (ambientDimension P family r) ^ (6 * P.h) := Nat.pow_le_pow_left hlower _

/-- The number of columns is polynomial with the revised exponent `6h`. -/
theorem degree_polynomial
    (family : Lemma32DirectionFamily P)
    (traceInput : FiniteFieldTrace.LiteratureInput F) :
    PolynomiallyBounded
      (fun r ↦ Fintype.card (Column P family r))
      (ambientDimension P family) := by
  refine ⟨P.q ^ 2 - 1, 6 * P.h, Eventually.of_forall fun r ↦ ?_⟩
  exact (degree_bound_six_h P family traceInput r).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_add_right _ 1) _))

/-- The quotient exponent is bounded by the binary logarithm of the nullity. -/
theorem quotient_le_log2_ambientDimension
    (family : Lemma32DirectionFamily P)
    (traceInput : FiniteFieldTrace.LiteratureInput F) (r : ℕ) :
    family.t r / (7 * P.h) ≤ Nat.log2 (ambientDimension P family r) := by
  let e := family.t r / (7 * P.h)
  have hbase : 2 ≤ P.q ^ 2 := by
    have hq : 8 ≤ P.q := P.q_ge_eight
    nlinarith
  have htwo : 2 ^ e ≤ (P.q ^ 2) ^ e := Nat.pow_le_pow_left hbase e
  have hlower := power_le_ambientDimension P family traceInput r
  have hpow : 2 ^ e ≤ ambientDimension P family r := by
    exact htwo.trans (by simpa [e] using hlower)
  have hn : ambientDimension P family r ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos e) hpow)
  exact (Nat.le_log2 hn).2 hpow

/-- The direction parameter itself is linear in the binary logarithm of the
matrix nullity. -/
theorem t_logarithmic
    (family : Lemma32DirectionFamily P)
    (traceInput : FiniteFieldTrace.LiteratureInput F) :
    LogarithmicallyBounded family.t (ambientDimension P family) := by
  let k := 7 * P.h
  refine ⟨k, Eventually.of_forall fun r ↦ ?_⟩
  have hk : 0 < k := by simpa [k] using blockSize_pos P
  calc
    family.t r ≤ k * (family.t r / k + 1) :=
      (Nat.lt_mul_div_succ (family.t r) hk).le
    _ ≤ k * (Nat.log2 (ambientDimension P family r) + 1) :=
      Nat.mul_le_mul_left k (Nat.add_le_add_right (by
        simpa [k] using quotient_le_log2_ambientDimension P family traceInput r) 1)

/-- The exact column weight is logarithmic in matrix nullity. -/
theorem rho_logarithmic
    (family : Lemma32DirectionFamily P)
    (traceInput : FiniteFieldTrace.LiteratureInput F) :
    LogarithmicallyBounded (rho P family) (ambientDimension P family) := by
  rcases rho_linear_in_t P family with ⟨C, r₀, hrho⟩
  rcases t_logarithmic P family traceInput with ⟨k, r₁, ht⟩
  refine ⟨C * (k + 1), max r₀ r₁, fun r hr ↦ ?_⟩
  let L := Nat.log2 (ambientDimension P family r)
  have ht' : family.t r ≤ k * (L + 1) := by
    simpa [L] using ht r (le_trans (Nat.le_max_right r₀ r₁) hr)
  have hone : 1 ≤ L + 1 := Nat.succ_le_succ (Nat.zero_le L)
  calc
    rho P family r ≤ C * (family.t r + 1) :=
      hrho r (le_trans (Nat.le_max_left r₀ r₁) hr)
    _ ≤ C * (k * (L + 1) + 1) :=
      Nat.mul_le_mul_left C (Nat.add_le_add_right ht' 1)
    _ ≤ C * ((k + 1) * (L + 1)) := by
      apply Nat.mul_le_mul_left
      calc
        k * (L + 1) + 1 ≤ k * (L + 1) + (L + 1) :=
          Nat.add_le_add_left hone _
        _ = (k + 1) * (L + 1) := by rw [Nat.add_mul, one_mul]
    _ = (C * (k + 1)) * (L + 1) := by rw [Nat.mul_assoc]

/-- All three asymptotic fields required by `SectionThreeFamily` follow from
the internally proved nullity estimate. -/
theorem asymptoticCertificate
    (family : Lemma32DirectionFamily P)
    (traceInput : FiniteFieldTrace.LiteratureInput F) :
    AsymptoticCertificate P family where
  ambientDimension_tendsToInfinity :=
    ambientDimension_tendsToInfinity P family traceInput
  degree_polynomial := degree_polynomial P family traceInput
  rho_logarithmic := rho_logarithmic P family traceInput

end SectionThreeFamily

end HDXLean
