import HDXLean.Families
import HDXLean.RelationMatrix

/-!
# The two-dimensional construction

This module formalizes the composition in Section 2.5.  A
`LemmaTwoThreeCertificate` records the matrix family supplied by Lemma 2.3 and
the elementary asymptotic consequences of its numerical bounds.  The only
literature input used to construct complexes is `RelationCompiler.LiteratureInput`.

The certificate fields corresponding directly to Lemma 2.3 are:

* `h`, `q`, `q_eq`, `q_at_least_eight`, and `q_spectral_choice`, recording the
  fixed field-size choice;
* `t`, `rowCount`, `columnCount`, `rho`, and `matrix`, with `Fin` row and column
  indices;
* `columnCount_formula` and `rowCount_formula`, recording
  `M_r = (q^2 - 1)(q^2)^(t_r)` and `3 R_r = rho_r M_r` without natural-number
  division;
* `nullity_eq`, identifying `n_r` exactly with the binary nullity;
* `t_tendsToInfinity`, `rho_linear_in_t`, and `spectralCertificate`, which
  package the qualitative and matrix conclusions of Lemma 2.3.

The fields `ambientDimension_tendsToInfinity`, `degree_polynomial`, and
`rho_logarithmic` record the elementary numerical consequences derived in
Section 2.5 from Lemma 2.3's nullity lower bound.  The Cayley edge codegree is
not included as a field: the compiler proves that it is exactly `2 * rho`, and
the proof below derives its logarithmic bound with the doubled constant.
-/

namespace HDXLean

/-- Auditable input data for the matrix family of Lemma 2.3, together with the
three numerical consequences of its nullity estimate used in Section 2.5. -/
structure LemmaTwoThreeCertificate (lambda : ℝ) where
  h : ℕ
  q : ℕ
  q_eq : q = 2 ^ h
  q_at_least_eight : 8 ≤ q
  q_spectral_choice : 4 / ((q : ℝ) - 2) < lambda
  t : ℕ → ℕ
  rowCount : ℕ → ℕ
  columnCount : ℕ → ℕ
  rho : ℕ → ℕ
  ambientDimension : ℕ → ℕ
  matrix : (r : ℕ) →
    BinaryMatrix (Fin (rowCount r)) (Fin (columnCount r))
  columnCount_formula : ∀ r,
    columnCount r = (q ^ 2 - 1) * (q ^ 2) ^ (t r)
  rowCount_formula : ∀ r,
    3 * rowCount r = rho r * columnCount r
  nullity_eq : ∀ r,
    RelationMatrix.nullity (matrix r) = ambientDimension r
  t_tendsToInfinity : TendsToInfinity t
  rho_linear_in_t : LinearBounded rho t
  ambientDimension_tendsToInfinity : TendsToInfinity ambientDimension
  degree_polynomial : PolynomiallyBounded columnCount ambientDimension
  rho_logarithmic : LogarithmicallyBounded rho ambientDimension
  spectralCertificate : ∀ r,
    RelationMatrix.SpectralCertificate (matrix r) (rho r) lambda

namespace LemmaTwoThreeCertificate

/-- Every level has columns: this follows from the existing count formula
and field-size bound, not from an additional construction assumption. -/
theorem columnCount_pos {lambda : ℝ}
    (certificate : LemmaTwoThreeCertificate lambda) (r : ℕ) :
    0 < certificate.columnCount r := by
  rw [certificate.columnCount_formula]
  have hq : 0 < certificate.q := lt_of_lt_of_le (by norm_num) certificate.q_at_least_eight
  have hq2 : 1 < certificate.q ^ 2 := by
    exact one_lt_pow₀ (lt_of_lt_of_le (by norm_num) certificate.q_at_least_eight)
      (by decide)
  exact Nat.mul_pos (Nat.sub_pos_of_lt hq2) (pow_pos (pow_pos hq _) _)

/-- The cited compiler applied levelwise to the certified relation matrices. -/
noncomputable def compiledOutput {lambda : ℝ}
    (certificate : LemmaTwoThreeCertificate lambda)
    (literature : RelationCompiler.LiteratureInput) (r : ℕ) :
    RelationCompiler.Output (certificate.matrix r) (certificate.rho r) lambda := by
  letI : Nonempty (Fin (certificate.columnCount r)) :=
    ⟨⟨0, certificate.columnCount_pos r⟩⟩
  exact literature.compileCertificate (certificate.matrix r) (certificate.rho r) lambda
    (certificate.spectralCertificate r)

/-- Section 2.5: compile the Lemma 2.3 matrices into the family of Theorem 1.1. -/
noncomputable def toTwoDimensionalFamily {lambda : ℝ}
    (certificate : LemmaTwoThreeCertificate lambda)
    (literature : RelationCompiler.LiteratureInput) :
    TwoDimensionalFamily lambda := by
  let output := certificate.compiledOutput literature
  refine
    { ambientDimension := fun r ↦ (output r).ambientDimension
      complex := fun r ↦ (output r).complex
      dimension_eq := fun r ↦ (output r).dimension_eq
      unweighted := fun r ↦ (output r).unweighted
      localExpansion := fun r ↦ (output r).localExpansion
      ambientDimension_tendsToInfinity := ?_
      degree_polynomial := ?_
      edgeCodegree := fun r ↦ 2 * certificate.rho r
      edgeCodegree_eq := ?_
      edgeCodegree_logarithmic := ?_ }
  · intro B
    rcases certificate.ambientDimension_tendsToInfinity B with ⟨r₀, hr₀⟩
    refine ⟨r₀, fun r hr ↦ ?_⟩
    have hdim : (output r).ambientDimension = certificate.ambientDimension r :=
      (output r).ambientDimension_eq.trans (certificate.nullity_eq r)
    change B ≤ (output r).ambientDimension
    rw [hdim]
    exact hr₀ r hr
  · rcases certificate.degree_polynomial with ⟨C, k, r₀, hr₀⟩
    refine ⟨C, k, r₀, fun r hr ↦ ?_⟩
    have hdim : (output r).ambientDimension = certificate.ambientDimension r :=
      (output r).ambientDimension_eq.trans (certificate.nullity_eq r)
    change (output r).complex.cayley.degree ≤
      C * ((output r).ambientDimension + 1) ^ k
    rw [(output r).degree_eq, Fintype.card_fin, hdim]
    exact hr₀ r hr
  · intro r x y hxy hface
    exact (output r).edgeCodegree_eq x y hxy hface
  · rcases certificate.rho_logarithmic with ⟨C, r₀, hr₀⟩
    refine ⟨2 * C, r₀, fun r hr ↦ ?_⟩
    have hdim : (output r).ambientDimension = certificate.ambientDimension r :=
      (output r).ambientDimension_eq.trans (certificate.nullity_eq r)
    change 2 * certificate.rho r ≤
      (2 * C) * (Nat.log2 (output r).ambientDimension + 1)
    rw [hdim]
    calc
      2 * certificate.rho r ≤
          2 * (C * (Nat.log2 (certificate.ambientDimension r) + 1)) :=
        Nat.mul_le_mul_left 2 (hr₀ r hr)
      _ = (2 * C) * (Nat.log2 (certificate.ambientDimension r) + 1) := by
        rw [Nat.mul_assoc]

/-- Logical theorem form of `toTwoDimensionalFamily`: Lemma 2.3 data and the
single cited compiler input imply the existence of the family in Theorem 1.1. -/
theorem nonempty_twoDimensionalFamily {lambda : ℝ}
    (certificate : LemmaTwoThreeCertificate lambda)
    (literature : RelationCompiler.LiteratureInput) :
    Nonempty (TwoDimensionalFamily lambda) :=
  ⟨certificate.toTwoDimensionalFamily literature⟩

end LemmaTwoThreeCertificate

end HDXLean
