import HDXLean.TwoDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Two-dimensional assembly with arbitrary finite matrix indices

The original `LemmaTwoThreeCertificate` uses `Fin` for every row and column
index.  Concrete relation matrices have more informative dependent index
types.  This module keeps those types, together with their finiteness and
decidable-equality data, all the way to the cited relation compiler.
-/

namespace HDXLean

/-- Binary rank of a finite matrix, defined as the dimension of the range of
its matrix-vector linear map. -/
noncomputable def binaryMatrixRank {R C : Type*} [Fintype R] [Fintype C]
    (H : BinaryMatrix R C) : ℕ :=
  Module.finrank F₂ (LinearMap.range (RelationMatrix.linearMap H))

/-- Lemma 2.3 data with arbitrary finite row and column types at each level.

The cardinality fields connect the intrinsic index types to the numerical
formulas in the paper.  The spectral certificate includes row distinctness,
weight three, positive constant column weight, and row-code distance at least
three. -/
structure IndexedLemmaTwoThreeCertificate (lambda : ℝ) where
  h : ℕ
  q : ℕ
  q_eq : q = 2 ^ h
  q_at_least_eight : 8 ≤ q
  q_spectral_choice : 4 / ((q : ℝ) - 2) < lambda
  t : ℕ → ℕ
  Row : ℕ → Type
  Column : ℕ → Type
  rowFintype : ∀ r, Fintype (Row r)
  rowDecidableEq : ∀ r, DecidableEq (Row r)
  columnFintype : ∀ r, Fintype (Column r)
  columnDecidableEq : ∀ r, DecidableEq (Column r)
  rowCount : ℕ → ℕ
  columnCount : ℕ → ℕ
  rowCount_eq_card : ∀ r, rowCount r = @Fintype.card (Row r) (rowFintype r)
  columnCount_eq_card : ∀ r,
    columnCount r = @Fintype.card (Column r) (columnFintype r)
  rho : ℕ → ℕ
  ambientDimension : ℕ → ℕ
  matrix : (r : ℕ) → BinaryMatrix (Row r) (Column r)
  columnCount_formula : ∀ r,
    columnCount r = (q ^ 2 - 1) * (q ^ 2) ^ (t r)
  rowCount_formula : ∀ r,
    3 * rowCount r = rho r * columnCount r
  nullity_eq : ∀ r,
    @RelationMatrix.nullity (Row r) (Column r)
      (columnFintype r) (matrix r) =
        ambientDimension r
  t_tendsToInfinity : TendsToInfinity t
  rho_linear_in_t : LinearBounded rho t
  ambientDimension_tendsToInfinity : TendsToInfinity ambientDimension
  degree_polynomial : PolynomiallyBounded columnCount ambientDimension
  rho_logarithmic : LogarithmicallyBounded rho ambientDimension
  spectralCertificate : ∀ r,
    @RelationMatrix.SpectralCertificate (Row r) (Column r)
      (rowFintype r) (columnFintype r) (columnDecidableEq r)
      (matrix r) (rho r) lambda

namespace IndexedLemmaTwoThreeCertificate

local instance indexedRowFintype {lambda : ℝ}
    (certificate : IndexedLemmaTwoThreeCertificate lambda) (r : ℕ) :
    Fintype (certificate.Row r) :=
  certificate.rowFintype r

local instance indexedRowDecidableEq {lambda : ℝ}
    (certificate : IndexedLemmaTwoThreeCertificate lambda) (r : ℕ) :
    DecidableEq (certificate.Row r) :=
  certificate.rowDecidableEq r

local instance indexedColumnFintype {lambda : ℝ}
    (certificate : IndexedLemmaTwoThreeCertificate lambda) (r : ℕ) :
    Fintype (certificate.Column r) :=
  certificate.columnFintype r

local instance indexedColumnDecidableEq {lambda : ℝ}
    (certificate : IndexedLemmaTwoThreeCertificate lambda) (r : ℕ) :
    DecidableEq (certificate.Column r) :=
  certificate.columnDecidableEq r

/-- Positivity is derived from the existing matrix-size formula. -/
theorem columnCount_pos {lambda : ℝ}
    (certificate : IndexedLemmaTwoThreeCertificate lambda) (r : ℕ) :
    0 < certificate.columnCount r := by
  rw [certificate.columnCount_formula]
  have hq : 0 < certificate.q := lt_of_lt_of_le (by norm_num) certificate.q_at_least_eight
  have hq2 : 1 < certificate.q ^ 2 := by
    exact one_lt_pow₀ (lt_of_lt_of_le (by norm_num) certificate.q_at_least_eight)
      (by decide)
  exact Nat.mul_pos (Nat.sub_pos_of_lt hq2) (pow_pos (pow_pos hq _) _)

/-- The intrinsic column index is nonempty at every level. -/
theorem column_nonempty {lambda : ℝ}
    (certificate : IndexedLemmaTwoThreeCertificate lambda) (r : ℕ) :
    Nonempty (certificate.Column r) := by
  apply Fintype.card_pos_iff.mp
  rw [← certificate.columnCount_eq_card]
  exact certificate.columnCount_pos r

/-- Binary rank of the matrix at a fixed level. -/
noncomputable def matrixRank {lambda : ℝ}
    (certificate : IndexedLemmaTwoThreeCertificate lambda) (r : ℕ) : ℕ :=
  binaryMatrixRank (certificate.matrix r)

/-- The distance conclusion can be projected without unpacking the full
spectral certificate. -/
theorem rowDistance {lambda : ℝ}
    (certificate : IndexedLemmaTwoThreeCertificate lambda) (r : ℕ) :
    @RowDistanceAtLeastThree (certificate.Row r) (certificate.Column r)
      (certificate.columnFintype r) (certificate.matrix r) :=
  (certificate.spectralCertificate r).rowDistance

/-- The cited compiler applied directly to the intrinsic row and column
types at one level. -/
noncomputable def compiledOutput {lambda : ℝ}
    (certificate : IndexedLemmaTwoThreeCertificate lambda)
    (literature : RelationCompiler.LiteratureInput) (r : ℕ) :
    RelationCompiler.Output (certificate.matrix r) (certificate.rho r) lambda := by
  letI := certificate.column_nonempty r
  exact literature.compileCertificate
    (certificate.matrix r) (certificate.rho r) lambda
    (certificate.spectralCertificate r)

/-- Section 2.5 with arbitrary finite matrix index types. -/
noncomputable def toTwoDimensionalFamily {lambda : ℝ}
    (certificate : IndexedLemmaTwoThreeCertificate lambda)
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
    rw [(output r).degree_eq,
      ← certificate.columnCount_eq_card r, hdim]
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

/-- Logical theorem form of the indexed assembly. -/
theorem nonempty_twoDimensionalFamily {lambda : ℝ}
    (certificate : IndexedLemmaTwoThreeCertificate lambda)
    (literature : RelationCompiler.LiteratureInput) :
    Nonempty (TwoDimensionalFamily lambda) :=
  ⟨certificate.toTwoDimensionalFamily literature⟩

end IndexedLemmaTwoThreeCertificate

end HDXLean
