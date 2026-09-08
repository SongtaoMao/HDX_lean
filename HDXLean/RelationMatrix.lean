import HDXLean.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Binary relation matrices and their counting Gram graphs

The same `0/1` incidence array has two different roles in the paper. Its
kernel and row code are computed over `F₂`, whereas common-row multiplicities
are counted in `ℕ` and then coerced to `ℝ`. This file keeps those roles
separate at the type level.
-/

namespace HDXLean

open scoped BigOperators

namespace RelationMatrix

variable {R C : Type*} [Fintype R] [DecidableEq R]
  [Fintype C] [DecidableEq C]

/-- Matrix-vector multiplication over the binary field. -/
def apply (H : BinaryMatrix R C) (x : C → F₂) (r : R) : F₂ :=
  ∑ c : C, H r c * x c

/-- The binary incidence matrix as a linear map. -/
def linearMap (H : BinaryMatrix R C) : (C → F₂) →ₗ[F₂] (R → F₂) where
  toFun := RelationMatrix.apply H
  map_add' x y := by
    funext r
    simp [RelationMatrix.apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    funext r
    simp [RelationMatrix.apply, Finset.mul_sum, mul_left_comm]

/-- Binary kernel of an incidence matrix. -/
def kernel (H : BinaryMatrix R C) : Submodule F₂ (C → F₂) :=
  LinearMap.ker (linearMap H)

/-- Nullity over `F₂`. -/
noncomputable def nullity (H : BinaryMatrix R C) : ℕ :=
  Module.finrank F₂ (kernel H)

/-- Distinctness of the indexed rows. -/
def RowsDistinct (H : BinaryMatrix R C) : Prop :=
  Function.Injective fun r ↦ H r

/-- Every row has Hamming weight three. -/
def RowsHaveWeightThree (H : BinaryMatrix R C) : Prop :=
  ∀ r, (rowSupport H r).card = 3

/-- Every column has the same prescribed positive weight. -/
def ConstantColumnWeight (H : BinaryMatrix R C) (rho : ℕ) : Prop :=
  0 < rho ∧ ∀ c, columnWeight H c = rho

/-- No two columns occur together in more than one row. -/
def PairMultiplicityAtMostOne (H : BinaryMatrix R C) : Prop :=
  ∀ c c', c ≠ c' → countingGram H c c' ≤ 1

/-- The normalized counting-Gram graph. -/
noncomputable def normalizedGramGraph (H : BinaryMatrix R C) (rho : ℕ)
    (hrho : 0 < rho) : WeightedGraph C :=
  (gramGraph H).scale ((2 * (rho : ℝ))⁻¹) (by positivity)

/-- Complete hypotheses of the cited row-relation compiler. -/
structure CompilerHypotheses (H : BinaryMatrix R C) (rho : ℕ) : Prop where
  rowsDistinct : RowsDistinct H
  rowsHaveWeightThree : RowsHaveWeightThree H
  constantColumnWeight : ConstantColumnWeight H rho
  rowDistance : RowDistanceAtLeastThree H

omit [DecidableEq R] [DecidableEq C] in
/-- With a nonempty column set, positive column weight forces a row to exist.
This implication fails for the old empty-column domain. -/
theorem CompilerHypotheses.row_nonempty [Nonempty C]
    {H : BinaryMatrix R C} {rho : ℕ} (hyp : CompilerHypotheses H rho) :
    Nonempty R := by
  obtain ⟨c⟩ := ‹Nonempty C›
  have hweight : 0 < columnWeight H c := by
    rw [hyp.constantColumnWeight.2 c]
    exact hyp.constantColumnWeight.1
  obtain ⟨r, _⟩ := Finset.card_pos.mp hweight
  exact ⟨r⟩

omit [DecidableEq R] [DecidableEq C] in
/-- The corrected domain has at least three columns, since one row has
weight three. No additional numerical premise is necessary. -/
theorem CompilerHypotheses.three_le_card_columns [Nonempty C]
    {H : BinaryMatrix R C} {rho : ℕ} (hyp : CompilerHypotheses H rho) :
    3 ≤ Fintype.card C := by
  obtain ⟨r⟩ := hyp.row_nonempty
  rw [← hyp.rowsHaveWeightThree r]
  exact Finset.card_le_univ _

/-- Additional conclusions established by the paper's internal construction. -/
structure SpectralCertificate (H : BinaryMatrix R C) (rho : ℕ)
    (lambda : ℝ) : Prop extends CompilerHypotheses H rho where
  pairMultiplicity : PairMultiplicityAtMostOne H
  gramConnected : (normalizedGramGraph H rho constantColumnWeight.1).Connected
  gramBound :
    (normalizedGramGraph H rho constantColumnWeight.1).TwoSidedSpectralBound lambda

end RelationMatrix

/-! ## Output interface of the cited Golowich compiler -/

namespace RelationCompiler

variable {R C : Type*} [Fintype R] [DecidableEq R]
  [Fintype C] [DecidableEq C]

/-- Output required of the relation-matrix construction, already transported
from the quotient vector space to binary coordinates. The complete adapter
to this interface remains a separate formalization obligation. -/
structure Output (H : BinaryMatrix R C) (rho : ℕ) (lambda : ℝ) where
  ambientDimension : ℕ
  complex : CayleyComplex (V := Fin ambientDimension → F₂)
  dimension_eq : complex.complex.dim = 2
  unweighted : complex.complex.IsUnweighted
  degree_eq : complex.cayley.degree = Fintype.card C
  ambientDimension_eq : ambientDimension = RelationMatrix.nullity H
  edgeCodegree_eq : ∀ x y,
    x ≠ y → complex.complex.IsFace {x, y} →
      complex.complex.edgeCodegree x y = 2 * rho
  localExpansion : complex.complex.IsTwoSidedLocalSpectralExpander lambda

/-- Relation-compiler assumption boundary, motivated by `[Gol23, Lemmas 45,
76, 77]`. It includes coordinate, measure, and counting adapters not literally
stated by those lemmas, so it must not be described as an exact cited theorem.

The column type is required to be nonempty. Without this restriction, the
empty matrix satisfies all other premises but the promised pure
two-dimensional complex cannot exist. See the historical regression in
`Checks/FinalAudit20260908.lean`. -/
structure LiteratureInput : Type 1 where
  compile : ∀ {R C : Type} [Fintype R] [DecidableEq R]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (H : BinaryMatrix R C) (rho : ℕ) (lambda : ℝ)
      (hyp : RelationMatrix.CompilerHypotheses H rho),
      WeightedGraph.IsTwoSidedSpectralExpander
          (RelationMatrix.normalizedGramGraph H rho hyp.constantColumnWeight.1) lambda →
      Output H rho lambda

/-- Apply the cited compiler directly to the stronger certificate produced by
the paper's internal relation-matrix construction. -/
def LiteratureInput.compileCertificate (input : LiteratureInput)
    {R₀ C₀ : Type} [Fintype R₀] [DecidableEq R₀]
    [Fintype C₀] [DecidableEq C₀] [Nonempty C₀]
    (H : BinaryMatrix R₀ C₀) (rho : ℕ) (lambda : ℝ)
    (certificate : RelationMatrix.SpectralCertificate H rho lambda) :
    Output H rho lambda :=
  input.compile H rho lambda certificate.toCompilerHypotheses
    ⟨certificate.gramConnected, certificate.gramBound⟩

end RelationCompiler

end HDXLean
