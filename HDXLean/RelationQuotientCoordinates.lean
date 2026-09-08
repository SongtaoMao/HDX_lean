import HDXLean.RelationTriangleComplex
import HDXLean.Relabeling
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Binary coordinates for the actual relation quotient

The quotient by the row code has dimension equal to the binary matrix
nullity. This follows internally from row-rank equality and rank--nullity;
it is not part of a cited compiler output. A linear equivalence then moves
the actual measured quotient triangle complex to the paper's literal
coordinate space, preserving dimension, uniform measure, and Cayley degree.
-/
namespace HDXLean.RelationQuotient

variable {R C : Type*} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

omit [Fintype R] [DecidableEq R] in
/-- The project's binary matrix action is mathlib's matrix-vector action. -/
theorem linearMap_eq_mulVecLin (H : BinaryMatrix R C) :
    RelationMatrix.linearMap H = H.mulVecLin := by
  ext x r
  rfl

omit [DecidableEq R] [DecidableEq C] in
/-- The row-code dimension is the matrix rank. No row-distance or
nonemptiness hypotheses are needed for this finite-dimensional identity. -/
theorem finrank_rowCode (H : BinaryMatrix R C) :
    Module.finrank F₂ (rowCode H) = H.rank := by
  have he : rowCode H = Submodule.span F₂ (Set.range H.row) := rfl
  rw [he]
  exact H.rank_eq_finrank_span_row.symm

/-- Quotient dimension equals kernel dimension, including degenerate
matrices. Nonempty-column hypotheses are needed for the triangle complex,
not for this rank--nullity identity. -/
theorem finrank_ambient (H : BinaryMatrix R C) :
    Module.finrank F₂ (Ambient H) = RelationMatrix.nullity H := by
  have hquot := (rowCode H).finrank_quotient_add_finrank
  have hker := LinearMap.finrank_range_add_finrank_ker (RelationMatrix.linearMap H)
  have hrange : Module.finrank F₂ (LinearMap.range (RelationMatrix.linearMap H)) =
      H.rank := by rw [linearMap_eq_mulVecLin]; rfl
  rw [finrank_rowCode] at hquot
  rw [hrange] at hker
  change H.rank + RelationMatrix.nullity H = _ at hker
  change Module.finrank F₂ (Ambient H) + H.rank = _ at hquot
  omega

/-- A basis choice in the quotient gives an actual linear equivalence to
`F₂^(nullity H)`. This is non-algorithmic, as allowed by the formalized scope. -/
noncomputable def coordinates (H : BinaryMatrix R C) :
    Ambient H ≃ₗ[F₂] (Fin (RelationMatrix.nullity H) → F₂) :=
  LinearEquiv.ofFinrankEq (R := F₂) (Ambient H)
    (Fin (RelationMatrix.nullity H) → F₂) (by
      rw [finrank_ambient]
      simp)

/-- In particular, the quotient has exactly the asserted number of binary
vertices, rather than merely an abstract dimension certificate. -/
theorem card_ambient (H : BinaryMatrix R C) :
    Fintype.card (Ambient H) = 2 ^ RelationMatrix.nullity H := by
  rw [Fintype.card_congr (coordinates H).toEquiv]
  simp [F₂]

end HDXLean.RelationQuotient

namespace HDXLean.MeasuredComplex

variable {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]

/-- A vertex bijection preserves uniform weight on the actual distinct
top faces. This is not an assertion about row/translation multiplicities. -/
theorem isUnweighted_relabel (X : MeasuredComplex V) (e : V ≃ W)
    (h : X.IsUnweighted) : (X.relabel e).IsUnweighted := by
  intro T hT
  rw [relabel_topWeight, h _ ((mem_relabel_topFaces_iff X e T).mp hT)]
  change (X.topFaces.card : ℝ)⁻¹ =
    ((X.topFaces.map e.finsetCongr.toEmbedding).card : ℝ)⁻¹
  rw [Finset.card_map]

end HDXLean.MeasuredComplex

namespace HDXLean.RelationQuotient

variable {R C : Type*} [Fintype R] [DecidableEq R]
  [Fintype C] [DecidableEq C] [Nonempty C]

/-- The corrected compiler hypotheses force enough quotient vertices for
triangles. In particular, the actual coordinate dimension cannot be zero or
one; this conclusion is derived rather than appended to the input record. -/
theorem two_le_nullity (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) : 2 ≤ RelationMatrix.nullity H := by
  have hgen := Fintype.card_le_of_injective (generator H)
    (generator_injective H hyp.rowDistance)
  rw [card_ambient] at hgen
  have hthree := hyp.three_le_card_columns
  by_contra h
  have hn : RelationMatrix.nullity H ≤ 1 := by omega
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
  norm_num at hpow
  omega

/-- The actual quotient triangle complex, now on binary coordinates of
dimension `nullity H`. No compiler output is assumed. -/
noncomputable def coordinateComplex (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) :
    CayleyComplex (V := Fin (RelationMatrix.nullity H) → F₂) :=
  (RelationTriangleComplex.cayleyComplex H hyp).relabel (coordinates H).toAddEquiv

theorem coordinateComplex_dimension (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) :
    (coordinateComplex H hyp).complex.dim = 2 :=
  RelationTriangleComplex.cayleyComplex_dimension H hyp

theorem coordinateComplex_unweighted (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) :
    (coordinateComplex H hyp).complex.IsUnweighted :=
  MeasuredComplex.isUnweighted_relabel _ _
    (RelationTriangleComplex.cayleyComplex_unweighted H hyp)

theorem coordinateComplex_degree (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) :
    (coordinateComplex H hyp).cayley.degree = Fintype.card C := by
  rw [coordinateComplex, CayleyComplex.relabel_degree]
  exact RelationTriangleComplex.cayleyComplex_degree H hyp

end HDXLean.RelationQuotient
