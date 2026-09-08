import HDXLean.RelationVertexLinkCount
import HDXLean.WeightedGraphScaling
import HDXLean.Relabeling

/-!
# The literal measured origin link and the counting Gram graph

This module identifies the actual singleton-link vertices and edge weights
of the constructed quotient complex. It uses the existing finite graph
scaling and relabeling lemmas. It does not reprove the cited propagation
statement for other vertex links.
-/

namespace HDXLean.RelationVertexLink

open scoped BigOperators
open RelationQuotient RelationTriangleComplex RelationVertexLinkCount

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C] [Nonempty C]

/-- A column is the corresponding actual vertex in the origin link. -/
noncomputable def columnVertex (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) (c : C) :
    (cayleyComplex H hyp).complex.LinkVertex {0} := by
  refine ⟨generator H c, ?_, ?_⟩
  · simpa only [Finset.mem_singleton] using generator_ne_zero H hyp.rowDistance c
  · apply ((cayleyComplex H hyp).cayley.edge_iff (generator H c) 0).mpr
    right
    change 0 - generator H c ∈ generators H
    rw [zero_sub, ambient_neg_eq]
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩

theorem columnVertex_injective (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) :
    Function.Injective (columnVertex H hyp) := by
  intro c d h
  exact generator_injective H hyp.rowDistance (congrArg Subtype.val h)

theorem columnVertex_surjective (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) :
    Function.Surjective (columnVertex H hyp) := by
  intro v
  have hv : v.1 ≠ 0 := by simpa only [Finset.mem_singleton] using v.2.1
  have hedge := ((cayleyComplex H hyp).cayley.edge_iff v.1 0).mp v.2.2
  have hgen : v.1 ∈ generators H := by
    have h := hedge.resolve_left hv
    change 0 - v.1 ∈ generators H at h
    simpa only [zero_sub, ambient_neg_eq] using h
  obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hgen
  exact ⟨c, Subtype.ext hc⟩

/-- Literal column/origin-link-vertex equivalence. -/
noncomputable def columnEquiv (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) :
    C ≃ (cayleyComplex H hyp).complex.LinkVertex {0} :=
  Equiv.ofBijective (columnVertex H hyp)
    ⟨columnVertex_injective H hyp, columnVertex_surjective H hyp⟩

/-- Native conditioned edge weight: counting Gram multiplicity divided by
the actual number of top faces, including the zero diagonal convention. -/
theorem originLink_weight (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) (c d : C) :
    ((cayleyComplex H hyp).complex.linkGraph {0}).weight
      (columnEquiv H hyp c) (columnEquiv H hyp d) =
      (gramGraph H).weight c d * ((topFaces H).card : ℝ)⁻¹ := by
  classical
  by_cases hne : c = d
  · subst d
    rw [WeightedGraph.weight_self, WeightedGraph.weight_self, zero_mul]
  have hvne : columnEquiv H hyp c ≠ columnEquiv H hyp d :=
    (columnEquiv H hyp).injective.ne hne
  change (cayleyComplex H hyp).complex.linkEdgeWeight {0}
    (columnEquiv H hyp c) (columnEquiv H hyp d) = _
  rw [MeasuredComplex.linkEdgeWeight, if_neg hvne]
  change (∑ T ∈ (topFaces H).filter (fun T ↦
      insert (generator H d) (insert (generator H c) {0}) ⊆ T),
      (if T ∈ topFaces H then ((topFaces H).card : ℝ)⁻¹ else 0)) = _
  have htriple : insert (generator H d) (insert (generator H c) {0}) =
      ({0, generator H c, generator H d} : Finset (Ambient H)) := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]
  rw [htriple]
  calc
    _ = ∑ T ∈ (topFaces H).filter (fun T ↦
        ({0, generator H c, generator H d} : Finset (Ambient H)) ⊆ T),
        ((topFaces H).card : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro T hT
      exact if_pos (Finset.mem_filter.mp hT).1
    _ = (((topFaces H).filter (fun T ↦
        ({0, generator H c, generator H d} : Finset (Ambient H)) ⊆ T)).card : ℝ) *
        ((topFaces H).card : ℝ)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by
      rw [origin_pair_faces_card H hyp.rowDistance hyp.rowsHaveWeightThree hyp.rowsDistinct hne]
      simp only [gramGraph, if_neg hne]

/-- The positive common edge factor converting the normalized Gram graph
to the native conditioned origin-link weights. -/
noncomputable def originLinkScale (H : BinaryMatrix R C) (rho : ℕ) : ℝ :=
  (2 * (rho : ℝ)) * ((topFaces H).card : ℝ)⁻¹

theorem originLinkScale_pos (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) : 0 < originLinkScale H rho := by
  letI := hyp.row_nonempty
  have hN : 0 < ((topFaces H).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (topFaces_nonempty H)
  have hrho : 0 < (rho : ℝ) := by exact_mod_cast hyp.constantColumnWeight.1
  unfold originLinkScale
  positivity

/-- Literal graph identity, including the native measure normalization and
the exact column/origin-link-vertex equivalence. -/
theorem originLink_eq_scaled_normalizedGram (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) :
    (cayleyComplex H hyp).complex.linkGraph {0} =
      ((RelationMatrix.normalizedGramGraph H rho hyp.constantColumnWeight.1).scale
        (originLinkScale H rho) (originLinkScale_pos H hyp).le).relabel
          (columnEquiv H hyp) := by
  apply WeightedGraph.ext_weight
  intro u v
  obtain ⟨c, rfl⟩ := (columnEquiv H hyp).surjective u
  obtain ⟨d, rfl⟩ := (columnEquiv H hyp).surjective v
  rw [originLink_weight]
  simp only [WeightedGraph.relabel, Equiv.symm_apply_apply, WeightedGraph.scale,
    RelationMatrix.normalizedGramGraph, originLinkScale]
  have hrho : (2 * (rho : ℝ)) ≠ 0 := by
    have hpos : 0 < (rho : ℝ) := by exact_mod_cast hyp.constantColumnWeight.1
    positivity
  symm
  calc
    _ = ((2 * (rho : ℝ)) * (2 * (rho : ℝ))⁻¹) *
        ((gramGraph H).weight c d * ((topFaces H).card : ℝ)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hrho, one_mul]

/-- The input Gram certificate transfers to the actual origin link using
only the existing positive-scaling and relabeling results. -/
theorem originLink_expander (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) {lambda : ℝ}
    (hgram : WeightedGraph.IsTwoSidedSpectralExpander
      (RelationMatrix.normalizedGramGraph H rho hyp.constantColumnWeight.1) lambda) :
    ((cayleyComplex H hyp).complex.linkGraph {0}).IsTwoSidedSpectralExpander lambda := by
  rw [originLink_eq_scaled_normalizedGram H hyp]
  apply WeightedGraph.isTwoSidedSpectralExpander_relabel
  exact WeightedGraph.isTwoSidedSpectralExpander_scale _ _ (originLinkScale_pos H hyp) hgram

end HDXLean.RelationVertexLink
