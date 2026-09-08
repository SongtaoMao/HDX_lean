import HDXLean.RelationTriangleCodegree

/-!
# Native singleton-link triangle counts

This is an actual-object adapter: it counts the top faces used in the
measured quotient complex's link weights. No external spectral theorem is
reproved or assumed here.
-/

namespace HDXLean.RelationVertexLinkCount

open scoped BigOperators
open RelationQuotient RelationTriangleComplex RelationTriangleCodegree

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]

theorem pair_triangle_card (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H) {c d : C} (hne : c ≠ d) :
    ({0, generator H c, generator H d} : Finset (Ambient H)).card = 3 := by
  have hc := generator_ne_zero H hdistance c
  have hd := generator_ne_zero H hdistance d
  have hcd := (generator_injective H hdistance).ne hne
  simp [Ne.symm hc, Ne.symm hd, hcd]

theorem pair_triangle_sum (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H) {c d : C} (hne : c ≠ d) :
    ∑ x ∈ ({0, generator H c, generator H d} : Finset (Ambient H)), x =
      generator H c + generator H d := by
  have hc := generator_ne_zero H hdistance c
  have hd := generator_ne_zero H hdistance d
  have hcd := (generator_injective H hdistance).ne hne
  simp [Ne.symm hc, Ne.symm hd, hcd]

/-- If a row contains both distinct columns, translating it by the sum of
their generators gives exactly the triangle through the origin and those
two generators. -/
theorem pair_triangle_subset_translate (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H) (r : R)
    {c d : C} (hne : c ≠ d) (hc : c ∈ rowSupport H r) (hd : d ∈ rowSupport H r) :
    ({0, generator H c, generator H d} : Finset (Ambient H)) ⊆
      translateFace (generator H c + generator H d) (rowTriangle H r) := by
  have hcg := (generator_mem_rowTriangle_iff H hdistance r c).mpr hc
  have hdg := (generator_mem_rowTriangle_iff H hdistance r d).mpr hd
  have hcd := (generator_injective H hdistance).ne hne
  have hsum : generator H c + generator H d ∈ rowTriangle H r := by
    simpa only [ambient_sub_eq_add] using
      rowTriangle_pair_difference_mem H hdistance hrows r hdg hcg hcd.symm
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
    mem_translateFace_iff, zero_sub, ambient_neg_eq]
  refine ⟨hsum, ?_, ?_⟩
  · simpa only [ambient_sub_eq_add, ← add_assoc, ambient_add_self, zero_add] using hdg
  · simpa only [ambient_sub_eq_add, add_left_comm (generator H d) (generator H c),
      ambient_add_self, add_zero] using hcg

/-- Triangles through two prescribed origin-link vertices are parametrized
by rows containing the two corresponding columns. -/
theorem origin_pair_faces_eq_image (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H) {c d : C} (hne : c ≠ d) :
    ((topFaces H).filter fun T ↦
      ({0, generator H c, generator H d} : Finset (Ambient H)) ⊆ T) =
      (Finset.univ.filter fun r : R ↦ H r c ≠ 0 ∧ H r d ≠ 0).image
        (fun r ↦ translateFace (generator H c + generator H d) (rowTriangle H r)) := by
  ext T
  constructor
  · intro hT
    obtain ⟨hTtop, hsub⟩ := Finset.mem_filter.mp hT
    have hTeq : ({0, generator H c, generator H d} : Finset (Ambient H)) = T := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [pair_triangle_card H hdistance hne, topFaces_card_three H hdistance hrows T hTtop]
    obtain ⟨r, v, hrv⟩ := (mem_topFaces H T).mp hTtop
    have hv : v = generator H c + generator H d := by
      have hs := congrArg (fun S : Finset (Ambient H) ↦ ∑ x ∈ S, x) hrv
      rw [sum_translated_rowTriangle H hdistance hrows, ← hTeq,
        pair_triangle_sum H hdistance hne] at hs
      exact hs
    have hzero : 0 ∈ translateFace v (rowTriangle H r) := by
      rw [hrv, ← hTeq]; simp
    have hc : generator H c ∈ translateFace v (rowTriangle H r) := by
      rw [hrv, ← hTeq]; simp
    have hd : generator H d ∈ translateFace v (rowTriangle H r) := by
      rw [hrv, ← hTeq]; simp
    have hrc := ((edge_mem_translated_rowTriangle_iff H hdistance hrows r v c).mp
      ⟨hzero, hc⟩).1
    have hrd := ((edge_mem_translated_rowTriangle_iff H hdistance hrows r v d).mp
      ⟨hzero, hd⟩).1
    refine Finset.mem_image.mpr ⟨r, ?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, rowSupport] using
        And.intro hrc hrd
    · simpa only [hv] using hrv
  · intro hT
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨_, hc, hd⟩ := Finset.mem_filter.mp hr
    refine Finset.mem_filter.mpr ⟨(mem_topFaces H _).mpr ⟨r, _, rfl⟩, ?_⟩
    apply pair_triangle_subset_translate H hdistance hrows r hne
    · simpa [rowSupport] using hc
    · simpa [rowSupport] using hd

theorem origin_pair_faces_card (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H)
    (hdistinct : RelationMatrix.RowsDistinct H) {c d : C} (hne : c ≠ d) :
    ((topFaces H).filter fun T ↦
      ({0, generator H c, generator H d} : Finset (Ambient H)) ⊆ T).card =
      countingGram H c d := by
  rw [origin_pair_faces_eq_image H hdistance hrows hne, Finset.card_image_of_injective]
  · rfl
  · intro r s hrs
    apply rowTriangle_injective H hdistance hdistinct
    exact Finset.image_injective (add_right_injective _) hrs

end HDXLean.RelationVertexLinkCount
