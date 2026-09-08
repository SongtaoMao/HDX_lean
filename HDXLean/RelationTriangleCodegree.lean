import HDXLean.RelationTriangleComplex
import Mathlib.Data.Finset.Sigma

/-!
# Counting actual triangles in the quotient complex

This file proves uniqueness of row/translation witnesses before using those
witnesses to count triangles. In characteristic two the sum of the three
vertices of a translated row triangle is exactly its translation parameter.
Thus distinct rows cannot have overlapping translation orbits.
-/

namespace HDXLean.RelationTriangleCodegree

open scoped BigOperators
open RelationQuotient RelationTriangleComplex

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]

theorem rowTriangle_injective (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsDistinct H) : Function.Injective (rowTriangle H) := by
  intro r s hrs
  have hs : rowSupport H r = rowSupport H s :=
    Finset.image_injective (generator_injective H hdistance) hrs
  apply hrows
  change H r = H s
  exact (sum_coordinateVector_rowSupport H r).symm.trans
    ((congrArg (fun S : Finset C ↦ ∑ c ∈ S, coordinateVector c) hs).trans
      (sum_coordinateVector_rowSupport H s))

/-- The vertex sum canonically recovers the translation witness. -/
theorem sum_translated_rowTriangle (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H) (r : R) (v : Ambient H) :
    ∑ x ∈ translateFace v (rowTriangle H r), x = v := by
  rw [translateFace, Finset.sum_image]
  · rw [Finset.sum_add_distrib, Finset.sum_const,
      rowTriangle_card H hdistance hrows, rowTriangle_sum H hdistance, add_zero]
    simp only [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul,
      two_nsmul, ambient_add_self, zero_add]
  · intro a _ b _ h
    exact add_left_cancel h

/-- Each actual top face has exactly one row and translation witness. -/
theorem translated_rowTriangle_injective (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H)
    (hweight : RelationMatrix.RowsHaveWeightThree H)
    (hdistinct : RelationMatrix.RowsDistinct H) :
    Function.Injective (fun p : Σ _ : R, Ambient H ↦
      translateFace p.2 (rowTriangle H p.1)) := by
  rintro ⟨r, v⟩ ⟨s, w⟩ h
  have hvw : v = w := by
    have hs := congrArg (fun T : Finset (Ambient H) ↦ ∑ x ∈ T, x) h
    simpa only [sum_translated_rowTriangle H hdistance hweight] using hs
  subst w
  have hrs : r = s := by
    apply rowTriangle_injective H hdistance hdistinct
    exact Finset.image_injective (add_right_injective v) h
  subst s
  rfl

theorem zero_not_mem_rowTriangle (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H) (r : R) : 0 ∉ rowTriangle H r := by
  intro hz
  obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hz
  exact generator_ne_zero H hdistance c hc

theorem generator_mem_rowTriangle_iff (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H) (r : R) (c : C) :
    generator H c ∈ rowTriangle H r ↔ c ∈ rowSupport H r := by
  exact Finset.mem_image.trans ⟨
    fun ⟨d, hd, heq⟩ ↦ generator_injective H hdistance heq ▸ hd,
    fun hc ↦ ⟨c, hc, rfl⟩⟩

/-- A translated row triangle contains the edge `{0, generator c}` exactly
when its row contains column `c` and its translation is one of the other two
row generators. -/
theorem edge_mem_translated_rowTriangle_iff (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H) (r : R) (v : Ambient H) (c : C) :
    (0 ∈ translateFace v (rowTriangle H r) ∧
      generator H c ∈ translateFace v (rowTriangle H r)) ↔
      c ∈ rowSupport H r ∧ v ∈ (rowTriangle H r).erase (generator H c) := by
  simp only [mem_translateFace_iff, zero_sub, ambient_neg_eq,
    Finset.mem_erase]
  constructor
  · rintro ⟨hv, hcv⟩
    have hvne : v ≠ generator H c := by
      intro h
      subst v
      rw [sub_self] at hcv
      exact zero_not_mem_rowTriangle H hdistance r hcv
    have hneq : v ≠ generator H c - v := by
      intro h
      have hc0 : generator H c = 0 := by
        have heq := congrArg (fun z : Ambient H ↦ z + v) h
        simpa only [ambient_add_self, sub_add_cancel] using heq.symm
      exact generator_ne_zero H hdistance c hc0
    have hc := rowTriangle_pair_difference_mem H hdistance hrows r hv hcv hneq
    have hcancel : (generator H c - v) - v = generator H c := by
      simp only [ambient_sub_eq_add]
      rw [add_assoc, ambient_add_self, add_zero]
    rw [hcancel] at hc
    exact ⟨(generator_mem_rowTriangle_iff H hdistance r c).mp hc, hvne, hv⟩
  · rintro ⟨hc, hvne, hv⟩
    have hcg := (generator_mem_rowTriangle_iff H hdistance r c).mpr hc
    exact ⟨hv, rowTriangle_pair_difference_mem H hdistance hrows r hv hcg hvne⟩

/-- The actual two choices of translation for each row incident to column
`c`, with no quotient by an unproved orbit equivalence. -/
noncomputable def incidentFlags (H : BinaryMatrix R C) (c : C) :
    Finset (Σ _ : R, Ambient H) :=
  (Finset.univ.filter fun r : R ↦ H r c ≠ 0).sigma
    fun r ↦ (rowTriangle H r).erase (generator H c)

theorem mem_incidentFlags (H : BinaryMatrix R C) (c : C)
    (p : Σ _ : R, Ambient H) :
    p ∈ incidentFlags H c ↔
      c ∈ rowSupport H p.1 ∧ p.2 ∈ (rowTriangle H p.1).erase (generator H c) := by
  simp [incidentFlags, Finset.mem_sigma, rowSupport]

theorem card_incidentFlags (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H) (c : C) :
    (incidentFlags H c).card = 2 * columnWeight H c := by
  rw [incidentFlags, Finset.card_sigma]
  have hf : ∀ r ∈ Finset.univ.filter (fun r : R ↦ H r c ≠ 0),
      ((rowTriangle H r).erase (generator H c)).card = 2 := by
    intro r hr
    have hc : c ∈ rowSupport H r := by simpa [rowSupport] using hr
    rw [Finset.card_erase_of_mem ((generator_mem_rowTriangle_iff H hdistance r c).mpr hc),
      rowTriangle_card H hdistance hrows]
  rw [Finset.sum_const_nat hf]
  exact Nat.mul_comm _ _

/-- The edge-containing top faces are exactly the injective image of the
incident row/translation flags. -/
theorem edgeFaces_eq_image (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H) (c : C) :
    ((topFaces H).filter fun T ↦ 0 ∈ T ∧ generator H c ∈ T) =
      (incidentFlags H c).image (fun p ↦ translateFace p.2 (rowTriangle H p.1)) := by
  ext T
  constructor
  · intro hT
    obtain ⟨hTtop, hedge⟩ := Finset.mem_filter.mp hT
    obtain ⟨r, v, rfl⟩ := (mem_topFaces H T).mp hTtop
    refine Finset.mem_image.mpr ⟨⟨r, v⟩, ?_, rfl⟩
    apply (mem_incidentFlags H c _).mpr
    exact (edge_mem_translated_rowTriangle_iff H hdistance hrows r v c).mp hedge
  · intro hT
    obtain ⟨⟨r, v⟩, hp, rfl⟩ := Finset.mem_image.mp hT
    refine Finset.mem_filter.mpr ⟨(mem_topFaces H _).mpr ⟨r, v, rfl⟩, ?_⟩
    exact (edge_mem_translated_rowTriangle_iff H hdistance hrows r v c).mpr
      ((mem_incidentFlags H c _).mp hp)

theorem edgeFaces_card (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H)
    (hdistinct : RelationMatrix.RowsDistinct H) (c : C) :
    ((topFaces H).filter fun T ↦ 0 ∈ T ∧ generator H c ∈ T).card =
      2 * columnWeight H c := by
  rw [edgeFaces_eq_image H hdistance hrows,
    Finset.card_image_of_injective _
      (translated_rowTriangle_injective H hdistance hrows hdistinct)]
  exact card_incidentFlags H hdistance hrows c

/-- Translating an edge to the origin preserves the number of actual top
faces containing it. -/
theorem edgeFaces_card_translate (H : BinaryMatrix R C) (x y : Ambient H) :
    ((topFaces H).filter fun T ↦ x ∈ T ∧ y ∈ T).card =
      ((topFaces H).filter fun T ↦ 0 ∈ T ∧ y - x ∈ T).card := by
  apply Finset.card_bij (fun T _ ↦ translateFace (-x) T)
  · intro T hT
    obtain ⟨hT, hx, hy⟩ := Finset.mem_filter.mp hT
    refine Finset.mem_filter.mpr ⟨(topFaces_translate_iff H (-x) T).mpr hT, ?_, ?_⟩
    · simpa only [mem_translateFace_iff, zero_sub, neg_neg] using hx
    · simpa only [mem_translateFace_iff, sub_neg_eq_add, sub_add_cancel] using hy
  · intro T _ S _ h
    exact Finset.image_injective (add_right_injective (-x)) h
  · intro S hS
    obtain ⟨hS, hzero, hy⟩ := Finset.mem_filter.mp hS
    refine ⟨translateFace x S, Finset.mem_filter.mpr
      ⟨(topFaces_translate_iff H x S).mpr hS, ?_, ?_⟩, ?_⟩
    · simpa only [mem_translateFace_iff, sub_self] using hzero
    · exact (mem_translateFace_iff x y S).mpr hy
    · simpa only [neg_neg] using translateFace_neg_cancel (-x) S

/-- Exact codegree for the constructed quotient Cayley complex. No compiler
output or orbit-counting assumption is used. -/
theorem cayleyComplex_edgeCodegree (H : BinaryMatrix R C) [Nonempty C]
    {rho : ℕ} (hyp : RelationMatrix.CompilerHypotheses H rho)
    (x y : Ambient H) (hne : x ≠ y)
    (hedge : (cayleyComplex H hyp).complex.IsFace {x, y}) :
    (cayleyComplex H hyp).complex.edgeCodegree x y = 2 * rho := by
  have hgen : y - x ∈ generators H := by
    have h := ((cayleyComplex H hyp).cayley.edge_iff x y).mp hedge
    exact h.resolve_left hne
  obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hgen
  change ((topFaces H).filter fun T ↦ x ∈ T ∧ y ∈ T).card = _
  rw [edgeFaces_card_translate, ← hc,
    edgeFaces_card H hyp.rowDistance hyp.rowsHaveWeightThree hyp.rowsDistinct,
    hyp.constantColumnWeight.2]

end HDXLean.RelationTriangleCodegree
