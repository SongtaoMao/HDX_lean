import HDXLean.RelationQuotient
import HDXLean.SkeletonCayley
import Mathlib.Algebra.CharP.Two

/-!
# The actual measured quotient triangle complex

The top faces are all translates of the three quotient generators in a
matrix row. They are stored as a finite set, not as a multiset of row and
translation witnesses. Uniform weight is normalized on that actual set.
The construction does not assume the output of a relation compiler.
-/

namespace HDXLean.RelationTriangleComplex

open scoped BigOperators
open RelationQuotient

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]

noncomputable instance ambientFintype (H : BinaryMatrix R C) : Fintype (Ambient H) :=
  Fintype.ofFinite _

noncomputable instance ambientDecidableEq (H : BinaryMatrix R C) :
    DecidableEq (Ambient H) := Classical.decEq _

/-- A row's three quotient coordinate images. -/
noncomputable def rowTriangle (H : BinaryMatrix R C) (r : R) : Finset (Ambient H) :=
  (rowSupport H r).image (generator H)

theorem rowTriangle_card (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H) (r : R) :
    (rowTriangle H r).card = 3 := by
  rw [rowTriangle, Finset.card_image_of_injective _ (generator_injective H hdistance)]
  exact hrows r

/-- All distinct translates of row triangles. -/
noncomputable def topFaces (H : BinaryMatrix R C) : Finset (Finset (Ambient H)) :=
  Finset.univ.biUnion fun r : R ↦
    Finset.univ.image fun x : Ambient H ↦ translateFace x (rowTriangle H r)

theorem mem_topFaces (H : BinaryMatrix R C) (T : Finset (Ambient H)) :
    T ∈ topFaces H ↔ ∃ r x, translateFace x (rowTriangle H r) = T := by
  simp [topFaces]

theorem topFaces_nonempty (H : BinaryMatrix R C) [Nonempty R] :
    (topFaces H).Nonempty := by
  obtain ⟨r⟩ := ‹Nonempty R›
  exact ⟨_, (mem_topFaces H _).mpr ⟨r, 0, rfl⟩⟩

theorem topFaces_card_three (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H)
    (T : Finset (Ambient H)) (hT : T ∈ topFaces H) : T.card = 3 := by
  obtain ⟨r, x, rfl⟩ := (mem_topFaces H T).mp hT
  rw [translateFace_card, rowTriangle_card H hdistance hrows]

theorem translate_add (H : BinaryMatrix R C) (x y : Ambient H)
    (T : Finset (Ambient H)) :
    translateFace x (translateFace y T) = translateFace (x + y) T := by
  simp only [translateFace, Finset.image_image, Function.comp_def, add_assoc]

theorem topFaces_translate_iff (H : BinaryMatrix R C) (x : Ambient H)
    (T : Finset (Ambient H)) :
    translateFace x T ∈ topFaces H ↔ T ∈ topFaces H := by
  constructor
  · intro h
    obtain ⟨r, y, hy⟩ := (mem_topFaces H _).mp h
    refine (mem_topFaces H _).mpr ⟨r, -x + y, ?_⟩
    rw [← translate_add, hy]
    simpa only [neg_neg] using translateFace_neg_cancel (-x) T
  · intro h
    obtain ⟨r, y, rfl⟩ := (mem_topFaces H _).mp h
    exact (mem_topFaces H _).mpr ⟨r, x + y, (translate_add H x y _).symm⟩

/-- The normalized uniform measure on the actual distinct triangles. -/
noncomputable def complex (H : BinaryMatrix R C) [Nonempty R]
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H) : MeasuredComplex (Ambient H) where
  dim := 2
  topFaces := topFaces H
  top_card := topFaces_card_three H hdistance hrows
  topWeight T := if T ∈ topFaces H then ((topFaces H).card : ℝ)⁻¹ else 0
  topWeight_pos T hT := by
    simp only [hT, if_true]
    have hcard := Finset.card_pos.mpr (topFaces_nonempty H)
    positivity
  topWeight_zero T hT := by simp [hT]
  topWeight_sum := by
    have hcard : ((topFaces H).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr (topFaces_nonempty H)).ne'
    simp [hcard]

theorem complex_dimension (H : BinaryMatrix R C) [Nonempty R]
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H) :
    (complex H hdistance hrows).dim = 2 := rfl

theorem complex_unweighted (H : BinaryMatrix R C) [Nonempty R]
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H) :
    (complex H hdistance hrows).IsUnweighted := by
  intro T hT
  change (if T ∈ topFaces H then _ else 0) = _
  simp only [show T ∈ topFaces H from hT, if_true]
  rfl

theorem complex_translationInvariant (H : BinaryMatrix R C) [Nonempty R]
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H) :
    TranslationInvariant (complex H hdistance hrows) := by
  intro x T
  refine ⟨topFaces_translate_iff H x T, ?_⟩
  change (if translateFace x T ∈ topFaces H then _ else 0) =
    (if T ∈ topFaces H then _ else 0)
  simp only [topFaces_translate_iff]

theorem ambient_add_self (H : BinaryMatrix R C) (x : Ambient H) : x + x = 0 := by
  calc
    x + x = ((1 : F₂) + 1) • x := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : F₂) + 1 = 0 by decide, zero_smul]

theorem ambient_neg_eq (H : BinaryMatrix R C) (x : Ambient H) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, ambient_add_self]

theorem ambient_sub_eq_add (H : BinaryMatrix R C) (x y : Ambient H) :
    x - y = x + y := by rw [sub_eq_add_neg, ambient_neg_eq]

theorem rowTriangle_sum (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H) (r : R) :
    ∑ x ∈ rowTriangle H r, x = 0 := by
  rw [rowTriangle, Finset.sum_image]
  · exact sum_generator_rowSupport H r
  · intro a _ b _ h
    exact generator_injective H hdistance h

/-- Each difference of distinct vertices in a row triangle is the third
generator in that same row triangle. -/
theorem rowTriangle_pair_difference_mem (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H) (r : R)
    {a b : Ambient H} (ha : a ∈ rowTriangle H r) (hb : b ∈ rowTriangle H r)
    (hab : a ≠ b) : b - a ∈ rowTriangle H r := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hT⟩ :=
    Finset.card_eq_three.mp (rowTriangle_card H hdistance hrows r)
  have hsum := rowTriangle_sum H hdistance r
  simp only [hT, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    hxy, hxz, hyz, or_self, not_false_eq_true, Finset.sum_singleton] at hsum
  have hpairxy : x + y = z := by
    have h := congrArg (fun w ↦ w + z) hsum
    simpa [add_assoc, ambient_add_self] using h
  have hpairxz : x + z = y := by
    rw [← hpairxy, ← add_assoc, ambient_add_self, zero_add]
  have hpairyz : y + z = x := by
    rw [← hpairxy, add_left_comm, ambient_add_self, add_zero]
  simp only [hT, Finset.mem_insert, Finset.mem_singleton] at ha hb ⊢
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals simp_all [ambient_sub_eq_add, add_comm]

theorem singleton_isFace (H : BinaryMatrix R C) [Nonempty R]
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H) (x : Ambient H) :
    (complex H hdistance hrows).IsFace {x} := by
  obtain ⟨r⟩ := ‹Nonempty R›
  have hne : (rowTriangle H r).Nonempty := by
    apply Finset.card_pos.mp
    rw [rowTriangle_card H hdistance hrows]
    decide
  obtain ⟨a, ha⟩ := hne
  refine ⟨translateFace (x - a) (rowTriangle H r),
    (mem_topFaces H _).mpr ⟨r, x - a, rfl⟩, ?_⟩
  apply Finset.singleton_subset_iff.mpr
  exact Finset.mem_image.mpr ⟨a, ha, sub_add_cancel x a⟩

theorem edge_difference_mem_generators (H : BinaryMatrix R C) [Nonempty R]
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H)
    {x y : Ambient H} (hedge : (complex H hdistance hrows).IsFace {x, y})
    (hne : x ≠ y) : y - x ∈ generators H := by
  obtain ⟨T, hT, hsub⟩ := hedge
  obtain ⟨r, v, rfl⟩ := (mem_topFaces H T).mp hT
  have hx := hsub (Finset.mem_insert_self x {y})
  have hy := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  have hab : a ≠ b := by intro h; exact hne (congrArg (v + ·) h)
  have hdiff := rowTriangle_pair_difference_mem H hdistance hrows r ha hb hab
  obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hdiff
  apply Finset.mem_image.mpr
  refine ⟨c, Finset.mem_univ _, ?_⟩
  simpa only [add_sub_add_left_eq_sub] using hc

/-- Positive column weight ensures that each proposed generator occurs in a
row triangle. -/
theorem columns_covered (H : BinaryMatrix R C) {rho : ℕ}
    (hweight : RelationMatrix.ConstantColumnWeight H rho) (c : C) :
    ∃ r, c ∈ rowSupport H r := by
  have hpos : 0 < columnWeight H c := by rw [hweight.2 c]; exact hweight.1
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hpos
  exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2⟩⟩

theorem isFace_of_difference_mem_generators (H : BinaryMatrix R C) [Nonempty R]
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H)
    (hcover : ∀ c, ∃ r, c ∈ rowSupport H r)
    {x y : Ambient H} (hgen : y - x ∈ generators H) :
    (complex H hdistance hrows).IsFace {x, y} := by
  obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hgen
  obtain ⟨r, hr⟩ := hcover c
  have hcg : generator H c ∈ rowTriangle H r :=
    Finset.mem_image.mpr ⟨c, hr, rfl⟩
  have hcard : 1 < (rowTriangle H r).card := by
    rw [rowTriangle_card H hdistance hrows]
    decide
  obtain ⟨a, ha, hane⟩ := Finset.exists_mem_ne hcard (generator H c)
  have hb := rowTriangle_pair_difference_mem H hdistance hrows r ha hcg hane
  refine ⟨translateFace (x - a) (rowTriangle H r),
    (mem_topFaces H _).mpr ⟨r, x - a, rfl⟩, ?_⟩
  apply Finset.insert_subset_iff.mpr
  refine ⟨Finset.mem_image.mpr ⟨a, ha, sub_add_cancel x a⟩, ?_⟩
  apply Finset.singleton_subset_iff.mpr
  refine Finset.mem_image.mpr ⟨generator H c - a, hb, ?_⟩
  calc
    (x - a) + (generator H c - a) = x + generator H c := by
      simp only [ambient_sub_eq_add]
      rw [add_assoc, add_left_comm a (generator H c), ambient_add_self, add_zero]
    _ = y := by
      rw [hc]
      simpa only [add_sub_assoc] using add_sub_cancel_left x y

/-- The actual Cayley presentation, including both directions of the
one-skeleton/generator correspondence. -/
noncomputable def cayleyPresentation (H : BinaryMatrix R C) [Nonempty R]
    (hdistance : RowDistanceAtLeastThree H)
    (hrows : RelationMatrix.RowsHaveWeightThree H)
    (hcover : ∀ c, ∃ r, c ∈ rowSupport H r) :
    CayleyPresentation (complex H hdistance hrows) where
  generators := generators H
  zero_not_mem := zero_not_mem_generators H hdistance
  neg_mem_iff s := by rw [ambient_neg_eq]
  edge_iff x y := by
    constructor
    · intro h
      by_cases hxy : x = y
      · exact Or.inl hxy
      · exact Or.inr (edge_difference_mem_generators H hdistance hrows h hxy)
    · rintro (rfl | h)
      · simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self x)] using
          singleton_isFace H hdistance hrows x
      · exact isFace_of_difference_mem_generators H hdistance hrows hcover h

/-- A two-dimensional unweighted Cayley complex constructed from the matrix
hypotheses. Local expansion and codegree are not assumed in this definition. -/
noncomputable def cayleyComplex (H : BinaryMatrix R C) [Nonempty C]
    {rho : ℕ} (hyp : RelationMatrix.CompilerHypotheses H rho) :
    CayleyComplex (V := Ambient H) := by
  letI := hyp.row_nonempty
  exact
    { complex := complex H hyp.rowDistance hyp.rowsHaveWeightThree
      cayley := cayleyPresentation H hyp.rowDistance hyp.rowsHaveWeightThree
        (columns_covered H hyp.constantColumnWeight)
      translationInvariant := complex_translationInvariant H hyp.rowDistance
        hyp.rowsHaveWeightThree }

theorem cayleyComplex_dimension (H : BinaryMatrix R C) [Nonempty C]
    {rho : ℕ} (hyp : RelationMatrix.CompilerHypotheses H rho) :
    (cayleyComplex H hyp).complex.dim = 2 := rfl

theorem cayleyComplex_unweighted (H : BinaryMatrix R C) [Nonempty C]
    {rho : ℕ} (hyp : RelationMatrix.CompilerHypotheses H rho) :
    (cayleyComplex H hyp).complex.IsUnweighted := by
  letI := hyp.row_nonempty
  exact complex_unweighted H hyp.rowDistance hyp.rowsHaveWeightThree

theorem cayleyComplex_degree (H : BinaryMatrix R C) [Nonempty C]
    {rho : ℕ} (hyp : RelationMatrix.CompilerHypotheses H rho) :
    (cayleyComplex H hyp).cayley.degree = Fintype.card C :=
  card_generators H hyp.rowDistance

end HDXLean.RelationTriangleComplex
