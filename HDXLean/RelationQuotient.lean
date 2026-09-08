import HDXLean.RelationMatrix
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# The quotient generators in the relation-matrix construction

This module proves the elementary quotient-vector-space part of the
manuscript's construction. In particular, minimum row-code distance three
makes the images of the coordinate vectors nonzero and pairwise distinct.
No literature input or desired geometric output is assumed here.
-/

namespace HDXLean.RelationQuotient

variable {R C : Type*} [Fintype C] [DecidableEq C]

/-- The coordinate vector indexed by a column. -/
def coordinateVector (c : C) : C → F₂ := fun j ↦ if j = c then 1 else 0

omit [Fintype C] in
theorem coordinateVector_ne_zero (c : C) : coordinateVector c ≠ 0 := by
  intro h
  have := congrFun h c
  simp [coordinateVector] at this

theorem coordinateVector_weight (c : C) : hammingWeight (coordinateVector c) = 1 := by
  have hs : Finset.univ.filter (fun j : C ↦ coordinateVector c j ≠ 0) = {c} := by
    ext j
    simp [coordinateVector]
  simp [hammingWeight, hs]

theorem coordinateVector_sub_weight_le (c d : C) :
    hammingWeight (coordinateVector c - coordinateVector d) ≤ 2 := by
  calc
    hammingWeight (coordinateVector c - coordinateVector d) ≤ ({c, d} : Finset C).card := by
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_contra h
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
      simp [coordinateVector, h.1, h.2] at hj
    _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)

/-- The additive quotient used in the paper, before choosing coordinates. -/
abbrev Ambient (H : BinaryMatrix R C) := (C → F₂) ⧸ rowCode H

/-- The image of a coordinate vector in the row-code quotient. -/
def generator (H : BinaryMatrix R C) (c : C) : Ambient H :=
  Submodule.Quotient.mk (coordinateVector c)

theorem generator_ne_zero (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H) (c : C) : generator H c ≠ 0 := by
  intro h
  have hmem : coordinateVector c ∈ rowCode H :=
    (Submodule.Quotient.mk_eq_zero (rowCode H)).mp h
  have hweight := hdistance _ hmem (coordinateVector_ne_zero c)
  rw [coordinateVector_weight] at hweight
  omega

theorem generator_injective (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H) : Function.Injective (generator H) := by
  intro c d h
  by_contra hcd
  have hmem : coordinateVector c - coordinateVector d ∈ rowCode H :=
    (Submodule.Quotient.eq _).mp h
  have hne : coordinateVector c - coordinateVector d ≠ 0 := by
    intro heq
    have := congrFun heq c
    simp [coordinateVector, hcd] at this
  have hweight := hdistance _ hmem hne
  have hupper := coordinateVector_sub_weight_le c d
  omega

/-- The actual finite generator set in the quotient. -/
noncomputable def generators (H : BinaryMatrix R C) : Finset (Ambient H) := by
  classical
  exact Finset.univ.image (generator H)

theorem zero_not_mem_generators (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H) : 0 ∉ generators H := by
  classical
  simp only [generators, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  exact fun c ↦ generator_ne_zero H hdistance c

/-- The quotient operation loses no generators, so the Cayley degree will be
exactly the number of matrix columns once the face adapter is constructed. -/
theorem card_generators (H : BinaryMatrix R C)
    (hdistance : RowDistanceAtLeastThree H) :
    (generators H).card = Fintype.card C := by
  classical
  rw [generators, Finset.card_image_of_injective _ (generator_injective H hdistance)]
  exact Finset.card_univ

/-- A binary row is the sum of the coordinate vectors in its support. -/
theorem sum_coordinateVector_rowSupport (H : BinaryMatrix R C) (r : R) :
    ∑ c ∈ rowSupport H r, coordinateVector c = H r := by
  ext j
  by_cases hj : H r j = 0
  · simp [coordinateVector, Finset.sum_apply, rowSupport, hj]
  · have hjone : H r j = 1 := Fin.eq_one_of_ne_zero _ hj
    simp [coordinateVector, Finset.sum_apply, rowSupport, hjone]

/-- Every row relation becomes a zero-sum relation among quotient generators.
For a weight-three row, this is precisely the triangle relation used by the
paper. -/
theorem sum_generator_rowSupport (H : BinaryMatrix R C) (r : R) :
    ∑ c ∈ rowSupport H r, generator H c = 0 := by
  change ∑ c ∈ rowSupport H r, (rowCode H).mkQ (coordinateVector c) = 0
  rw [← map_sum, sum_coordinateVector_rowSupport]
  exact (Submodule.Quotient.mk_eq_zero (rowCode H)).mpr
    (Submodule.subset_span ⟨r, rfl⟩)

end HDXLean.RelationQuotient
