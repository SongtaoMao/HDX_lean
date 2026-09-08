import HDXLean.AffineRelation
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# The affine-function kernel of the relation matrix

This file formalizes Lemma 3.6.  An affine-on-directions function is evaluated
on every column and paired with the column's nonzero field label through the
binary trace.  Characteristic-two triple identities put the resulting word in
the matrix kernel.  Nondegeneracy of the cited trace pairing proves injectivity
and supplies the coordinate-detecting and pair-separating words used to deduce
row-code distance at least three.
-/

namespace HDXLean

open scoped BigOperators

namespace AffineRelationKernel

universe u v

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
  [CharP F 2] [Algebra F₂ F]
variable {t : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The map `Φ` from Lemma 3.6. -/
noncomputable def phi (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) :
    (affineFunctions F D) →ₗ[F₂] (AffineRelation.Column F t → F₂) where
  toFun f c := input.trace ((c.1 : F) * f.1 c.2)
  map_add' f g := by
    funext c
    simp only [Submodule.coe_add, Pi.add_apply, mul_add, map_add]
  map_smul' a f := by
    funext c
    simpa [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using
      input.trace.map_smul a ((c.1 : F) * f.1 c.2)

omit [CharP F 2] [DecidableEq ι] in
@[simp]
theorem phi_apply (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) (f : affineFunctions F D)
    (c : AffineRelation.Column F t) :
    phi input D f c = input.trace ((c.1 : F) * f.1 c.2) :=
  rfl

omit [Algebra F₂ F] in
/-- Matrix application is summation over the three entries in the indexed
relation row. -/
theorem matrix_apply_eq_sum_rowEntries (D : DirectionSet F t ι)
    (word : AffineRelation.Column F t → F₂)
    (r : AffineRelation.RowIndex F t ι) :
    RelationMatrix.apply (AffineRelation.matrix D) word r =
      ∑ c ∈ AffineRelation.rowEntries D r, word c := by
  classical
  simp [RelationMatrix.apply, AffineRelation.matrix]

omit [CharP F 2] [Algebra F₂ F] in
/-- The sum over the attached subtype is the sum over the original field
triple. -/
theorem sum_attach (ell : AffineRelation.TripleIndex F) (g : F → F) :
    (∑ p : {z : F // z ∈ ell.1}, g p.1) = ∑ p ∈ ell.1, g p := by
  classical
  exact Finset.sum_attach ell.1 g

/-- Every affine evaluation word has zero parity on every relation row. -/
theorem phi_mem_kernel (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) (f : affineFunctions F D) :
    phi input D f ∈ RelationMatrix.kernel (AffineRelation.matrix D) := by
  rw [RelationMatrix.kernel, LinearMap.mem_ker]
  funext r
  change RelationMatrix.apply (AffineRelation.matrix D) (phi input D f) r = 0
  rw [matrix_apply_eq_sum_rowEntries]
  rw [AffineRelation.rowEntries]
  rw [Finset.sum_image]
  · rw [Finset.attach_eq_univ]
    obtain ⟨A, B, hline⟩ :=
      AffineOnDirection.smul F (f.2 r.direction) (r.scale : F) r.base
    simp only [phi_apply, AffineRelation.rowColumn,
      AffineRelation.tripleMemberUnit_val, AffineRelation.directionVector, hline]
    rw [← map_sum]
    rw [show
      (∑ p : {z : F // z ∈ r.triple.1},
          p.1 * (A + B * p.1)) = 0 by
        calc
          (∑ p : {z : F // z ∈ r.triple.1},
              p.1 * (A + B * p.1)) =
              A * (∑ p : {z : F // z ∈ r.triple.1}, p.1) +
                B * (∑ p : {z : F // z ∈ r.triple.1}, p.1 ^ 2) := by
                simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
                apply congrArg₂ (fun x y : F ↦ x + y)
                · apply Finset.sum_congr rfl
                  intro p _
                  ring
                · apply Finset.sum_congr rfl
                  intro p _
                  ring
          _ = 0 := by
            rw [sum_attach r.triple (fun z : F ↦ z),
              sum_attach r.triple (fun z : F ↦ z ^ 2),
              CharTwoTriples.family_member_sum r.triple.2,
              CharTwoTriples.family_member_sum_sq r.triple.2]
            simp]
    exact map_zero input.trace
  · exact (AffineRelation.rowColumn_injective D r).injOn

omit [CharP F 2] [DecidableEq ι] in
/-- Nondegeneracy of the trace pairing makes `Φ` injective. -/
theorem phi_injective (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) : Function.Injective (phi input D) := by
  intro f g hfg
  apply Subtype.ext
  funext x
  apply sub_eq_zero.mp
  apply input.pairing_nondegenerate
  intro p
  by_cases hp : p = 0
  · simp [hp]
  · let pu : Fˣ := Units.mk0 p hp
    have hc := congrFun hfg (pu, x)
    change input.trace (p * f.1 x) = input.trace (p * g.1 x) at hc
    rw [mul_sub, map_sub, hc, sub_self]

/-- Restrict `Φ` to its proved codomain, the concrete matrix kernel. -/
noncomputable def phiToKernel (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) :
    (affineFunctions F D) →ₗ[F₂]
      RelationMatrix.kernel (AffineRelation.matrix D) :=
  (phi input D).codRestrict
    (RelationMatrix.kernel (AffineRelation.matrix D))
    (phi_mem_kernel input D)

/-- The kernel-restricted map remains injective. -/
theorem phiToKernel_injective (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) : Function.Injective (phiToKernel input D) := by
  intro f g hfg
  apply phi_injective input D
  exact congrArg Subtype.val hfg

/-- The dimension estimate in Lemma 3.6, stated for an arbitrary finite
extension of the binary field.  In the paper `F = 𝔽_(2^(2h))`, so the
first factor is `2h`. -/
theorem finrank_mul_finrank_le_nullity
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) :
    Module.finrank F₂ F * Module.finrank F (affineFunctions F D) ≤
      RelationMatrix.nullity (AffineRelation.matrix D) := by
  rw [Module.finrank_mul_finrank]
  exact (phiToKernel input D).finrank_le_finrank_of_injective
    (phiToKernel_injective input D)

omit [CharP F 2] [DecidableEq ι] in
/-- A trace word coming from a constant function detects any prescribed
column. -/
theorem phi_detects_coordinate (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) (c : AffineRelation.Column F t) :
    ∃ f : affineFunctions F D, phi input D f c ≠ 0 := by
  obtain ⟨a, ha⟩ := FiniteFieldTrace.exists_trace_mul_eq_one F input c.1.ne_zero
  let f : affineFunctions F D :=
    ⟨fun _ ↦ a, constant_mem_affineFunctions F D a⟩
  refine ⟨f, ?_⟩
  have hvalue : phi input D f c = 1 := by
    simpa [f, mul_comm] using ha
  rw [hvalue]
  exact one_ne_zero

omit [DecidableEq ι] in
/-- Constants distinguish columns with different nonzero field labels. -/
theorem phi_separates_of_fst_ne (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (p r : Fˣ) (x y : CoordinateSpace F t) (hpr : p ≠ r) :
    ∃ f : affineFunctions F D,
      phi input D f (p, x) ≠ phi input D f (r, y) := by
  have hprValue : (p : F) ≠ (r : F) := by
    intro h
    exact hpr (Units.ext h)
  have hsum : (p : F) + (r : F) ≠ 0 :=
    CharTwoTriples.add_ne_zero_of_ne hprValue
  obtain ⟨a, ha⟩ := FiniteFieldTrace.exists_trace_mul_eq_one F input hsum
  let f : affineFunctions F D :=
    ⟨fun _ ↦ a, constant_mem_affineFunctions F D a⟩
  refine ⟨f, ?_⟩
  intro heq
  have htrace :
      input.trace (a * ((p : F) + (r : F))) =
        phi input D f (p, x) + phi input D f (r, y) := by
    calc
      input.trace (a * ((p : F) + (r : F))) =
          input.trace (a * (p : F)) + input.trace (a * (r : F)) := by
            rw [mul_add, map_add]
      _ = phi input D f (p, x) + phi input D f (r, y) := by
        simp [f, mul_comm]
  rw [ha, heq, CharTwoTriples.add_self_eq_zero] at htrace
  exact one_ne_zero htrace

omit [Field F] [Fintype F] [CharP F 2] [Algebra F₂ F] in
/-- A coordinate at which two vectors differ. -/
theorem exists_coordinate_ne {x y : CoordinateSpace F t} (hxy : x ≠ y) :
    ∃ i : Fin t, x i ≠ y i := by
  by_contra h
  apply hxy
  funext i
  by_contra hi
  exact h ⟨i, hi⟩

omit [DecidableEq ι] in
/-- A globally linear function distinguishes columns with the same field
label and different affine-space positions. -/
theorem phi_separates_of_snd_ne (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (p : Fˣ) (x y : CoordinateSpace F t) (hxy : x ≠ y) :
    ∃ f : affineFunctions F D,
      phi input D f (p, x) ≠ phi input D f (p, y) := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne hxy
  have hxySum : x i + y i ≠ 0 :=
    CharTwoTriples.add_ne_zero_of_ne hi
  have hz : (p : F) * (x i + y i) ≠ 0 :=
    mul_ne_zero p.ne_zero hxySum
  obtain ⟨k, hk⟩ := FiniteFieldTrace.exists_trace_mul_eq_one F input hz
  let functional : CoordinateSpace F t →ₗ[F] F :=
    { toFun := fun z ↦ k * z i
      map_add' := fun z w ↦ by simp only [Pi.add_apply, mul_add]
      map_smul' := fun a z ↦ by
        simp [mul_left_comm] }
  let f : affineFunctions F D :=
    ⟨functional, linear_mem_affineFunctions F D functional⟩
  refine ⟨f, ?_⟩
  intro heq
  have htrace :
      input.trace (k * ((p : F) * (x i + y i))) =
        phi input D f (p, x) + phi input D f (p, y) := by
    calc
      input.trace (k * ((p : F) * (x i + y i))) =
          input.trace ((p : F) * (k * x i) + (p : F) * (k * y i)) := by
            congr 1
            ring
      _ = input.trace ((p : F) * (k * x i)) +
          input.trace ((p : F) * (k * y i)) := by rw [map_add]
      _ = phi input D f (p, x) + phi input D f (p, y) := by
        rfl
  rw [hk, heq, CharTwoTriples.add_self_eq_zero] at htrace
  exact one_ne_zero htrace

omit [DecidableEq ι] in
/-- Exact image-separation assertion from Lemma 3.6. -/
theorem phi_separates_coordinates (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) (c c' : AffineRelation.Column F t)
    (hne : c ≠ c') :
    ∃ f : affineFunctions F D, phi input D f c ≠ phi input D f c' := by
  rcases c with ⟨p, x⟩
  rcases c' with ⟨r, y⟩
  by_cases hpr : p = r
  · subst r
    apply phi_separates_of_snd_ne input D p x y
    intro hxy
    exact hne (Prod.ext rfl hxy)
  · exact phi_separates_of_fst_ne input D p r x y hpr

/-- The image of `Φ` detects every coordinate and separates every pair of
distinct coordinates. -/
theorem separatesCoordinates (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) :
    KernelDistance.SeparatesCoordinates (AffineRelation.matrix D) where
  detects := by
    intro c
    obtain ⟨f, hf⟩ := phi_detects_coordinate input D c
    exact ⟨phi input D f, phi_mem_kernel input D f, hf⟩
  separates := by
    intro c c' hne
    obtain ⟨f, hf⟩ := phi_separates_coordinates input D c c' hne
    exact ⟨phi input D f, phi_mem_kernel input D f, hf⟩

/-- The row code of the affine relation matrix has minimum distance at least
three, the final conclusion of Lemma 3.6. -/
theorem rowDistanceAtLeastThree (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) :
    RowDistanceAtLeastThree (AffineRelation.matrix D) :=
  KernelDistance.rowDistanceAtLeastThree_of_separates
    (AffineRelation.matrix D) (separatesCoordinates input D)

end AffineRelationKernel

end HDXLean
