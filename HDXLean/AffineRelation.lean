import HDXLean.CharTwoTriples
import HDXLean.Directions
import HDXLean.FiniteFieldTrace
import HDXLean.KernelDistance

/-!
# The affine-restriction relation matrix

This is the concrete incidence matrix of Section 3.2.  A row is indexed by a
nonzero representative of a projective direction, a base point, and an
unordered characteristic-two triple.  Its three columns are
`(p, x + p • b)` as `p` ranges over the triple.
-/

namespace HDXLean

open scoped BigOperators

namespace AffineRelation

universe u v

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
  [CharP F 2] [Algebra F₂ F]
variable {t : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The unordered triple index set `ℒ_F`. -/
abbrev TripleIndex (F : Type u) [Field F] [Fintype F] [DecidableEq F] :=
  {ell : Finset F // ell ∈ CharTwoTriples.family F}

/-- Columns are indexed by `Fˣ × F^t`. -/
abbrev Column (F : Type u) [Field F] (t : ℕ) :=
  Fˣ × CoordinateSpace F t

/-- A row index packages `b`, `x`, and `ell` from the paper.  The pair
`(direction, scale)` represents the actual vector
`scale • D.representative direction`. -/
structure RowIndex (F : Type u) [Field F] [Fintype F] [DecidableEq F]
    (t : ℕ) (ι : Type v) [Fintype ι] [DecidableEq ι] where
  direction : ι
  scale : Fˣ
  base : CoordinateSpace F t
  triple : TripleIndex F

def rowIndexEquiv :
    RowIndex F t ι ≃ ι × Fˣ × (CoordinateSpace F t × TripleIndex F) where
  toFun r := (r.direction, r.scale, r.base, r.triple)
  invFun r := ⟨r.1, r.2.1, r.2.2.1, r.2.2.2⟩
  left_inv r := by cases r; rfl
  right_inv r := by rcases r with ⟨i, s, x, ell⟩; rfl

noncomputable instance rowIndexDecidableEq : DecidableEq (RowIndex F t ι) :=
  Classical.decEq _

noncomputable instance rowIndexFintype : Fintype (RowIndex F t ι) :=
  Fintype.ofEquiv
    (ι × Fˣ × (CoordinateSpace F t × TripleIndex F))
    (rowIndexEquiv (F := F) (t := t) (ι := ι)).symm

/-- The actual nonzero direction vector represented by a row. -/
def directionVector (D : DirectionSet F t ι)
    (r : RowIndex F t ι) : CoordinateSpace F t :=
  (r.scale : F) • D.representative r.direction

omit [CharP F 2] [Algebra F₂ F] in
theorem directionVector_ne_zero (D : DirectionSet F t ι)
    (r : RowIndex F t ι) : directionVector D r ≠ 0 := by
  exact smul_ne_zero r.scale.ne_zero (D.representative_ne_zero r.direction)

/-- Turn an element of a family triple into a unit; family triples never
contain zero. -/
def tripleMemberUnit (ell : TripleIndex F)
    (p : {z : F // z ∈ ell.1}) : Fˣ :=
  Units.mk0 p.1 fun hp ↦
    CharTwoTriples.family_member_zero_not_mem ell.2 (hp ▸ p.2)

omit [Algebra F₂ F] in
@[simp]
theorem tripleMemberUnit_val (ell : TripleIndex F)
    (p : {z : F // z ∈ ell.1}) :
    ((tripleMemberUnit ell p : Fˣ) : F) = p.1 :=
  rfl

/-- The column corresponding to a member of the row's field triple. -/
def rowColumn (D : DirectionSet F t ι) (r : RowIndex F t ι)
    (p : {z : F // z ∈ r.triple.1}) : Column F t :=
  (tripleMemberUnit r.triple p,
    r.base + p.1 • directionVector D r)

omit [Algebra F₂ F] in
theorem rowColumn_injective (D : DirectionSet F t ι)
    (r : RowIndex F t ι) : Function.Injective (rowColumn D r) := by
  intro p q hpq
  apply Subtype.ext
  have hfirst := congrArg (fun c : Column F t ↦ ((c.1 : Fˣ) : F)) hpq
  simpa [rowColumn] using hfirst

/-- The three-element support of a row. -/
noncomputable def rowEntries (D : DirectionSet F t ι)
    (r : RowIndex F t ι) : Finset (Column F t) := by
  classical
  exact r.triple.1.attach.image (rowColumn D r)

omit [Algebra F₂ F] in
theorem rowEntries_card (D : DirectionSet F t ι)
    (r : RowIndex F t ι) : (rowEntries D r).card = 3 := by
  classical
  rw [rowEntries, Finset.card_image_of_injective _ (rowColumn_injective D r),
    Finset.card_attach, CharTwoTriples.family_member_card r.triple.2]

/-- The binary incidence matrix `H_D`. -/
noncomputable def matrix (D : DirectionSet F t ι) :
    BinaryMatrix (RowIndex F t ι) (Column F t) := by
  classical
  exact fun r c ↦ if c ∈ rowEntries D r then 1 else 0

omit [Algebra F₂ F] in
theorem matrix_apply_ne_zero_iff (D : DirectionSet F t ι)
    (r : RowIndex F t ι) (c : Column F t) :
    matrix D r c ≠ 0 ↔ c ∈ rowEntries D r := by
  classical
  simp [matrix]

omit [Algebra F₂ F] in
theorem rowSupport_matrix (D : DirectionSet F t ι)
    (r : RowIndex F t ι) :
    rowSupport (matrix D) r = rowEntries D r := by
  classical
  ext c
  simp [rowSupport, matrix_apply_ne_zero_iff]

omit [Algebra F₂ F] in
/-- First assertion of Lemma 3.5: every relation row has weight three. -/
theorem rowsHaveWeightThree (D : DirectionSet F t ι) :
    RelationMatrix.RowsHaveWeightThree (matrix D) := by
  intro r
  rw [rowSupport_matrix, rowEntries_card]

end AffineRelation

end HDXLean
