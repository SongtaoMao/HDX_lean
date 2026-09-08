import HDXLean.BooleanCube
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Squarefree Cauchy--Binet expansion

This file proves the finite determinant calculation in Proposition 4.7.  A
matrix of the form `U * diagonal x * Zᵀ` is expanded into squarefree monomials
in the coordinates of `x`.  The coefficients are written without choosing an
ordering on a finite support: we sum over all injective assignments of one
coordinate to each row.  This is the ordering-free form of the usual product
of the two corresponding maximal minors.
-/

namespace HDXLean

open scoped BigOperators

namespace BooleanCubeMinorExpansion

variable {F : Type*} [CommRing F]
variable {R : Type*} [Fintype R] [DecidableEq R]
variable {t : ℕ}

/-- A square matrix written as a sum of rank-one matrices, one for each
coordinate.  Entrywise this is `U * diagonal x * Zᵀ`. -/
def coordinateMatrix (U Z : Matrix R (Fin t) F)
    (x : Fin t → F) : Matrix R R F :=
  fun i j ↦ ∑ k, U i k * x k * Z j k

/-- Matrix form of `coordinateMatrix`. -/
theorem coordinateMatrix_eq_mul_diagonal_transpose
    (U Z : Matrix R (Fin t) F) (x : Fin t → F) :
    coordinateMatrix U Z x = U * Matrix.diagonal x * Z.transpose := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal]
  rfl

/-- The set of coordinates used by an assignment of one coordinate to each
row. -/
def assignmentSupport (r : R → Fin t) : Finset (Fin t) :=
  Finset.univ.image r

/-- The summand attached to one row-to-coordinate assignment. -/
noncomputable def assignmentCoefficient (U Z : Matrix R (Fin t) F)
    (r : R → Fin t) : F := by
  classical
  exact (∏ i, U i (r i)) * Matrix.det (fun i j ↦ Z j (r i))

/-- Squarefree coefficients obtained by collecting the injective assignments
with the same support. -/
noncomputable def coefficients (U Z : Matrix R (Fin t) F) :
    BooleanCube.Coefficients (F := F) t := by
  classical
  exact fun S ↦ ∑ r : R → Fin t,
    if Function.Injective r then
      if assignmentSupport r = S then assignmentCoefficient U Z r else 0
    else 0

/-- A repeated coordinate gives two equal rows in the corresponding
determinant summand. -/
theorem assignment_det_eq_zero_of_not_injective
    (Z : Matrix R (Fin t) F) (r : R → Fin t)
    (hr : ¬ Function.Injective r) :
    Matrix.det (fun i j ↦ Z j (r i)) = 0 := by
  classical
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hr
  apply Matrix.det_zero_of_row_eq hne
  funext k
  simp [hij]

/-- An injective assignment turns the product indexed by rows into the
squarefree monomial indexed by its image. -/
theorem assignmentSupport_monomial
    (x : Fin t → F) (r : R → Fin t) (hr : Function.Injective r) :
    (∏ k ∈ assignmentSupport r, x k) = ∏ i, x (r i) := by
  classical
  unfold assignmentSupport
  exact Finset.prod_image (fun _ _ _ _ h ↦ hr h)

/-- The support of an injective assignment has exactly as many elements as
there are rows. -/
theorem assignmentSupport_card
    (r : R → Fin t) (hr : Function.Injective r) :
    (assignmentSupport r).card = Fintype.card R := by
  classical
  unfold assignmentSupport
  rw [Finset.card_image_iff.mpr]
  · simp
  · exact fun _ _ _ _ h ↦ hr h

/-- Raw multilinear determinant expansion, before repeated-coordinate terms
are removed. -/
theorem coordinateMatrix_det_assignment_expansion
    (U Z : Matrix R (Fin t) F) (x : Fin t → F) :
    (coordinateMatrix U Z x).det =
      ∑ r : R → Fin t,
        assignmentCoefficient U Z r * ∏ i, x (r i) := by
  classical
  change Matrix.detRowAlternating
      (fun i j ↦ ∑ k, U i k * x k * Z j k) = _
  have hrows :
      (fun i j ↦ ∑ k, U i k * x k * Z j k) =
        fun i ↦ ∑ k, (U i k * x k) • (fun j ↦ Z j k) := by
    funext i j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hrows]
  let g : R → Fin t → (R → F) :=
    fun i k ↦ (U i k * x k) • (fun j ↦ Z j k)
  have hexpand :
      Matrix.detRowAlternating (fun i ↦ ∑ k, g i k) =
        ∑ r : R → Fin t,
          Matrix.detRowAlternating (fun i ↦ g i (r i)) :=
    Matrix.detRowAlternating.toMultilinearMap.map_sum g
  change Matrix.detRowAlternating (fun i ↦ ∑ k, g i k) = _
  rw [hexpand]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [AlternatingMap.map_smul_univ]
  simp only [smul_eq_mul, assignmentCoefficient]
  rw [Finset.prod_mul_distrib]
  change
    ((∏ i, U i (r i)) * ∏ i, x (r i)) *
        Matrix.det (fun i j ↦ Z j (r i)) =
      ((∏ i, U i (r i)) * Matrix.det (fun i j ↦ Z j (r i))) *
        ∏ i, x (r i)
  ring

/-- Only injective assignments survive in the determinant expansion. -/
theorem coordinateMatrix_det_injective_expansion
    (U Z : Matrix R (Fin t) F) (x : Fin t → F) :
    (coordinateMatrix U Z x).det =
      ∑ r : R → Fin t,
        if Function.Injective r then
          assignmentCoefficient U Z r * ∏ i, x (r i)
        else 0 := by
  classical
  rw [coordinateMatrix_det_assignment_expansion]
  apply Finset.sum_congr rfl
  intro r _hr
  split_ifs with hinj
  · rfl
  · simp [assignmentCoefficient,
      assignment_det_eq_zero_of_not_injective Z r hinj]

/-- Evaluation of the collected squarefree coefficients recovers the
injective-assignment expansion. -/
theorem evaluate_coefficients
    (U Z : Matrix R (Fin t) F) (x : Fin t → F) :
    BooleanCube.evaluate (coefficients U Z) x =
      ∑ r : R → Fin t,
        if Function.Injective r then
          assignmentCoefficient U Z r * ∏ i, x (r i)
        else 0 := by
  classical
  unfold BooleanCube.evaluate coefficients
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hinj : Function.Injective r
  · simp only [hinj, if_true]
    rw [Finset.sum_eq_single (assignmentSupport r)]
    · rw [if_pos rfl, assignmentSupport_monomial x r hinj]
    · intro S _hS hSne
      rw [if_neg (Ne.symm hSne)]
      simp
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · simp [hinj]

/-- Cauchy--Binet in squarefree coefficient form. -/
theorem coordinateMatrix_det_eq_evaluate
    (U Z : Matrix R (Fin t) F) (x : Fin t → F) :
    (coordinateMatrix U Z x).det =
      BooleanCube.evaluate (coefficients U Z) x := by
  rw [coordinateMatrix_det_injective_expansion, evaluate_coefficients]

/-- The Cauchy--Binet coefficient vanishes outside homogeneous degree equal
to the number of rows. -/
theorem coefficients_eq_zero_of_card_ne
    (U Z : Matrix R (Fin t) F) (S : Finset (Fin t))
    (hcard : S.card ≠ Fintype.card R) :
    coefficients U Z S = 0 := by
  classical
  unfold coefficients
  apply Finset.sum_eq_zero
  intro r _hr
  by_cases hinj : Function.Injective r
  · rw [if_pos hinj]
    by_cases hs : assignmentSupport r = S
    · exfalso
      apply hcard
      rw [← hs]
      exact assignmentSupport_card r hinj
    · simp [hs]
  · simp [hinj]

section SelectedMinor

variable {C J : Type*}

/-- A selected maximal minor of a rectangular rank-one factorization. -/
noncomputable def selectedMinor
    (U : Matrix R (Fin t) F) (Z : Matrix C (Fin t) F)
    (select : J → R → C) (j : J) (x : Fin t → F) : F := by
  classical
  exact Matrix.det
    (coordinateMatrix U (fun a k ↦ Z (select j a) k) x)

/-- The squarefree coefficient vector of a selected maximal minor. -/
noncomputable def selectedMinorCoefficients
    (U : Matrix R (Fin t) F) (Z : Matrix C (Fin t) F)
    (select : J → R → C) (j : J) :
    BooleanCube.Coefficients (F := F) t :=
  coefficients U (fun a k ↦ Z (select j a) k)

theorem selectedMinor_eq_evaluate
    (U : Matrix R (Fin t) F) (Z : Matrix C (Fin t) F)
    (select : J → R → C) (j : J) (x : Fin t → F) :
    selectedMinor U Z select j x =
      BooleanCube.evaluate (selectedMinorCoefficients U Z select j) x := by
  exact coordinateMatrix_det_eq_evaluate _ _ _

/-- Function equality in exactly the form required by the Boolean-cube
evaluation-certificate constructor. -/
theorem evaluationLinear_selectedMinorCoefficients
    (U : Matrix R (Fin t) F) (Z : Matrix C (Fin t) F)
    (select : J → R → C) (j : J) :
    BooleanCube.evaluationLinear (F := F) t
        (selectedMinorCoefficients U Z select j) =
      selectedMinor U Z select j := by
  funext x
  exact (selectedMinor_eq_evaluate U Z select j x).symm

/-- Transfer the proved expansion across a paper-specific polynomial encoding
and a paper-specific identification of the determinant functions. -/
theorem evaluates_minor_of_identifications {P : Type*}
    (U : Matrix R (Fin t) F) (Z : Matrix C (Fin t) F)
    (select : J → R → C)
    (encoding : P → BooleanCube.Coefficients (F := F) t)
    (polynomialMinor : J → P) (minor : J → (Fin t → F) → F)
    (hcoeff : ∀ j,
      encoding (polynomialMinor j) = selectedMinorCoefficients U Z select j)
    (hminor : ∀ j, selectedMinor U Z select j = minor j) :
    ∀ j, BooleanCube.evaluationLinear (F := F) t
        (encoding (polynomialMinor j)) = minor j := by
  intro j
  rw [hcoeff j, evaluationLinear_selectedMinorCoefficients, hminor j]

end SelectedMinor

end BooleanCubeMinorExpansion

end HDXLean
