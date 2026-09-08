import HDXLean.AlgebraicGeometry
import HDXLean.BooleanCubeMinorExpansion

/-!
# Cauchy--Binet coordinates for the Section 4 multiplication matrix

The paper chooses evaluation functionals forming a basis of `Wᵛ` and writes
the multiplication matrix as `U * diagonal x * Zᵀ`.  The structure below is
the exact finite datum recording that coordinate choice.  From it, literal
selected maximal minors acquire computed squarefree coefficient vectors, and
their evaluation identity is proved by `BooleanCubeMinorExpansion`.
-/

namespace HDXLean

open scoped BigOperators

universe u v

section

variable {F : Type u} [Field F]
variable {t : ℕ} {I : Type v} [Fintype I]
variable (D : DirectionSet F t I)

/-- A coordinate presentation of the multiplication matrix in the form
`M(x) = U * diagonal x * Zᵀ`.  This is the finite linear-coordinate datum
obtained after choosing the evaluation functionals used as a basis in the
proof of Proposition 4.7. -/
structure CoordinateRankOneFactorization
    (M : MultiplicationMatrixData D) where
  coordinateU : Matrix M.Row (Fin t) F
  coordinateZ : Matrix M.Column (Fin t) F
  entry_eq_sum_rankOne : ∀ row column x,
    M.entry row column x =
      ∑ k, coordinateU row k * x k * coordinateZ column k

namespace CoordinateRankOneFactorization

variable {D}
variable {M : MultiplicationMatrixData D}

/-- The squarefree coefficient vector computed for every literal selected
maximal minor. -/
noncomputable def selectedMaximalMinorCoefficients {J : Type*}
    (factorization : CoordinateRankOneFactorization D M)
    (selection : MaximalMinorSelection D M J) (j : J) :
    BooleanCube.Coefficients (F := F) t := by
  classical
  exact BooleanCubeMinorExpansion.selectedMinorCoefficients
    factorization.coordinateU factorization.coordinateZ selection.column j

/-- Concrete Cauchy--Binet expansion of each selected maximal minor as a
squarefree polynomial function. -/
theorem selectedMaximalMinor_eq_evaluate {J : Type*}
    (factorization : CoordinateRankOneFactorization D M)
    (selection : MaximalMinorSelection D M J) (j : J)
    (x : CoordinateSpace F t) :
    selectedMaximalMinor D M selection j x =
      BooleanCube.evaluate
        (factorization.selectedMaximalMinorCoefficients selection j) x := by
  classical
  unfold selectedMaximalMinor selectedMaximalMinorCoefficients
  change Matrix.det
      (Matrix.of fun row column ↦
        M.entry row (selection.column j column) x) =
    BooleanCube.evaluate
      (BooleanCubeMinorExpansion.coefficients
        factorization.coordinateU
        (fun column k ↦
          factorization.coordinateZ (selection.column j column) k)) x
  rw [show
      Matrix.of (fun row column ↦
        M.entry row (selection.column j column) x) =
        BooleanCubeMinorExpansion.coordinateMatrix
          factorization.coordinateU
          (fun column k ↦
            factorization.coordinateZ (selection.column j column) k) x by
    ext row column
    rw [Matrix.of_apply]
    exact factorization.entry_eq_sum_rankOne row
      (selection.column j column) x]
  exact BooleanCubeMinorExpansion.coordinateMatrix_det_eq_evaluate _ _ _

/-- Function equality in the exact shape of
`BooleanCubeEvaluationCertificate.evaluates_minor`. -/
theorem evaluationLinear_selectedMaximalMinorCoefficients {J : Type*}
    (factorization : CoordinateRankOneFactorization D M)
    (selection : MaximalMinorSelection D M J) (j : J) :
    BooleanCube.evaluationLinear (F := F) t
        (factorization.selectedMaximalMinorCoefficients selection j) =
      selectedMaximalMinor D M selection j := by
  funext x
  exact (factorization.selectedMaximalMinor_eq_evaluate selection j x).symm

/-- The cited consequence of Eisenbud's theorem, parameterized directly by
the explicit Cauchy--Binet coefficient family.  Its sole mathematical proof
field is the cited polynomial-independence conclusion; there is no additional
evaluation or encoding certificate. -/
structure EisenbudCoefficientIndependenceInput {J : Type*}
    (factorization : CoordinateRankOneFactorization D M)
    (selection : MaximalMinorSelection D M J) where
  oneGeneric : Prop
  oneGeneric_proof : oneGeneric
  maximalMinorCoefficients_independent : oneGeneric →
    LinearIndependent F
      (factorization.selectedMaximalMinorCoefficients selection)

/-- Proposition 4.7 with all project-owned algebra internal: independence of
the explicit coefficient family is transported through the proved injective
Boolean-cube evaluation map to independence of the selected minors as
functions. -/
theorem selectedMaximalMinor_linearIndependent {J : Type*}
    (factorization : CoordinateRankOneFactorization D M)
    (selection : MaximalMinorSelection D M J)
    (eisenbud : EisenbudCoefficientIndependenceInput factorization selection) :
    LinearIndependent F (selectedMaximalMinor D M selection) := by
  have hkernel :
      LinearMap.ker (BooleanCube.evaluationLinear (F := F) t) = ⊥ :=
    LinearMap.ker_eq_bot.mpr
      (BooleanCube.evaluationLinear_injective (F := F) t)
  have hmapped :=
    (eisenbud.maximalMinorCoefficients_independent
      eisenbud.oneGeneric_proof).map'
        (BooleanCube.evaluationLinear (F := F) t) hkernel
  rw [show selectedMaximalMinor D M selection =
      BooleanCube.evaluationLinear (F := F) t ∘
        factorization.selectedMaximalMinorCoefficients selection by
    funext j
    exact (factorization.evaluationLinear_selectedMaximalMinorCoefficients
      selection j).symm]
  exact hmapped

end CoordinateRankOneFactorization

end

end HDXLean
