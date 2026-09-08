import HDXLean.SectionFourCanonicalMinors
import HDXLean.AlgebraicGeometryConcrete
import HDXLean.ScalarExtensionGenericity

/-!
# Connecting the constructed rectangular data to the main proof

The following definitions are output adapters. Coefficient independence
has already been proved by `SectionFourCanonicalMinors.concreteLevel`;
this file does not add a new cited independence assumption.
-/

namespace HDXLean.SectionFourCanonicalMinors.RectangularLevelData

universe u
variable {F : Type u} [Field F] [Fintype F]
variable {P : SquareFieldParameters F} {g : ℕ}
variable {level : RiemannRochLevelInput P g}

/-- The literal rectangular matrix, with its finite index types made explicit. -/
noncomputable def matrix (data : RectangularLevelData P level) :
    MultiplicationMatrixData level.directions where
  Row := Fin (g / 4)
  Column := Fin (3 * (g / 4))
  rowFintype := inferInstance
  columnFintype := inferInstance
  entry := data.entry
  uEvaluation := data.uEvaluation
  zEvaluation := data.zEvaluation
  entry_at_evaluation := data.entry_at_evaluation

/-- All maximal minors, with no caller-supplied selection or count. -/
noncomputable def selection (data : RectangularLevelData P level) :
    MaximalMinorSelection level.directions data.matrix
      (CanonicalMaximalMinors.Index (g / 4) (3 * (g / 4))) where
  column := CanonicalMaximalMinors.column
  column_injective := CanonicalMaximalMinors.column_injective

/-- The already established factorization in the historical matrix interface. -/
noncomputable def factorization (data : RectangularLevelData P level) :
    CoordinateRankOneFactorization level.directions data.matrix where
  coordinateU := data.coordinateU
  coordinateZ := data.coordinateZ
  entry_eq_sum_rankOne := data.entry_eq_sum_rankOne

/-- The two interfaces compute the very same coefficient family. -/
theorem coefficients_eq (data : RectangularLevelData P level) :
    data.factorization.selectedMaximalMinorCoefficients data.selection =
      BooleanCubeMinorExpansion.selectedMinorCoefficients data.coordinateU data.coordinateZ
        (@CanonicalMaximalMinors.column (g / 4) (3 * (g / 4))) := by
  funext j
  simp only [CoordinateRankOneFactorization.selectedMaximalMinorCoefficients,
    factorization, selection, matrix]
  congr 1

/-- Independence crosses the adapter, without a new hypothesis. -/
theorem coefficientFamily_linearIndependent (data : RectangularLevelData P level) :
    LinearIndependent F
      (data.factorization.selectedMaximalMinorCoefficients data.selection) := by
  rw [coefficients_eq]
  exact data.coefficients_independent

/-- Fill the old output certificate from the constructed rectangular data.
The old proposition field carries an already proved fact here, and is not
exposed as a fresh literature premise. -/
noncomputable def toConcrete (data : RectangularLevelData P level) :
    ConcreteMaximalMinorLevelData P level where
  matrix := data.matrix
  MinorIndex := CanonicalMaximalMinors.Index (g / 4) (3 * (g / 4))
  index_card := CanonicalMaximalMinors.index_card _ _
  selection := data.selection
  factorization := data.factorization
  eisenbud :=
    { oneGeneric := LinearIndependent F
        (data.factorization.selectedMaximalMinorCoefficients data.selection)
      oneGeneric_proof := data.coefficientFamily_linearIndependent
      maximalMinorCoefficients_independent := fun h ↦ h }

/-- The actual rectangular minors yield the paper's dimension lower bound. -/
theorem minorCount_le_finrank (data : RectangularLevelData P level) :
    Nat.choose (3 * (g / 4)) (g / 4) ≤
      Module.finrank F (affineFunctions F level.directions) :=
  data.toConcrete.minorCount_le_finrank

end HDXLean.SectionFourCanonicalMinors.RectangularLevelData

namespace HDXLean.SectionFourCanonicalMinors

open scoped BigOperators TensorProduct

universe u v w
variable {F : Type u} [Field F] [Fintype F]
variable {K : Type v} [Field K] [IsAlgClosed K] [Algebra F K]
variable {A : Type w} [CommRing A] [Algebra F A]
variable [IsDomain (K ⊗[F] A)]
variable (P : SquareFieldParameters F) {g : ℕ}
variable (level : RiemannRochLevelInput P g)

/-- Feed the original Section 4 proof with the actual multiplication data.
Genericity and coefficient independence are conclusions, not inputs.
The function algebra, its geometric integrality, the independent functions
and their realization still need to come from the cited curve/RR instance.
Eisenbud's general determinantal result remains an explicit cited input. -/
noncomputable def concreteLevelFromIntegralMultiplication
    (hk : 0 < g / 4)
    (entry : Fin (g / 4) → Fin (3 * (g / 4)) →
      CoordinateSpace F level.t →ₗ[F] F)
    (uEvaluation : Fin ((P.q - 2) * g) → Fin (g / 4) → F)
    (zEvaluation : Fin ((P.q - 2) * g) → Fin (3 * (g / 4)) → F)
    (hevaluation : ∀ i row column,
      entry row column (level.directions.representative i) =
        uEvaluation i row * zEvaluation i column)
    (U : Matrix (Fin (g / 4)) (Fin level.t) F)
    (Z : Matrix (Fin (3 * (g / 4))) (Fin level.t) F)
    (hfactorization : ∀ row column x,
      entry row column x = ∑ i, U row i * x i * Z column i)
    (realize : (Fin level.t → F) →ₗ[F] A)
    {u : Fin (g / 4) → A} {z : Fin (3 * (g / 4)) → A}
    (hu : LinearIndependent F u) (hz : LinearIndependent F z)
    (hproducts : ∀ row column,
      realize (fun i ↦ U row i * Z column i) = u row * z column)
    (eisenbud : OneGenericMatrix.EisenbudMinimalGeneratorsInput.{v,0} K) :
    ConcreteMaximalMinorLevelData P level :=
  (concreteLevel P level hk entry uEvaluation zEvaluation hevaluation U Z
    hfactorization (algebraMap F K) eisenbud
    (ScalarExtensionGenericity.rankOneCoordinates_isOneGeneric
      realize U Z hu hz hproducts)).toConcrete

end HDXLean.SectionFourCanonicalMinors
