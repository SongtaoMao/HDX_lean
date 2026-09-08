import HDXLean.AlgebraicGeometry
import HDXLean.PolynomialMinorBridge
import HDXLean.CanonicalMaximalMinors

/-!
# Constructing the Section 4 minor certificate

The actual rectangular dimensions, all column subsets, and the independent
Cauchy--Binet coefficients are constructed in this module. The remaining
geometric input is the multiplication/evaluation
presentation and its actual 1-genericity over an algebraically closed
extension. Neither the desired dimension bound nor coefficient independence
is an input to this constructor.

This new rectangular datum is not yet converted to the historical
`ConcreteMaximalMinorLevelData`. That integration is a separate obligation;
the outer theorem does not automatically switch to the path proved here.
-/

namespace HDXLean

open scoped BigOperators

universe u v

namespace SectionFourCanonicalMinors

variable {F : Type u} [Field F] [Fintype F]
variable {K : Type v} [Field K] [IsAlgClosed K]
variable (P : SquareFieldParameters F) {g : ℕ}
variable (level : RiemannRochLevelInput P g)

/-- Rectangular multiplication data with canonical, internally counted
minor indices. The constructor below proves its independence field from
the actual matrix and the cited determinantal theorem. -/
structure RectangularLevelData where
  entry : Fin (g / 4) → Fin (3 * (g / 4)) → CoordinateSpace F level.t →ₗ[F] F
  uEvaluation : Fin ((P.q - 2) * g) → Fin (g / 4) → F
  zEvaluation : Fin ((P.q - 2) * g) → Fin (3 * (g / 4)) → F
  entry_at_evaluation : ∀ i row column,
    entry row column (level.directions.representative i) =
      uEvaluation i row * zEvaluation i column
  coordinateU : Matrix (Fin (g / 4)) (Fin level.t) F
  coordinateZ : Matrix (Fin (3 * (g / 4))) (Fin level.t) F
  entry_eq_sum_rankOne : ∀ row column x,
    entry row column x = ∑ i, coordinateU row i * x i * coordinateZ column i
  coefficients_independent : LinearIndependent F
    (BooleanCubeMinorExpansion.selectedMinorCoefficients coordinateU coordinateZ
      (@CanonicalMaximalMinors.column (g / 4) (3 * (g / 4))))

/-- Build all rectangular maximal-minor data using precisely `k=floor(g/4)`
rows and `3k` columns. Independent polynomial generators are obtained only
from the actual extended coefficient matrix and the stated citation. -/
noncomputable def concreteLevel
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
    (f : F →+* K)
    (eisenbud : OneGenericMatrix.EisenbudMinimalGeneratorsInput.{v,0} K)
    (hgeneric : OneGenericMatrix.IsOneGeneric (F := K)
      (fun row column i ↦ f (U row i) * f (Z column i))) :
    RectangularLevelData P level := by
  classical
  have hcoeff0 (h : OneGenericMatrix.IsOneGeneric (F := K)
      (fun row column i ↦ f (U row i) * f (Z column i))) :
      LinearIndependent F
        (BooleanCubeMinorExpansion.selectedMinorCoefficients U Z
          (@CanonicalMaximalMinors.column (g / 4) (3 * (g / 4)))) := by
    exact PolynomialMinorBridge.coefficients_linearIndependent_of_extension
      (F := F) (K := K) (k := g / 4) (m := 3 * (g / 4))
      (t := level.t)
      (J := CanonicalMaximalMinors.Index (g / 4) (3 * (g / 4)))
      f eisenbud hk (by omega) U Z h CanonicalMaximalMinors.column
      CanonicalMaximalMinors.column_injective
      (CanonicalMaximalMinors.column_range_injective _ _)
  exact
    { entry := entry
      uEvaluation := uEvaluation
      zEvaluation := zEvaluation
      entry_at_evaluation := hevaluation
      coordinateU := U
      coordinateZ := Z
      entry_eq_sum_rankOne := hfactorization
      coefficients_independent := hcoeff0 hgeneric }

end SectionFourCanonicalMinors

end HDXLean
