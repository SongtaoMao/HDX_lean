import HDXLean.CurveRiemannRochLevel
import HDXLean.TowerPointCapacity

/-!
# Reusing the Section 4 family proof with a common cited curve model

The external input is a Garcia--Stichtenoth sequence with its general
Riemann--Roch function-space model and Eisenbud's cited determinantal result.
Selected points, directions, matrix entries, genericity, and independent
minor functions are not inputs. The original asymptotic family proof is
reused unchanged through a constructed `ConcreteSectionFourInput`.

The one-point models are axiomatic models of the cited geometric facts;
this module does not claim a scheme-level construction or reproof of them.
Algorithms and complexity are intentionally outside its conclusions.
-/

namespace HDXLean.CurveTowerAssembly

universe u

/-- External facts for Section 4, concerning one common sequence of curves.
The point types exclude the distinguished point at infinity, as in the
latest manuscript's Garcia--Stichtenoth statement. -/
structure CitedInput {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (P : SquareFieldParameters F) where
  Extension : Type u
  [extensionField : Field Extension]
  [extensionAlgClosed : IsAlgClosed Extension]
  [extensionAlgebra : Algebra F Extension]
  genus : ℕ → ℕ
  curve : ∀ r, CurveRiemannRochCited.OnePointData F Extension (genus r)
  genus_growth : TendsToInfinity genus
  point_ratio : PointGenusRatioConverges
    (fun r ↦ Fintype.card (curve r).Point) genus (P.q - 1 : ℕ)
  eisenbud : OneGenericMatrix.EisenbudMinimalGeneratorsInput.{u,0} Extension

attribute [instance] CitedInput.extensionField CitedInput.extensionAlgClosed
  CitedInput.extensionAlgebra

namespace CitedInput

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {P : SquareFieldParameters F} (input : CitedInput P)

/-- Reuse the old tower record, deriving its spare-point capacity from the
ratio limit. Its point-count field here counts the available points away
from infinity; the stronger spare-point inequality follows from the limit.
The excluded algorithmic marker is `True`, not an algorithm certificate. -/
def tower : GarciaStichtenothTowerInput P :=
  GarciaStichtenothTowerInput.ofGrowth P input.genus
    (fun r ↦ Fintype.card (input.curve r).Point)
    input.genus_growth input.point_ratio

/-- A sufficient genus threshold is chosen from the cited growth, not
assumed as another construction property. -/
noncomputable def threshold : ℕ := Classical.choose (input.genus_growth 4)

theorem genus_ge_four (r : ℕ) (hr : input.threshold ≤ r) :
    4 ≤ input.genus r := Classical.choose_spec (input.genus_growth 4) r hr

/-- All per-level Section 4 output, using the same curve data at this index. -/
noncomputable def levelWithMinors (r : ℕ) (hr : input.threshold ≤ r)
    (hpoints : 1 + (P.q - 2) * input.tower.genus r ≤
      input.tower.rationalPointCount r) :
    Σ level : RiemannRochLevelInput P (input.tower.genus r),
      ConcreteMaximalMinorLevelData P level :=
  CurveRiemannRochLevel.levelWithMinors P (input.curve r)
    (input.genus_ge_four r hr) (by
      change (P.q - 2) * input.genus r ≤ Fintype.card (input.curve r).Point
      change 1 + (P.q - 2) * input.genus r ≤ Fintype.card (input.curve r).Point
        at hpoints
      omega) input.eisenbud

/-- Fill the old Section 4 interface internally, preserving its downstream
proofs. No direction, matrix, or independent-minor certificate is supplied
by the caller. -/
noncomputable def sectionFour : ConcreteSectionFourInput P input.tower where
  constructionThreshold := input.threshold
  level r hr hp := (input.levelWithMinors r hr hp).1
  minors r hr hp := (input.levelWithMinors r hr hp).2
  explicitAssembly := True
  explicitAssembly_proof := trivial

/-- Lemma 3.2 via the existing asymptotic argument, now from the common
cited curve-function-space model and cited determinantal theorem. -/
theorem directionFamily (input : CitedInput P) : Nonempty (Lemma32DirectionFamily P) :=
  ConcreteSectionFourInput.lemma_3_2_concrete P input.sectionFour

end CitedInput

end HDXLean.CurveTowerAssembly
