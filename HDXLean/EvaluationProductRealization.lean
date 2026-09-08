import HDXLean.EvaluationMultiplication
import HDXLean.SectionFourAssembly
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Realizing product coefficients in the actual function algebra

One evaluation basis is used for directions, matrix entries, and coefficient
reconstruction. Its dual coordinates reconstruct the product functions, so
the product-realization identity needed for scalar-extension genericity is
a theorem, not a new assumption.

The input still includes the genuine function spaces, their multiplication
and evaluations, and compatibility with their maps into the function algebra.
Geometric integrality and the cited Riemann--Roch facts are not reproved here.
-/

namespace HDXLean.EvaluationProductRealization

open scoped BigOperators TensorProduct

universe u v w

section Reconstruction

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
  [FiniteDimensional F W] {t : ℕ}

/-- Function coordinates dual to the chosen basis of evaluation
functionals. The `i`th coordinate of `w` is exactly `(b i) w`. -/
noncomputable def primalCoordinates
    (b : Module.Basis (Fin t) F (Module.Dual F W)) : W ≃ₗ[F] (Fin t → F) :=
  (Module.evalEquiv F W).trans b.dualBasis.equivFun

theorem primalCoordinates_apply
    (b : Module.Basis (Fin t) F (Module.Dual F W)) (w : W) (i : Fin t) :
    primalCoordinates b w i = b i w := by
  simp only [primalCoordinates, LinearEquiv.trans_apply,
    Module.Basis.dualBasis_equivFun, Module.evalEquiv_apply, Module.Dual.eval_apply]

/-- Reconstruct a function from its evaluations in this basis and then
map it to the actual function algebra. -/
noncomputable def realize {A : Type*} [AddCommGroup A] [Module F A]
    (b : Module.Basis (Fin t) F (Module.Dual F W)) (embedW : W →ₗ[F] A) :
    (Fin t → F) →ₗ[F] A :=
  embedW.comp (primalCoordinates b).symm.toLinearMap

theorem realize_primalCoordinates {A : Type*} [AddCommGroup A] [Module F A]
    (b : Module.Basis (Fin t) F (Module.Dual F W)) (embedW : W →ₗ[F] A)
    (w : W) : realize b embedW (primalCoordinates b w) = embedW w := by
  exact congrArg embedW ((primalCoordinates b).symm_apply_apply w)

end Reconstruction

section Products

variable {F U V W A I R C : Type*} [Field F]
  [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]
  [CommRing A] [Algebra F A] {t : ℕ}

/-- The rank-one coefficient vector is exactly the evaluation-coordinate
vector of the actual product function. -/
theorem product_coordinates
    (b : Module.Basis (Fin t) F (Module.Dual F W))
    (multiply : U →ₗ[F] V →ₗ[F] W)
    (e : I → Module.Dual F W) (eU : I → Module.Dual F U)
    (eV : I → Module.Dual F V)
    (hmul : ∀ i x y, e i (multiply x y) = eU i x * eV i y)
    (selected : Fin t → I) (hselected : ∀ i, e (selected i) = b i)
    (x : U) (y : V) :
    (fun i ↦ eU (selected i) x * eV (selected i) y) =
      primalCoordinates b (multiply x y) := by
  funext i
  rw [primalCoordinates_apply, ← hselected i, hmul]

/-- Reconstructing the computed coordinate products gives the product in
the function algebra. Compatibility of genuine multiplication, not a
coefficient-independence or 1-genericity statement, is the input. -/
theorem realize_product_coefficients
    (b : Module.Basis (Fin t) F (Module.Dual F W))
    (multiply : U →ₗ[F] V →ₗ[F] W)
    (e : I → Module.Dual F W) (eU : I → Module.Dual F U)
    (eV : I → Module.Dual F V)
    (hmul : ∀ i x y, e i (multiply x y) = eU i x * eV i y)
    (selected : Fin t → I) (hselected : ∀ i, e (selected i) = b i)
    (embedU : U →ₗ[F] A) (embedV : V →ₗ[F] A) (embedW : W →ₗ[F] A)
    (hcompat : ∀ x y, embedW (multiply x y) = embedU x * embedV y)
    (x : U) (y : V) :
    realize b embedW (fun i ↦ eU (selected i) x * eV (selected i) y) =
      embedU x * embedV y := by
  rw [product_coordinates b multiply e eU eV hmul selected hselected,
    realize_primalCoordinates, hcompat]

/-- Injective maps into the function algebra preserve the selected
independent families, using the existing linear-independence map theorem. -/
theorem linearIndependent_embedded (embedU : U →ₗ[F] A)
    (hinjective : Function.Injective embedU) {u : R → U}
    (hu : LinearIndependent F u) : LinearIndependent F (embedU ∘ u) :=
  hu.map' embedU (LinearMap.ker_eq_bot.mpr hinjective)

end Products

section Assembly

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {K : Type v} [Field K] [IsAlgClosed K] [Algebra F K]
variable {A : Type w} [CommRing A] [Algebra F A]
variable [IsDomain (K ⊗[F] A)]
variable {U V W : Type*}
  [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]
variable (P : SquareFieldParameters F) {g : ℕ}
variable (level : RiemannRochLevelInput P g)

/-- Assemble the original concrete-level output from genuine multiplication
and a single basis drawn from the actual evaluation family. Point selection,
matrix entries, rank-one factorization, coefficient realization, scalar
genericity, and minor independence are all filled internally.

`hD` ensures that this very basis is also the one defining the directions.
`hb` is the basis-membership output of `exists_evaluation_basis`; it does not
supply an independently chosen matrix-coordinate system.
-/
noncomputable def concreteLevelFromEvaluationBasis
    (hk : 0 < g / 4)
    (b : Module.Basis (Fin level.t) F (Module.Dual F W))
    (multiply : U →ₗ[F] V →ₗ[F] W)
    (u : Fin (g / 4) → U) (v : Fin (3 * (g / 4)) → V)
    (hu : LinearIndependent F u) (hv : LinearIndependent F v)
    (e : Fin ((P.q - 2) * g) → Module.Dual F W)
    (eU : Fin ((P.q - 2) * g) → Module.Dual F U)
    (eV : Fin ((P.q - 2) * g) → Module.Dual F V)
    (hmul : ∀ i x y, e i (multiply x y) = eU i x * eV i y)
    (hb : ∀ i, ∃ j, e j = b i)
    (hD : ∀ i, level.directions.representative i = b.equivFun (e i))
    (embedU : U →ₗ[F] A) (embedV : V →ₗ[F] A) (embedW : W →ₗ[F] A)
    (hinjectiveU : Function.Injective embedU)
    (hinjectiveV : Function.Injective embedV)
    (hcompat : ∀ x y, embedW (multiply x y) = embedU x * embedV y)
    (eisenbud : OneGenericMatrix.EisenbudMinimalGeneratorsInput.{v,0} K) :
    ConcreteMaximalMinorLevelData P level := by
  classical
  let selected : Fin level.t → Fin ((P.q - 2) * g) := fun i ↦ Classical.choose (hb i)
  have hselected : ∀ i, e (selected i) = b i := fun i ↦ Classical.choose_spec (hb i)
  refine SectionFourCanonicalMinors.concreteLevelFromIntegralMultiplication
    P level hk (EvaluationMultiplication.entry b multiply u v)
    (fun i r ↦ eU i (u r)) (fun i c ↦ eV i (v c)) ?_
    (fun r i ↦ eU (selected i) (u r))
    (fun c i ↦ eV (selected i) (v c)) ?_
    (realize b embedW)
    (linearIndependent_embedded embedU hinjectiveU hu)
    (linearIndependent_embedded embedV hinjectiveV hv) ?_ eisenbud
  · intro i r c
    rw [hD]
    exact EvaluationMultiplication.entry_at_point b multiply u v e eU eV hmul i r c
  · intro r c x
    exact EvaluationMultiplication.entry_eq_sum b multiply u v e eU eV hmul
      selected hselected r c x
  · intro r c
    exact realize_product_coefficients b multiply e eU eV hmul selected hselected
      embedU embedV embedW hcompat (u r) (v c)

end Assembly

end HDXLean.EvaluationProductRealization
