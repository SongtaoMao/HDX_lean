import HDXLean.OneGenericMatrix
import HDXLean.BooleanCubeMinorExpansion
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Literal polynomial minors and squarefree coefficient vectors

This module connects the actual polynomial determinants in the determinantal
theorem with the coefficient vectors used by the finite-field evaluation
argument. The Cauchy--Binet identity is applied over a polynomial ring, not
inferred from equality of finite-field polynomial functions.
-/

namespace HDXLean

open scoped BigOperators

namespace PolynomialMinorBridge

universe u v

section PolynomialEncoding

variable {F : Type*} [CommRing F] {t : ℕ}

/-- The genuine polynomial whose squarefree coefficients are `c`. -/
noncomputable def polynomialEncoding (t : ℕ) :
    BooleanCube.Coefficients (F := F) t →ₗ[F] MvPolynomial (Fin t) F where
  toFun c := ∑ S : Finset (Fin t),
    MvPolynomial.C (c S) * ∏ i ∈ S, MvPolynomial.X i
  map_add' c d := by
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply,
      MvPolynomial.smul_eq_C_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    ring

theorem polynomialEncoding_apply (c : BooleanCube.Coefficients (F := F) t) :
    polynomialEncoding t c = ∑ S : Finset (Fin t),
      MvPolynomial.C (c S) * ∏ i ∈ S, MvPolynomial.X i := rfl

end PolynomialEncoding

section RingHomTransport

variable {F K R : Type*} [CommRing F] [CommRing K]
variable [Fintype R] [DecidableEq R] {t : ℕ}

open BooleanCubeMinorExpansion

/-- The assignment coefficient commutes with every ring homomorphism. -/
theorem assignmentCoefficient_map (f : F →+* K)
    (U Z : Matrix R (Fin t) F) (r : R → Fin t) :
    assignmentCoefficient (fun i x ↦ f (U i x))
      (fun i x ↦ f (Z i x)) r = f (assignmentCoefficient U Z r) := by
  classical
  unfold assignmentCoefficient
  rw [map_mul, map_prod]
  congr 1
  exact (f.map_det (Matrix.of fun i j ↦ Z j (r i))).symm

/-- Thus the full squarefree Cauchy--Binet coefficients commute with scalar
extension, including extension to a polynomial coefficient ring. -/
theorem coefficients_map (f : F →+* K)
    (U Z : Matrix R (Fin t) F) (S : Finset (Fin t)) :
    coefficients (fun i x ↦ f (U i x)) (fun i x ↦ f (Z i x)) S =
      f (coefficients U Z S) := by
  classical
  unfold coefficients
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : Function.Injective r
  · by_cases hs : assignmentSupport r = S
    · simp only [hr, hs, if_true]
      exact assignmentCoefficient_map f U Z r
    · simp only [hr, hs, if_true, if_false, map_zero]
  · simp only [hr, if_false, map_zero]

end RingHomTransport

section LiteralDeterminants

variable {F : Type u} [Field F] {k m t : ℕ} {J : Type v}

open OneGenericMatrix BooleanCubeMinorExpansion

/-- Cauchy--Binet as an identity of actual polynomials. It is valid even
when `F` is finite, since it is proved in the polynomial ring itself. -/
theorem polynomialMinor_eq_encoding
    (U : Matrix (Fin k) (Fin t) F) (Z : Matrix (Fin m) (Fin t) F)
    (column : Fin k → Fin m) :
    polynomialMinor F (fun r c i ↦ U r i * Z c i) column =
      polynomialEncoding t (coefficients U (fun r i ↦ Z (column r) i)) := by
  classical
  let U' : Matrix (Fin k) (Fin t) (MvPolynomial (Fin t) F) :=
    fun r i ↦ MvPolynomial.C (U r i)
  let Z' : Matrix (Fin k) (Fin t) (MvPolynomial (Fin t) F) :=
    fun r i ↦ MvPolynomial.C (Z (column r) i)
  have hmatrix :
      (fun i j ↦ linearForm F (fun x ↦ U i x * Z (column j) x)) =
        coordinateMatrix U' Z' MvPolynomial.X := by
    funext i j
    unfold linearForm coordinateMatrix
    apply Finset.sum_congr rfl
    intro x _
    dsimp [U', Z']
    rw [map_mul]
    ring
  unfold polynomialMinor
  rw [hmatrix, coordinateMatrix_det_eq_evaluate, polynomialEncoding_apply]
  unfold BooleanCube.evaluate
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  exact coefficients_map MvPolynomial.C U (fun r i ↦ Z (column r) i) S

/-- Polynomial independence forces independence of the computed squarefree
coefficient vectors; no injectivity assumption or opaque certificate is
required in this direction. -/
theorem coefficients_linearIndependent_of_polynomialMinors
    (U : Matrix (Fin k) (Fin t) F) (Z : Matrix (Fin m) (Fin t) F)
    (column : J → Fin k → Fin m)
    (hpoly : LinearIndependent F
      (fun j ↦ polynomialMinor F (fun r c i ↦ U r i * Z c i) (column j))) :
    LinearIndependent F (selectedMinorCoefficients U Z column) := by
  apply LinearIndependent.of_comp (polynomialEncoding t)
  have heq : polynomialEncoding t ∘ selectedMinorCoefficients U Z column =
      (fun j ↦ polynomialMinor F (fun r c i ↦ U r i * Z c i) (column j)) := by
    funext j
    exact (polynomialMinor_eq_encoding U Z (column j)).symm
  rw [heq]
  exact hpoly

/-- Actual 1-genericity over an algebraically closed field and the stated
determinantal citation imply independence of the literal computed
squarefree coefficients, with all transport proved internally. -/
theorem coefficients_linearIndependent [IsAlgClosed F]
    (input : EisenbudMinimalGeneratorsInput.{u,v} F)
    (hk : 0 < k) (hkm : k ≤ m)
    (U : Matrix (Fin k) (Fin t) F) (Z : Matrix (Fin m) (Fin t) F)
    (hgeneric : IsOneGeneric (F := F) (fun r c i ↦ U r i * Z c i))
    (column : J → Fin k → Fin m)
    (hinjective : ∀ j, Function.Injective (column j))
    (hdistinct : Function.Injective (fun j ↦ Set.range (column j))) :
    LinearIndependent F (selectedMinorCoefficients U Z column) := by
  apply coefficients_linearIndependent_of_polynomialMinors U Z column
  exact polynomialMinors_linearIndependent F input hk hkm
    (fun r c i ↦ U r i * Z c i) hgeneric column hinjective hdistinct

end LiteralDeterminants

section ScalarDescent

variable {F : Type u} {K : Type*} [Field F] [Field K]
variable {k m t : ℕ} {J : Type v}

open OneGenericMatrix BooleanCubeMinorExpansion

/-- Independence of the extended coefficient vectors descends along a
field embedding. Only finite linear relations are used. -/
theorem coefficients_linearIndependent_descend
    (f : F →+* K)
    (U : Matrix (Fin k) (Fin t) F) (Z : Matrix (Fin m) (Fin t) F)
    (column : J → Fin k → Fin m)
    (hK : LinearIndependent K
      (selectedMinorCoefficients (fun r i ↦ f (U r i))
        (fun c i ↦ f (Z c i)) column)) :
    LinearIndependent F (selectedMinorCoefficients U Z column) := by
  classical
  rw [linearIndependent_iff']
  intro s a hz j hj
  have hcoeff : ∀ j S, selectedMinorCoefficients
      (fun r i ↦ f (U r i)) (fun c i ↦ f (Z c i)) column j S =
      f (selectedMinorCoefficients U Z column j S) := by
    intro j S
    exact coefficients_map f U (fun r i ↦ Z (column j r) i) S
  have hrelation :
      (∑ j ∈ s, f (a j) • selectedMinorCoefficients
        (fun r i ↦ f (U r i)) (fun c i ↦ f (Z c i)) column j) = 0 := by
    funext S
    have hzero := congrFun hz S
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hzero ⊢
    simp_rw [hcoeff, ← map_mul]
    rw [← map_sum, hzero, map_zero]
  have hjzero : f (a j) = 0 :=
    linearIndependent_iff'.mp hK s (fun j ↦ f (a j)) hrelation j hj
  exact f.injective (hjzero.trans (map_zero f).symm)

/-- Complete polynomial/coefficient/scalar descent bridge used over a
finite ground field. The 1-genericity hypothesis is imposed over the actual
algebraically closed extension field, never only over the finite field. -/
theorem coefficients_linearIndependent_of_extension
    [IsAlgClosed K] (f : F →+* K)
    (input : EisenbudMinimalGeneratorsInput.{_,v} K)
    (hk : 0 < k) (hkm : k ≤ m)
    (U : Matrix (Fin k) (Fin t) F) (Z : Matrix (Fin m) (Fin t) F)
    (hgeneric : IsOneGeneric (F := K)
      (fun r c i ↦ f (U r i) * f (Z c i)))
    (column : J → Fin k → Fin m)
    (hinjective : ∀ j, Function.Injective (column j))
    (hdistinct : Function.Injective (fun j ↦ Set.range (column j))) :
    LinearIndependent F (selectedMinorCoefficients U Z column) := by
  apply coefficients_linearIndependent_descend f U Z column
  exact coefficients_linearIndependent input hk hkm
    (fun r i ↦ f (U r i)) (fun c i ↦ f (Z c i)) hgeneric
    column hinjective hdistinct

end ScalarDescent

end PolynomialMinorBridge

end HDXLean
