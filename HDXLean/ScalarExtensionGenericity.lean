import HDXLean.OneGenericMatrix
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Scalar extension of the multiplication matrix

The field extension is an actual tensor product. Independent functions stay
independent after extension of scalars. Geometric integrality enters through
the precise algebraic hypothesis that the base-changed function algebra is
an integral domain, not through an assumed matrix-genericity conclusion.

The curve/Riemann--Roch integration must supply the function algebra, its
geometric-integrality instance, the chosen independent function families,
and the identity realizing matrix coefficients as their products. Everything
from those data to 1-genericity over the extended field is proved here.
-/

namespace HDXLean.ScalarExtensionGenericity

open scoped BigOperators TensorProduct

universe u v w

section LinearBaseChange

variable {F : Type u} {K : Type v} [Field F] [Field K] [Algebra F K]
variable {A : Type w} [AddCommGroup A] [Module F A]

/-- Flat scalar extension preserves a selected independent family, with
the extended vectors explicitly equal to `1 ⊗ u i`. -/
theorem linearIndependent_one_tmul {I : Type*} {u : I → A}
    (hu : LinearIndependent F u) :
    LinearIndependent K (fun i ↦ (1 : K) ⊗ₜ[F] u i) :=
  Module.Flat.linearIndependent_one_tmul hu

/-- Extend a linear realization of coefficient vectors and identify the
scalar extension of coordinate space with the new coordinate space. -/
noncomputable def realizationBaseChange {t : ℕ}
    (realize : (Fin t → F) →ₗ[F] A) :
    (Fin t → K) →ₗ[K] K ⊗[F] A :=
  (realize.baseChange K).comp
    (TensorProduct.piScalarRight F K K (Fin t)).symm.toLinearMap

/-- The extended realization agrees with scalar extension on every
ground-field coefficient vector. -/
theorem realizationBaseChange_algebraMap {t : ℕ}
    (realize : (Fin t → F) →ₗ[F] A) (x : Fin t → F) :
    realizationBaseChange realize (fun i ↦ algebraMap F K (x i)) =
      (1 : K) ⊗ₜ[F] realize x := by
  have hcoordinates :
      (TensorProduct.piScalarRight F K K (Fin t)).symm
        (fun i ↦ algebraMap F K (x i)) = (1 : K) ⊗ₜ[F] x := by
    apply (TensorProduct.piScalarRight F K K (Fin t)).injective
    simp only [LinearEquiv.apply_symm_apply, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
    funext i
    simp only [Algebra.smul_def, mul_one]
  simp only [realizationBaseChange, LinearMap.comp_apply,
    LinearEquiv.coe_coe, hcoordinates, LinearMap.baseChange_tmul]

end LinearBaseChange

section IntegralMultiplication

variable {F : Type u} {K : Type v} [Field F] [Field K] [Algebra F K]
variable {A : Type w} [CommRing A] [Algebra F A]
variable {R C : Type*} [Fintype R] [Fintype C] {t : ℕ}

/-- The coefficient vectors of the actual multiplication matrix after
extension of its ground field. -/
def extendedMatrix (M : R → C → Fin t → F) : R → C → Fin t → K :=
  fun r c i ↦ algebraMap F K (M r c i)

omit [Fintype R] [Fintype C] in
/-- The extended coefficient realization sends each entry to the product
of the extended row and column functions. -/
theorem realizationBaseChange_entry
    (realize : (Fin t → F) →ₗ[F] A)
    (M : R → C → Fin t → F) (u : R → A) (v : C → A)
    (hentry : ∀ r c, realize (M r c) = u r * v c) (r : R) (c : C) :
    realizationBaseChange realize (extendedMatrix (K := K) M r c) =
      ((1 : K) ⊗ₜ[F] u r) * ((1 : K) ⊗ₜ[F] v c) := by
  change realizationBaseChange realize (fun i ↦ algebraMap F K (M r c i)) = _
  rw [realizationBaseChange_algebraMap, hentry,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- The extended coefficient bilinear map realizes the multiplication of
the extended linear combinations. This is the scalar-extension version of
the generalized-row/generalized-column calculation. -/
theorem generalizedEntry_realization
    (realize : (Fin t → F) →ₗ[F] A)
    (M : R → C → Fin t → F) (u : R → A) (v : C → A)
    (hentry : ∀ r c, realize (M r c) = u r * v c)
    (a : R → K) (b : C → K) :
    realizationBaseChange realize
        (∑ r, ∑ c, (a r * b c) • extendedMatrix (K := K) M r c) =
      (∑ r, a r • ((1 : K) ⊗ₜ[F] u r)) *
        (∑ c, b c • ((1 : K) ⊗ₜ[F] v c)) := by
  simp only [map_sum, map_smul, realizationBaseChange_entry realize M u v hentry]
  exact OneGenericMatrix.generalizedEntry_eq_product
    (LinearMap.mul K (K ⊗[F] A))
    (fun r ↦ (1 : K) ⊗ₜ[F] u r) (fun c ↦ (1 : K) ⊗ₜ[F] v c) a b

/-- Geometric integrality and scalar extension of the selected independent
functions imply actual 1-genericity over the extension field.

No injectivity of `realize` is required: if an extended coefficient vector
were zero, its realized nonzero product would be zero as well. -/
theorem isOneGeneric_of_integral_baseChange
    [IsDomain (K ⊗[F] A)]
    (realize : (Fin t → F) →ₗ[F] A)
    (M : R → C → Fin t → F) {u : R → A} {v : C → A}
    (hu : LinearIndependent F u) (hv : LinearIndependent F v)
    (hentry : ∀ r c, realize (M r c) = u r * v c) :
    OneGenericMatrix.IsOneGeneric (F := K) (extendedMatrix (K := K) M) := by
  have huK := linearIndependent_one_tmul (K := K) hu
  have hvK := linearIndependent_one_tmul (K := K) hv
  have hgeneric := OneGenericMatrix.isOneGeneric_of_no_zero_products
    (LinearMap.mul K (K ⊗[F] A))
    (fun x y hx hy ↦ mul_ne_zero hx hy) huK hvK
  intro a b ha hb hz
  apply hgeneric a b ha hb
  have hrealized := congrArg (realizationBaseChange realize) hz
  simp only [map_sum, map_smul, map_zero,
    realizationBaseChange_entry realize M u v hentry] at hrealized
  exact hrealized

/-- The form used directly by the Cauchy--Binet certificate: coordinates
of the multiplication matrix are the products of the corresponding row
and column evaluations. -/
theorem rankOneCoordinates_isOneGeneric
    [IsDomain (K ⊗[F] A)]
    (realize : (Fin t → F) →ₗ[F] A)
    (U : R → Fin t → F) (Z : C → Fin t → F)
    {u : R → A} {v : C → A}
    (hu : LinearIndependent F u) (hv : LinearIndependent F v)
    (hentry : ∀ r c, realize (fun i ↦ U r i * Z c i) = u r * v c) :
    OneGenericMatrix.IsOneGeneric (F := K)
      (fun r c i ↦ algebraMap F K (U r i) * algebraMap F K (Z c i)) := by
  have h := isOneGeneric_of_integral_baseChange (K := K) realize
    (fun r c i ↦ U r i * Z c i) hu hv hentry
  have heq : extendedMatrix (K := K) (fun r c i ↦ U r i * Z c i) =
      (fun r c i ↦ algebraMap F K (U r i) * algebraMap F K (Z c i)) := by
    funext r c i
    exact map_mul (algebraMap F K) (U r i) (Z c i)
  rw [heq] at h
  exact h

/-- A faithful realization of the scalar-extended function algebra inside
a field supplies the integral-domain hypothesis internally. Such a field
may be the function field of the geometrically integral base-changed curve.
Faithfulness is about the concrete algebra map, not a matrix conclusion. -/
theorem rankOneCoordinates_isOneGeneric_of_field_model
    {L : Type*} [Field L] [Algebra K L]
    (fieldModel : K ⊗[F] A →ₐ[K] L)
    (hfaithful : Function.Injective fieldModel)
    (realize : (Fin t → F) →ₗ[F] A)
    (U : R → Fin t → F) (Z : C → Fin t → F)
    {u : R → A} {v : C → A}
    (hu : LinearIndependent F u) (hv : LinearIndependent F v)
    (hentry : ∀ r c, realize (fun i ↦ U r i * Z c i) = u r * v c) :
    OneGenericMatrix.IsOneGeneric (F := K)
      (fun r c i ↦ algebraMap F K (U r i) * algebraMap F K (Z c i)) := by
  letI : IsDomain (K ⊗[F] A) := hfaithful.isDomain fieldModel
  exact rankOneCoordinates_isOneGeneric realize U Z hu hv hentry

end IntegralMultiplication

end HDXLean.ScalarExtensionGenericity
