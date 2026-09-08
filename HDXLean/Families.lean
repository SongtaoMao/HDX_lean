import HDXLean.Asymptotics
import HDXLean.Basic

/-!
# The two asymptotic conclusions of the paper

These structures state the mathematical content of Theorems 1.1 and 1.2 while
keeping all hidden constants explicit through the predicates in
`HDXLean.Asymptotics`.  Simplicity, purity, full support of the top-face
measure, and translation invariance are already part of `MeasuredComplex` and
`CayleyComplex`.
-/

namespace HDXLean

/-- A sequence is eventually bounded by a constant times the binary logarithm
of another sequence. -/
def LogarithmicallyBounded (f g : ℕ → ℕ) : Prop :=
  LinearBounded f fun r ↦ Nat.log2 (g r)

/-- The complete mathematical output asserted by Theorem 1.1. -/
structure TwoDimensionalFamily (lambda : ℝ) where
  ambientDimension : ℕ → ℕ
  complex : (r : ℕ) → CayleyComplex (V := Fin (ambientDimension r) → F₂)
  dimension_eq : ∀ r, (complex r).complex.dim = 2
  unweighted : ∀ r, (complex r).complex.IsUnweighted
  localExpansion : ∀ r,
    (complex r).complex.IsTwoSidedLocalSpectralExpander lambda
  ambientDimension_tendsToInfinity : TendsToInfinity ambientDimension
  degree_polynomial :
    PolynomiallyBounded (fun r ↦ (complex r).cayley.degree) ambientDimension
  edgeCodegree : ℕ → ℕ
  edgeCodegree_eq : ∀ r x y,
    x ≠ y → (complex r).complex.IsFace {x, y} →
      (complex r).complex.edgeCodegree x y = edgeCodegree r
  edgeCodegree_logarithmic :
    LogarithmicallyBounded edgeCodegree ambientDimension

/-- The number of vertices in a binary coordinate space. -/
def binaryVertexCount (n : ℕ) : ℕ := 2 ^ n

theorem binaryVertexCount_card (n : ℕ) :
    Fintype.card (Fin n → F₂) = binaryVertexCount n := by
  simp [binaryVertexCount, ZMod.card]

/-- The polynomial Cayley-degree assertion in Theorem 1.1 implies the stated
polylogarithmic bound in the actual number of vertices. -/
theorem TwoDimensionalFamily.degree_polylogarithmic
    {lambda : ℝ} (family : TwoDimensionalFamily lambda) :
    PolylogarithmicallyBounded
      (fun r ↦ (family.complex r).cayley.degree)
      (fun r ↦ binaryVertexCount (family.ambientDimension r)) := by
  exact family.degree_polynomial.polylogarithmic_of_vertexCount_pow_two
    (fun r ↦ rfl)

/-- A higher-dimensional family with the qualitative and polynomial-degree
properties used by the original weighted-lift development. -/
structure HigherDimensionalFamily (d : ℕ) where
  ambientDimension : ℕ → ℕ
  complex : (r : ℕ) → CayleyComplex (V := Fin (ambientDimension r) → F₂)
  dimension_eq : ∀ r, (complex r).complex.dim = d
  localExpansion : ∀ r,
    (complex r).complex.IsTwoSidedLocalSpectralExpander (1 / (d : ℝ))
  ambientDimension_tendsToInfinity : TendsToInfinity ambientDimension
  degree_polynomial :
    PolynomiallyBounded (fun r ↦ (complex r).cayley.degree) ambientDimension

/-- The strengthened family interface in the current Theorem 1.2.  In
addition to the codimension-two bound and connectivity, the Cayley degree is
Theta of the ambient binary dimension. -/
structure LinearDegreeHigherDimensionalFamily (d : ℕ)
    extends HigherDimensionalFamily d where
  degree_theta :
    ThetaLinear
      (fun r ↦ (complex r).cayley.degree)
      ambientDimension

/-- The polynomial Cayley-degree assertion in Theorem 1.2 is polylogarithmic
in the number of vertices. -/
theorem HigherDimensionalFamily.degree_polylogarithmic
    {d : ℕ} (family : HigherDimensionalFamily d) :
    PolylogarithmicallyBounded
      (fun r ↦ (family.complex r).cayley.degree)
      (fun r ↦ binaryVertexCount (family.ambientDimension r)) := by
  exact family.degree_polynomial.polylogarithmic_of_vertexCount_pow_two
    (fun r ↦ rfl)

end HDXLean
