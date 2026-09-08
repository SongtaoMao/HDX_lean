import HDXLean.SectionFourSubspaces
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Cited one-point Riemann--Roch model

This interface states the standard function-space facts used from Stichtenoth
[Sti09, Chapter 1; Theorems 1.5.15 and 1.5.17] and the zero-divisor bound.
Those external results are inputs, not theorems reproved in this project.

The model uses the algebra of functions regular away from the distinguished
point. Unlike the full function field, this algebra admits evaluation at
every selected rational point. Its one-point spaces are actual submodules,
evaluations are algebra maps, and vanishing spaces are actual intersections
of evaluation kernels. Integral scalar extension is the geometric-integrality
fact used in the paper. No direction set, multiplication matrix, genericity,
minor independence, or final expansion conclusion occurs in this interface.

This is an axiomatic function-space model of the cited curve facts, not a
separate formalization of schemes or a proof of Riemann--Roch. The tower
existence citation must supply a common sequence of these models.
-/

namespace HDXLean.CurveRiemannRochCited

open scoped TensorProduct

universe u v

section Vanishing

variable {F A Point : Type*} [Field F] [CommRing A] [Algebra F A]

/-- Restrict a rational-point evaluation to an actual function subspace. -/
def evaluationOn (L : Submodule F A) (evaluation : Point → A →ₐ[F] F)
    (p : Point) : Module.Dual F L :=
  (evaluation p).toLinearMap.comp L.subtype

/-- The literal space of sections vanishing at all points of `S`.
For `L=L(m P_infinity)` this is `L(m P_infinity - sum_{p in S} p)`. -/
def vanishingSpace (L : Submodule F A) (evaluation : Point → A →ₐ[F] F)
    (S : Finset Point) : Submodule F L :=
  S.inf fun p ↦ LinearMap.ker (evaluationOn L evaluation p)

end Vanishing

/-- Precisely the cited algebraic-geometry data required at one curve level.
`Point` is a finite set of distinct rational points away from `P_infinity`;
the distinguished point is not counted in this type. -/
structure OnePointData (F : Type u) [Field F] [DecidableEq F]
    (K : Type v) [Field K] [Algebra F K] (genus : ℕ) where
  Regular : Type u
  [regularCommRing : CommRing Regular]
  [regularAlgebra : Algebra F Regular]
  [geometricIntegral : IsDomain (K ⊗[F] Regular)]
  Point : Type u
  [pointFintype : Fintype Point]
  [pointDecidableEq : DecidableEq Point]
  space : ℕ → Submodule F Regular
  [spaceFinite : ∀ m, FiniteDimensional F (space m)]
  evaluation : Point → Regular →ₐ[F] F
  one_mem : ∀ m, (1 : Regular) ∈ space m
  multiply_mem : ∀ a b (x y : Regular),
    x ∈ space a → y ∈ space b → x * y ∈ space (a + b)
  /-- Stichtenoth's general RR lower bound for an effective one-point divisor. -/
  rr_lower : ∀ m, m + 1 - genus ≤ Module.finrank F (space m)
  /-- RR equality for a one-point divisor with distinct rational zeros imposed.
  The premise is `m - |S| > 2g-2`, written without integer subtraction. -/
  rr_vanishing : ∀ m (S : Finset Point),
    2 * genus + S.card ≤ m + 1 →
      Module.finrank F (vanishingSpace (space m) evaluation S) =
        m + 1 - genus - S.card
  /-- A nonzero section of `L(m P_infinity)` has at most `m` rational zeros
  away from the distinguished point. -/
  zero_bound : ∀ m (f : space m), f ≠ 0 →
    (Finset.univ.filter fun p ↦ evaluation p f = 0).card ≤ m

attribute [instance] OnePointData.regularCommRing OnePointData.regularAlgebra
  OnePointData.geometricIntegral OnePointData.pointFintype
  OnePointData.pointDecidableEq OnePointData.spaceFinite

namespace OnePointData

variable {F : Type u} [Field F] [DecidableEq F]
  {K : Type v} [Field K] [Algebra F K]
variable {g : ℕ} (data : OnePointData F K g)

/-- The actual evaluation on `L(m P_infinity)`. -/
def eval (m : ℕ) (p : data.Point) : Module.Dual F (data.space m) :=
  evaluationOn (data.space m) data.evaluation p

/-- The section equal to the constant function one. -/
def one (m : ℕ) : data.space m := ⟨1, data.one_mem m⟩

theorem eval_one (m : ℕ) (p : data.Point) : data.eval m p (data.one m) = 1 :=
  (data.evaluation p).map_one

/-- The product is the actual product in the regular function algebra,
restricted using the cited `L(a P_infinity)L(b P_infinity)` inclusion. -/
def multiplication (a b : ℕ) :
    data.space a →ₗ[F] data.space b →ₗ[F] data.space (a + b) where
  toFun x :=
    { toFun := fun y ↦ ⟨x.val * y.val, data.multiply_mem a b x y x.property y.property⟩
      map_add' := by intro y z; apply Subtype.ext; exact mul_add _ _ _
      map_smul' := by intro c y; apply Subtype.ext; exact mul_smul_comm _ _ _ }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact add_mul _ _ _
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact smul_mul_assoc _ _ _

theorem eval_multiplication (a b : ℕ) (p : data.Point)
    (x : data.space a) (y : data.space b) :
    data.eval (a + b) p (data.multiplication a b x y) =
      data.eval a p x * data.eval b p y :=
  (data.evaluation p).map_mul x.val y.val

end OnePointData

end HDXLean.CurveRiemannRochCited
