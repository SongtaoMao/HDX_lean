import HDXLean.AffineRelationKernel
import HDXLean.AlgebraicGeometry
import Mathlib.FieldTheory.Finiteness

/-!
# The binary dimension of the square field

This file supplies the exact finite-field cardinality calculation used in
Lemma 3.6.  For the paper's field `F` of cardinality
`q² = (2^h)²`, its dimension over `F₂` is exactly `2h`.  Substitution in
the injectivity estimate for the affine-function map then gives the displayed
nullity lower bound from the paper.
-/

namespace HDXLean

universe u v

namespace SquareFieldParameters

variable {F : Type u} [Field F] [Fintype F] [Algebra F₂ F]

/-- The square field `F` has binary vector-space dimension exactly `2h`. -/
theorem binary_finrank_eq_two_mul_h (P : SquareFieldParameters F) :
    Module.finrank F₂ F = 2 * P.h := by
  apply Nat.pow_right_injective (a := 2) (by norm_num)
  calc
    2 ^ Module.finrank F₂ F = Fintype.card F := by
      rw [Module.card_eq_pow_finrank (K := F₂), ZMod.card]
    _ = P.q ^ 2 := P.card_field
    _ = (2 ^ P.h) ^ 2 := by rw [P.q_eq_two_pow]
    _ = 2 ^ (2 * P.h) := by
      rw [Nat.mul_comm 2 P.h, pow_mul]

end SquareFieldParameters

namespace AffineRelationKernel

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
  [CharP F 2] [Algebra F₂ F]
variable {t : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The exact Lemma 3.6 nullity estimate after evaluating `[F : F₂] = 2h`. -/
theorem two_mul_h_mul_affineFinrank_le_nullity
    (P : SquareFieldParameters F)
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) :
    (2 * P.h) * Module.finrank F (affineFunctions F D) ≤
      RelationMatrix.nullity (AffineRelation.matrix D) := by
  rw [← P.binary_finrank_eq_two_mul_h]
  exact finrank_mul_finrank_le_nullity input D

end AffineRelationKernel

end HDXLean
