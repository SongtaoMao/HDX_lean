import HDXLean.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Cited finite-field trace facts

The paper invokes Lidl--Niederreiter, Theorems 2.23 and 2.24.  Rather than
postulating global axioms, this file packages precisely the two facts used by
Sections 3.2 and 3.3: nondegeneracy of the trace pairing and additive-character
orthogonality.
-/

namespace HDXLean

open scoped BigOperators

namespace FiniteFieldTrace

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra F₂ F]

/-- The sign character associated with a binary-valued trace. -/
def signCharacter (trace : F →ₗ[F₂] F₂) (z : F) : ℝ :=
  if trace z = 0 then 1 else -1

/-- Exact input from the cited finite-field trace theorems. -/
structure LiteratureInput where
  trace : F →ₗ[F₂] F₂
  pairing_nondegenerate :
    ∀ z : F, (∀ p : F, trace (p * z) = 0) → z = 0
  character_orthogonality : ∀ z : F,
    (∑ p : F, signCharacter F trace (p * z)) =
      if z = 0 then (Fintype.card F : ℝ) else 0

theorem exists_trace_mul_ne_zero (input : LiteratureInput F)
    {z : F} (hz : z ≠ 0) :
    ∃ p : F, input.trace (p * z) ≠ 0 := by
  by_contra h
  apply hz
  apply input.pairing_nondegenerate z
  intro p
  by_contra hp
  exact h ⟨p, hp⟩

theorem exists_trace_mul_eq_one (input : LiteratureInput F)
    {z : F} (hz : z ≠ 0) :
    ∃ p : F, input.trace (p * z) = 1 := by
  obtain ⟨p, hp⟩ := exists_trace_mul_ne_zero F input hz
  exact ⟨p, Fin.eq_one_of_ne_zero _ hp⟩

@[simp]
theorem signCharacter_zero (input : LiteratureInput F) :
    signCharacter F input.trace 0 = 1 := by
  simp [signCharacter]

theorem character_sum_nonzero (input : LiteratureInput F)
    {z : F} (hz : z ≠ 0) :
    (∑ p : F, signCharacter F input.trace (p * z)) = 0 := by
  rw [input.character_orthogonality, if_neg hz]

theorem character_sum_zero (input : LiteratureInput F) :
    (∑ p : F, signCharacter F input.trace (p * 0)) =
      (Fintype.card F : ℝ) := by
  simpa only [mul_zero, if_pos] using input.character_orthogonality 0

end FiniteFieldTrace

end HDXLean
