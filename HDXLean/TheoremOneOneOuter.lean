import HDXLean.AlgebraicGeometryConcrete
import HDXLean.ParameterChoice
import HDXLean.TheoremOneOne
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The outer quantifiers of Theorem 1.1

`TheoremOneOne` proves the construction after a square finite field has been
fixed.  This file performs the remaining elementary parameter selection.  For
every `lambda > 0` it chooses `q = 2^h`, takes the concrete field
`GaloisField 2 (2 * h)`, and then invokes the cited tower/Section 4 inputs.

The record `TheoremOneOneLiterature` is deliberately uniform in `h`.  Its
fields are exactly the external results cited by the paper; finite-field
existence, cardinality, the choice of `q`, and the final assembly are proved
inside Lean.
-/

namespace HDXLean

namespace ConcreteSquareField

/-- A canonical concrete realization of the square field of order
`(2^h)^2`. -/
abbrev Extension (h : ℕ) := GaloisField 2 (2 * h)

noncomputable instance extensionFintype (h : ℕ) : Fintype (Extension h) :=
  Fintype.ofFinite (Extension h)

noncomputable instance extensionDecidableEq (h : ℕ) :
    DecidableEq (Extension h) :=
  Classical.decEq (Extension h)

/-- The concrete Galois field has the cardinality required by
`SquareFieldParameters`. -/
theorem card_extension (h : ℕ) (hh : 0 < h) :
    Fintype.card (Extension h) = (2 ^ h) ^ 2 := by
  rw [Fintype.card_eq_nat_card, GaloisField.card 2 (2 * h) (by omega)]
  calc
    2 ^ (2 * h) = 2 ^ (h * 2) := by rw [Nat.mul_comm]
    _ = (2 ^ h) ^ 2 := by rw [pow_mul]

/-- Package `GaloisField 2 (2h)` as the paper's square-field parameter. -/
noncomputable def parameters (h : ℕ) (hh : 3 ≤ h) :
    SquareFieldParameters (Extension h) where
  h := h
  q := 2 ^ h
  h_pos := by omega
  q_eq_two_pow := rfl
  q_ge_eight := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by omega) hh
  card_field := card_extension h (by omega)

end ConcreteSquareField

/--
The cited inputs used by the construction, supplied uniformly for every
binary square field selected by the elementary parameter argument.

This is the sole literature boundary of the outer theorem.  In particular,
it does not contain the finite Fourier diagonalization, the relation-matrix
counting lemmas, or any of the numerical choice of `q`; those are proved in
the surrounding Lean development.
-/
structure TheoremOneOneLiterature : Type 1 where
  tower : ∀ (h : ℕ) (hh : 3 ≤ h),
    GarciaStichtenothTowerInput (ConcreteSquareField.parameters h hh)
  sectionFour : ∀ (h : ℕ) (hh : 3 ≤ h),
    ConcreteSectionFourInput (ConcreteSquareField.parameters h hh) (tower h hh)
  trace : ∀ (h : ℕ) (_hh : 3 ≤ h),
    FiniteFieldTrace.LiteratureInput (ConcreteSquareField.Extension h)
  compiler : RelationCompiler.LiteratureInput

/-- The genuine outer form of Theorem 1.1: every positive target expansion
parameter produces a family.  The field and its size are constructed in Lean;
only the results explicitly cited by the paper are fields of `literature`. -/
theorem theoremOneOne {lambda : ℝ} (hlambda : 0 < lambda)
    (literature : TheoremOneOneLiterature) :
    Nonempty (TwoDimensionalFamily lambda) := by
  let choice := chooseSpectralField hlambda
  let P := ConcreteSquareField.parameters choice.h choice.h_at_least_three
  have hchoice : 4 / ((P.q : ℝ) - 2) < lambda := by
    simpa [P, ConcreteSquareField.parameters, choice.q_eq] using
      choice.spectral_inequality
  exact theoremOneOne_of_cited_inputs P
    (literature.tower choice.h choice.h_at_least_three)
    (literature.sectionFour choice.h choice.h_at_least_three).toSectionFourInput
    (literature.trace choice.h choice.h_at_least_three)
    hchoice literature.compiler

end HDXLean
