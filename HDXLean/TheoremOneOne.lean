import HDXLean.SectionThreeAsymptotics

/-!
# Assembly of Theorem 1.1

This file composes the algebraic-geometric direction family, the concrete
affine relation matrices, and the cited relation compiler.  All asymptotic
claims are proved in `SectionThreeAsymptotics`; the finite Fourier bridge is
proved internally in `FiniteFourierBasis`.
-/

namespace HDXLean

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  [CharP F 2] [Algebra F₂ F]

/-- A direction family from Lemma 3.2 produces the family of Theorem 1.1. -/
noncomputable def theoremOneOneFromDirections {lambda : ℝ}
    (P : SquareFieldParameters F)
    (family : Lemma32DirectionFamily P)
    (traceInput : FiniteFieldTrace.LiteratureInput F)
    (hchoice : 4 / ((P.q : ℝ) - 2) < lambda)
    (compiler : RelationCompiler.LiteratureInput) :
    TwoDimensionalFamily lambda :=
  SectionThreeFamily.toTwoDimensionalFamily P family traceInput hchoice
    (SectionThreeFamily.asymptoticCertificate P family traceInput) compiler

/-- Theorem 1.1 from the explicitly represented cited inputs.  Its finite
Fourier step is discharged by the internally proved basis theorem. -/
theorem theoremOneOne_of_cited_inputs {lambda : ℝ}
    (P : SquareFieldParameters F)
    (tower : GarciaStichtenothTowerInput P)
    (sectionFour : SectionFourInput P tower)
    (traceInput : FiniteFieldTrace.LiteratureInput F)
    (hchoice : 4 / ((P.q : ℝ) - 2) < lambda)
    (compiler : RelationCompiler.LiteratureInput) :
    Nonempty (TwoDimensionalFamily lambda) := by
  obtain ⟨family⟩ := lemma_3_2 P tower sectionFour
  exact ⟨theoremOneOneFromDirections P family traceInput hchoice compiler⟩

end HDXLean
