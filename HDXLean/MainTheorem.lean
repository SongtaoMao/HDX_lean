import HDXLean.TheoremOneOneOuter
import HDXLean.TheoremOneTwo

/-!
# Paper-wide public entry point

Current PDF numbering (2026-09-08): Question 1.1, Theorem 1.2 (unweighted
two-dimensional), and Theorem 1.3 (weighted higher-dimensional). Historical
module/declaration names are retained for compatibility. Use `theorem_1_2`
and `theorem_1_3` below for the current manuscript numbering.

This module retains the earlier assumption interfaces. The newer
`MainTheoremCited` module constructs the quotient-to-compiler and Section 4
adapters from explicit cited data and calls these proofs unchanged. The
compiler requires nonempty columns, derived at every call site. Exact
Section 5 spectrum theorems are in `ProductExactSpectrum` under their separate
literature inputs.

This module exposes both main mathematical family conclusions of `main.pdf`.
It assembles existing proofs; it does not add a new literature assumption or
assert that every lemma, example, or discussion claim has been formalized.

The two-dimensional path takes the existing tower, Section 4, trace, and
relation-compiler interfaces. In particular, `ConcreteSectionFourInput`
supplies geometric level and matrix/minor data; `MainTheoremCited` assembles
that interface through the common cited curve/Riemann–Roch model. The
higher-dimensional path takes the two stated Golowich product inputs.
Neither path formalizes algorithmic explicitness or complexity.

The actual global-gap identification and the separately cited optimal-degree
comparison are not assertions of `MainConclusions`. See `README.md` for the
formalization scope and premise inventory.
-/

namespace HDXLean.Paper

/-- Current Lemma 4.5: rank-one update, with the historical signature. -/
alias lemma_4_5_rank_one_update :=
  HDXLean.MultiplicationMatrixData.lemma_4_6_rank_one_update

/-- Current Lemma 4.5: affine restriction of the certified minors. -/
alias lemma_4_5 := HDXLean.lemma_4_6

/-- Current Proposition 4.6, conditional on the existing concrete level data.
Coefficient independence is still supplied, not derived from 1-genericity. -/
alias proposition_4_6 :=
  HDXLean.ConcreteMaximalMinorLevelData.selectedMaximalMinor_linearIndependent

/-- Existing assumption packages for the two independent main theorem paths.
This record does not supply proof terms for either input package. -/
structure Inputs : Type 1 where
  twoDimensional : TheoremOneOneLiterature
  higherDimensional : GolowichProduct.LiteratureInput

/-- Mathematical family conclusion of current Theorem 1.2; no algorithmic claim. -/
def TwoDimensionalConclusion : Prop :=
  ∀ lambda : ℝ, 0 < lambda → Nonempty (TwoDimensionalFamily lambda)

/-- Mathematical family conclusion of current Theorem 1.3; no global-gap formula. -/
def HigherDimensionalConclusion : Prop :=
  ∀ d : ℕ, 2 ≤ d → Nonempty (LinearDegreeHigherDimensionalFamily d)

/-- The conjunction of the two main family conclusions, not all paper claims. -/
def MainConclusions : Prop :=
  TwoDimensionalConclusion ∧ HigherDimensionalConclusion

/-- Historical name: current Theorem 1.2. See the remaining input boundaries above. -/
theorem conditionalTheoremOneOne (input : TheoremOneOneLiterature) :
    TwoDimensionalConclusion := by
  intro lambda hlambda
  exact HDXLean.theoremOneOne hlambda input

/-- Historical name: current Theorem 1.3, independent of Section 4 premises. -/
theorem conditionalTheoremOneTwo (input : GolowichProduct.LiteratureInput) :
    HigherDimensionalConclusion := by
  intro d hd
  exact HDXLean.TheoremOneTwo.theoremOneTwo d hd input

/-- Current Theorem 1.2, under the existing two-dimensional input.
The empty-domain repair does not complete the remaining geometric adapters. -/
theorem theorem_1_2 {lambda : ℝ} (hlambda : 0 < lambda)
    (input : TheoremOneOneLiterature) : Nonempty (TwoDimensionalFamily lambda) :=
  HDXLean.theoremOneOne hlambda input

/-- Current Theorem 1.3, under the independent Golowich product input. -/
theorem theorem_1_3 (d : ℕ) (hd : 2 ≤ d)
    (input : GolowichProduct.LiteratureInput) :
    Nonempty (LinearDegreeHigherDimensionalFamily d) :=
  HDXLean.TheoremOneTwo.theoremOneTwo d hd input

/-- Both main family conclusions from their explicitly displayed inputs. -/
theorem conditionalMainTheorems (inputs : Inputs) : MainConclusions :=
  ⟨conditionalTheoremOneOne inputs.twoDimensional,
    conditionalTheoremOneTwo inputs.higherDimensional⟩

end HDXLean.Paper
