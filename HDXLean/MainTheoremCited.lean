import HDXLean.MainTheorem
import HDXLean.CurveTowerAssembly
import HDXLean.RelationCompilerAssembly

/-!
# Main-theorem entry point using the constructed adapters

The previously checked main proofs are reused unchanged. The old supplied
Section 4 and whole-compiler records are now outputs of internal adapters.
The remaining two-dimensional inputs are the common cited curve/RR model,
the cited determinantal and trace facts, and Golowich's origin-link
propagation statement. The geometry is represented by the precise axiomatic
function-space model, not by a separate scheme-level development.

This module does not assert coverage of every example or discussion claim,
nor algorithmic explicitness, complexity, or a fresh full-library check.
-/

namespace HDXLean.Paper

/-- Cited mathematical data for the two-dimensional route. No direction
set, independent-minor family, or full relation-compiler output is assumed. -/
structure TwoDimensionalCitedInput : Type 1 where
  geometry : ∀ (h : ℕ) (hh : 3 ≤ h),
    CurveTowerAssembly.CitedInput (ConcreteSquareField.parameters h hh)
  trace : ∀ (h : ℕ) (_hh : 3 ≤ h),
    FiniteFieldTrace.LiteratureInput (ConcreteSquareField.Extension h)
  originPropagation : RelationCompiler.OriginLinkPropagationInput

/-- Construct the old main-proof interface; its proofs and signatures are
preserved for compatibility, not copied or replaced by equivalent proofs. -/
noncomputable def TwoDimensionalCitedInput.toLegacy
    (input : TwoDimensionalCitedInput) : TheoremOneOneLiterature where
  tower h hh := (input.geometry h hh).tower
  sectionFour h hh := (input.geometry h hh).sectionFour
  trace := input.trace
  compiler := RelationCompiler.literatureInput_of_originPropagation input.originPropagation

/-- Current Theorem 1.2, with the common geometric construction and actual
compiler assembled before invoking the existing outer theorem. -/
theorem theorem_1_2_from_cited_data {lambda : ℝ} (hlambda : 0 < lambda)
    (input : TwoDimensionalCitedInput) : Nonempty (TwoDimensionalFamily lambda) :=
  theorem_1_2 hlambda input.toLegacy

/-- Inputs for both main family conclusions; the Section 5 input and proof
are exactly the previously checked ones. -/
structure CitedInputs : Type 1 where
  twoDimensional : TwoDimensionalCitedInput
  higherDimensional : GolowichProduct.LiteratureInput

/-- Both main family conclusions, reusing the original main proofs. -/
theorem mainTheorems_from_cited_data (input : CitedInputs) : MainConclusions :=
  ⟨fun _ hlambda ↦ theorem_1_2_from_cited_data hlambda input.twoDimensional,
    conditionalTheoremOneTwo input.higherDimensional⟩

end HDXLean.Paper
