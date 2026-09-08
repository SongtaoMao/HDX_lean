import HDXLean.RelationQuotientConnected
import HDXLean.RelationCodegreeCoordinates
import HDXLean.RelationVertexLink

/-!
# Actual relation compiler from a narrowly stated cited propagation lemma

The manuscript's Lemma 2.2 cites Golowich, Lemma 45, for propagation of the
origin-link expansion statement to every vertex link of the relation
complex. That external statement is retained as an explicit input and is
not reproved here. Source: https://arxiv.org/pdf/2305.02512.

Everything else in the compiler output is assembled from the existing
internal construction: quotient dimension, Cayley generators, uniform
triangle measure, degree, codegree, global connectivity, and the native
origin-link/counting-Gram identification. The historical compiler interface
is preserved and is now produced as a derived adapter.
-/
namespace HDXLean.RelationCompiler

/-- The cited manuscript Lemma 2.2, restricted to its actual content:
origin-link expansion implies expansion of all singleton links of the
literal quotient triangle complex. No output, coordinate, dimension,
counting, or global-connectivity conclusion is included in this input. -/
structure OriginLinkPropagationInput : Prop where
  lemma_2_2 : ∀ (R C : Type) [Fintype R] [DecidableEq R]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (H : BinaryMatrix R C) (rho : ℕ)
    (hyp : RelationMatrix.CompilerHypotheses H rho) (lambda : ℝ),
    ((RelationTriangleComplex.cayleyComplex H hyp).complex.linkGraph {0}).IsTwoSidedSpectralExpander
      lambda →
    ∀ v : RelationQuotient.Ambient H,
      ((RelationTriangleComplex.cayleyComplex H hyp).complex.linkGraph {v}).IsTwoSidedSpectralExpander
        lambda

variable {R C : Type} [Fintype R] [DecidableEq R]
  [Fintype C] [DecidableEq C] [Nonempty C]

/-- Named application of the cited propagation lemma. It is deliberately
only a wrapper around the user-authorized external input. -/
theorem lemma_2_2 (input : OriginLinkPropagationInput)
    (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) {lambda : ℝ}
    (horigin : ((RelationTriangleComplex.cayleyComplex H hyp).complex.linkGraph {0}).IsTwoSidedSpectralExpander
      lambda) (v : RelationQuotient.Ambient H) :
    ((RelationTriangleComplex.cayleyComplex H hyp).complex.linkGraph {v}).IsTwoSidedSpectralExpander
      lambda :=
  input.lemma_2_2 R C H rho hyp lambda horigin v

end HDXLean.RelationCompiler

namespace HDXLean.MeasuredComplex
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In dimension two, all positive-dimensional links are the empty-face
link or singleton links. This finite face classification is internal. -/
theorem localExpansion_two_of_vertexLinks (X : MeasuredComplex V)
    (hdim : X.dim = 2) {lambda : ℝ}
    (hglobal : (X.linkGraph ∅).Connected)
    (hvertex : ∀ v : V, (X.linkGraph {v}).IsTwoSidedSpectralExpander lambda) :
    X.IsTwoSidedLocalSpectralExpander lambda := by
  constructor
  · intro F _hF hcard
    rw [hdim] at hcard
    by_cases he : F = ∅
    · subst F
      exact hglobal
    · have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (by omega : F.card = 1)
      exact (hvertex v).1
  · intro F _hF hcard
    rw [hdim] at hcard
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (by omega : F.card = 1)
    exact (hvertex v).2

end HDXLean.MeasuredComplex

namespace HDXLean.RelationCompiler
variable {R C : Type} [Fintype R] [DecidableEq R]
  [Fintype C] [DecidableEq C] [Nonempty C]

/-- Local expansion of the actual quotient complex. Only propagation
between vertex links is external; the origin-link identification and global
connectivity are already proved internally. -/
theorem quotient_localExpansion (input : OriginLinkPropagationInput)
    (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) {lambda : ℝ}
    (hgram : WeightedGraph.IsTwoSidedSpectralExpander
      (RelationMatrix.normalizedGramGraph H rho hyp.constantColumnWeight.1) lambda) :
    (RelationTriangleComplex.cayleyComplex H hyp).complex.IsTwoSidedLocalSpectralExpander
      lambda := by
  apply MeasuredComplex.localExpansion_two_of_vertexLinks _
    (RelationTriangleComplex.cayleyComplex_dimension H hyp)
    (RelationQuotient.cayleyComplex_empty_link_connected H hyp)
  exact lemma_2_2 input H hyp (RelationVertexLink.originLink_expander H hyp hgram)

/-- The same local expansion on the paper's literal binary coordinate
space, using the previously proved whole-complex relabeling theorem. -/
theorem coordinate_localExpansion (input : OriginLinkPropagationInput)
    (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) {lambda : ℝ}
    (hgram : WeightedGraph.IsTwoSidedSpectralExpander
      (RelationMatrix.normalizedGramGraph H rho hyp.constantColumnWeight.1) lambda) :
    (RelationQuotient.coordinateComplex H hyp).complex.IsTwoSidedLocalSpectralExpander
      lambda :=
  MeasuredComplex.localSpectralExpander_relabel _ _
    (quotient_localExpansion input H hyp hgram)

/-- Every historical compiler-output field is supplied by the actual
construction. The only external assumption is the narrow cited propagation
statement above, not the desired output itself. -/
noncomputable def output (input : OriginLinkPropagationInput)
    (H : BinaryMatrix R C) (rho : ℕ) (lambda : ℝ)
    (hyp : RelationMatrix.CompilerHypotheses H rho)
    (hgram : WeightedGraph.IsTwoSidedSpectralExpander
      (RelationMatrix.normalizedGramGraph H rho hyp.constantColumnWeight.1) lambda) :
    Output H rho lambda where
  ambientDimension := RelationMatrix.nullity H
  complex := RelationQuotient.coordinateComplex H hyp
  dimension_eq := RelationQuotient.coordinateComplex_dimension H hyp
  unweighted := RelationQuotient.coordinateComplex_unweighted H hyp
  degree_eq := RelationQuotient.coordinateComplex_degree H hyp
  ambientDimension_eq := rfl
  edgeCodegree_eq := RelationQuotient.coordinateComplex_edgeCodegree H hyp
  localExpansion := coordinate_localExpansion input H hyp hgram

/-- Backward-compatible adapter to the old compiler interface. Existing
matching proofs remain unchanged; callers can now construct that interface
from the precise cited input and internally proved fields. -/
noncomputable def literatureInput_of_originPropagation
    (input : OriginLinkPropagationInput) : LiteratureInput := by
  refine ⟨?_⟩
  intro R C _ _ _ _ _ H rho lambda hyp hgram
  exact output input H rho lambda hyp hgram

end HDXLean.RelationCompiler
