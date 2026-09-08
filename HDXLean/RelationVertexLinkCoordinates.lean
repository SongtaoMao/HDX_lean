import HDXLean.RelationVertexLink
import HDXLean.RelationQuotientCoordinates

/-!
# Origin-link certificate in binary coordinates

This uses the existing link-graph relabeling theorem. The cited propagation
from the origin to other vertex links is deliberately not reproved here.
-/

namespace HDXLean.RelationQuotient

variable {R C : Type*} [Fintype R] [DecidableEq R]
  [Fintype C] [DecidableEq C] [Nonempty C]

theorem coordinateComplex_originLink_expander (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) {lambda : ℝ}
    (hgram : WeightedGraph.IsTwoSidedSpectralExpander
      (RelationMatrix.normalizedGramGraph H rho hyp.constantColumnWeight.1) lambda) :
    ((coordinateComplex H hyp).complex.linkGraph {0}).IsTwoSidedSpectralExpander lambda := by
  let X := (RelationTriangleComplex.cayleyComplex H hyp).complex
  let e := (coordinates H).toEquiv
  have hF : e.finsetCongr ({0} : Finset (Ambient H)) = {0} := by
    simp [e, Equiv.finsetCongr_apply]
  have hnative := RelationVertexLink.originLink_expander H hyp hgram
  have hrelabeled := WeightedGraph.isTwoSidedSpectralExpander_relabel
    (X.linkGraph {0}) (X.linkVertexEquiv e {0}) hnative
  rw [← X.linkGraph_relabel e {0}] at hrelabeled
  change ((X.relabel e).linkGraph {0}).IsTwoSidedSpectralExpander lambda
  rw [hF] at hrelabeled
  exact hrelabeled

end HDXLean.RelationQuotient
