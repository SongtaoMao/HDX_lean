import HDXLean.RelationTriangleCodegree
import HDXLean.RelationQuotientCoordinates
import HDXLean.EdgeCodegreeRelabel

/-!
# Exact codegree in the paper's binary coordinate space

This adapter transfers the proved actual triangle count through the already
constructed coordinate equivalence. It assumes no cited compiler output.
-/

namespace HDXLean.RelationQuotient

variable {R C : Type*} [Fintype R] [DecidableEq R]
  [Fintype C] [DecidableEq C] [Nonempty C]

theorem coordinateComplex_edgeCodegree (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho)
    (x y : Fin (RelationMatrix.nullity H) → F₂) (hne : x ≠ y)
    (hedge : (coordinateComplex H hyp).complex.IsFace {x, y}) :
    (coordinateComplex H hyp).complex.edgeCodegree x y = 2 * rho := by
  let e := (coordinates H).toEquiv
  let X := (RelationTriangleComplex.cayleyComplex H hyp).complex
  have hpre : X.IsFace {e.symm x, e.symm y} := by
    have h := (MeasuredComplex.isFace_relabel_iff X e {x, y}).mp hedge
    simpa [Equiv.finsetCongr_apply] using h
  have hnepre : e.symm x ≠ e.symm y := fun h ↦ hne (e.symm.injective h)
  change (X.relabel e).edgeCodegree x y = 2 * rho
  calc
    (X.relabel e).edgeCodegree x y = X.edgeCodegree (e.symm x) (e.symm y) := by
      simpa only [Equiv.apply_symm_apply] using
        MeasuredComplex.edgeCodegree_relabel X e (e.symm x) (e.symm y)
    _ = 2 * rho := RelationTriangleCodegree.cayleyComplex_edgeCodegree H hyp
      (e.symm x) (e.symm y) hnepre hpre

end HDXLean.RelationQuotient
