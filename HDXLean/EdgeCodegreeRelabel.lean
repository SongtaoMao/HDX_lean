import HDXLean.Relabeling

/-!
# Edge codegree is invariant under relabeling

The proof counts actual top-face sets through their existing bijection.
-/

namespace HDXLean.MeasuredComplex

variable {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]

theorem edgeCodegree_relabel (X : MeasuredComplex V) (e : V ≃ W) (x y : V) :
    (X.relabel e).edgeCodegree (e x) (e y) = X.edgeCodegree x y := by
  classical
  change ((X.topFaces.map e.finsetCongr.toEmbedding).filter
    (fun T ↦ e x ∈ T ∧ e y ∈ T)).card = _
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  ext T
  simp [Equiv.finsetCongr_apply]

end HDXLean.MeasuredComplex
