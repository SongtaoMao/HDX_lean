import HDXLean.RelationQuotientCoordinates
import HDXLean.WeightedLiftLinks

/-!
# Connectivity of the actual quotient one-skeleton

The coordinate images span the row-code quotient. Over the binary field,
linear combinations of Cayley generators give actual paths. The resulting
connectedness statement concerns the native empty-face link graph of the
constructed triangle complex and its coordinate relabeling. No literature
statement or relation-compiler output is assumed.
-/
namespace HDXLean.RelationQuotient
open scoped BigOperators
variable {R C : Type*} [Fintype C] [DecidableEq C]

/-- Ordinary coordinate decomposition before passing to the quotient. -/
theorem sum_smul_coordinateVector (x : C → F₂) :
    (∑ c, x c • coordinateVector c) = x := by
  ext j
  simp [coordinateVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Every quotient vector is a linear combination of the actual coordinate
images. This fact does not need row-distance or nonempty-column hypotheses. -/
theorem span_range_generator (H : BinaryMatrix R C) :
    Submodule.span F₂ (Set.range (generator H)) = ⊤ := by
  apply top_unique
  intro q _
  obtain ⟨x, rfl⟩ := (rowCode H).mkQ_surjective q
  rw [← sum_smul_coordinateVector x, map_sum]
  apply Submodule.sum_mem
  intro c _
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

/-- Finite-generator-set version used by the actual Cayley presentation. -/
theorem span_generators (H : BinaryMatrix R C) :
    Submodule.span F₂ (generators H : Set (Ambient H)) = ⊤ := by
  classical
  have hset : (generators H : Set (Ambient H)) = Set.range (generator H) := by
    ext x
    simp [generators]
  rw [hset]
  exact span_range_generator H

end HDXLean.RelationQuotient

namespace HDXLean.CayleyPresentation
variable {V : Type*} [Fintype V] [DecidableEq V]
  [AddCommGroup V] [Module F₂ V]

/-- Binary linear spanning of Cayley generators implies connectivity of the
actual weighted one-skeleton. The proof uses finite paths, not a spectral
certificate or a new assumption about connectedness. -/
theorem empty_link_connected_of_span {X : MeasuredComplex V}
    (C : CayleyPresentation X)
    (hspan : Submodule.span F₂ (C.generators : Set V) = ⊤) :
    (X.linkGraph ∅).Connected := by
  classical
  let step : V → V → Prop := fun x y ↦ y - x ∈ C.generators
  have shift (v : V) {a b : V} (h : Relation.ReflTransGen step a b) :
      Relation.ReflTransGen step (v + a) (v + b) := by
    apply Relation.ReflTransGen.lift (v + ·) ?_ a b h
    intro x y hxy
    change (v + y) - (v + x) ∈ C.generators
    simpa only [step, add_sub_add_left_eq_sub] using hxy
  have from_zero (z : V) : Relation.ReflTransGen step 0 z := by
    have hz : z ∈ Submodule.span F₂ (C.generators : Set V) := by
      rw [hspan]
      exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => exact Relation.ReflTransGen.single (by simpa [step] using hz)
    | zero => exact Relation.ReflTransGen.refl
    | add x y _ _ hx hy =>
      exact hx.trans (by simpa only [add_zero] using shift x hy)
    | smul a x _ hx =>
      by_cases ha : a = 0
      · simpa only [ha, zero_smul] using
          (Relation.ReflTransGen.refl (r := step) (a := (0 : V)))
      · have ha1 : a = 1 := Fin.eq_one_of_ne_zero _ ha
        simpa only [ha1, one_smul] using hx
  let vertex (x : V) : X.LinkVertex ∅ :=
    ⟨x, by simp, by simpa using (C.edge_iff x x).mpr (Or.inl rfl)⟩
  have hedge (x y : V) (h : step x y) :
      (X.linkGraph ∅).Adj (vertex x) (vertex y) := by
    apply (X.linkGraph_adj_iff ∅ _ _).mpr
    refine ⟨?_, ?_⟩
    · intro he
      have hxy : x = y := congrArg Subtype.val he
      apply C.zero_not_mem
      simpa only [step, hxy, sub_self] using h
    · simpa [vertex, Finset.pair_comm] using (C.edge_iff x y).mpr (Or.inr h)
  intro x y
  have hp : Relation.ReflTransGen step x.1 y.1 := by
    simpa only [add_zero, add_sub_cancel] using shift x.1 (from_zero (y.1 - x.1))
  have hgraph := Relation.ReflTransGen.lift vertex hedge x.1 y.1 hp
  change Relation.ReflTransGen (X.linkGraph ∅).Adj (vertex x.1) (vertex y.1) at hgraph
  have hx : vertex x.1 = x := Subtype.ext rfl
  have hy : vertex y.1 = y := Subtype.ext rfl
  simpa only [hx, hy] using hgraph

end HDXLean.CayleyPresentation

namespace HDXLean.RelationQuotient
variable {R C : Type*} [Fintype R] [DecidableEq R]
  [Fintype C] [DecidableEq C] [Nonempty C]

omit [DecidableEq R] in
/-- The actual quotient triangle complex has connected global graph. -/
theorem cayleyComplex_empty_link_connected (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) :
    ((RelationTriangleComplex.cayleyComplex H hyp).complex.linkGraph ∅).Connected := by
  apply (RelationTriangleComplex.cayleyComplex H hyp).cayley.empty_link_connected_of_span
  exact span_generators H

/-- Global connectedness survives the internally constructed identification
of the quotient with the literal binary coordinate space. -/
theorem coordinateComplex_empty_link_connected (H : BinaryMatrix R C) {rho : ℕ}
    (hyp : RelationMatrix.CompilerHypotheses H rho) :
    ((coordinateComplex H hyp).complex.linkGraph ∅).Connected := by
  let X := (RelationTriangleComplex.cayleyComplex H hyp).complex
  let e := (coordinates H).toEquiv
  have h := WeightedGraph.connected_relabel (X.linkGraph ∅)
    (X.linkVertexEquiv e ∅) (cayleyComplex_empty_link_connected H hyp)
  rw [← X.linkGraph_relabel e ∅] at h
  have he : e.finsetCongr ∅ = ∅ := by simp
  rw [he] at h
  exact h

end HDXLean.RelationQuotient
