import HDXLean.Basic
import Mathlib.Data.Finset.Image

/-!
# Relabeling finite weighted objects

The paper repeatedly identifies an abstract finite binary quotient or product
with a coordinate space.  This file makes the first part of that transport
explicit: weighted graphs and all quantities entering their random-walk
spectral bound are invariant under a bijective relabeling of vertices.
-/

namespace HDXLean

open scoped BigOperators

namespace WeightedGraph

variable {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]

/-- Transport a finite weighted graph through a vertex equivalence. -/
def relabel (G : WeightedGraph V) (e : V ≃ W) : WeightedGraph W where
  weight x y := G.weight (e.symm x) (e.symm y)
  weight_symm _x _y := G.weight_symm _ _
  weight_self _x := G.weight_self _
  weight_nonneg _x _y := G.weight_nonneg _ _

/-- Two weighted graphs are equal when all their edge weights agree. -/
theorem ext_weight (G H : WeightedGraph V)
    (h : ∀ u v, G.weight u v = H.weight u v) : G = H := by
  cases G with
  | mk weightG symmetricG selfG nonnegativeG =>
      cases H with
      | mk weightH symmetricH selfH nonnegativeH =>
          have hweight : weightG = weightH := by
            funext u v
            exact h u v
          subst weightH
          rfl

@[simp]
theorem relabel_weight (G : WeightedGraph V) (e : V ≃ W) (x y : W) :
    (G.relabel e).weight x y = G.weight (e.symm x) (e.symm y) :=
  rfl

@[simp]
theorem degree_relabel (G : WeightedGraph V) (e : V ≃ W) (x : W) :
    (G.relabel e).degree x = G.degree (e.symm x) := by
  unfold degree
  exact e.symm.sum_comp (fun y ↦ G.weight (e.symm x) y)

@[simp]
theorem walk_relabel (G : WeightedGraph V) (e : V ≃ W)
    (f : W → ℝ) (x : W) :
    (G.relabel e).walk f x = G.walk (f ∘ e) (e.symm x) := by
  unfold walk
  rw [degree_relabel]
  congr 1
  simpa [relabel, Function.comp_def] using e.symm.sum_comp
    (fun y ↦ G.weight (e.symm x) y * f (e y))

@[simp]
theorem weightedMean_relabel (G : WeightedGraph V) (e : V ≃ W)
    (f : W → ℝ) :
    (G.relabel e).weightedMean f = G.weightedMean (f ∘ e) := by
  unfold weightedMean
  simp only [degree_relabel]
  simpa [Function.comp_def] using e.symm.sum_comp
    (fun x ↦ G.degree x * f (e x))

@[simp]
theorem sqNorm_relabel (G : WeightedGraph V) (e : V ≃ W)
    (f : W → ℝ) :
    (G.relabel e).sqNorm f = G.sqNorm (f ∘ e) := by
  unfold sqNorm
  simp only [degree_relabel]
  simpa [Function.comp_def] using e.symm.sum_comp
    (fun x ↦ G.degree x * (f (e x)) ^ 2)

@[simp]
theorem adj_relabel_iff (G : WeightedGraph V) (e : V ≃ W)
    (u v : V) :
    (G.relabel e).Adj (e u) (e v) ↔ G.Adj u v := by
  unfold Adj
  simp

/-- Connectedness is unchanged by a bijective relabeling. -/
theorem connected_relabel (G : WeightedGraph V) (e : V ≃ W)
    (hconnected : G.Connected) :
    (G.relabel e).Connected := by
  intro x y
  have hpath := hconnected (e.symm x) (e.symm y)
  have liftPath : ∀ {u v : V}, Relation.ReflTransGen G.Adj u v →
      Relation.ReflTransGen (G.relabel e).Adj (e u) (e v) := by
    intro u v huv
    induction huv with
    | refl => exact Relation.ReflTransGen.refl
    | tail _hpath hedge ih =>
        exact ih.tail ((adj_relabel_iff G e _ _).2 hedge)
  simpa using liftPath hpath

/-- A two-sided random-walk bound is unchanged by a bijective relabeling. -/
theorem twoSidedSpectralBound_relabel (G : WeightedGraph V) (e : V ≃ W)
    {lambda : ℝ} (hbound : G.TwoSidedSpectralBound lambda) :
    (G.relabel e).TwoSidedSpectralBound lambda := by
  refine ⟨hbound.1, ?_⟩
  intro f hmean
  have hmeanPullback : G.weightedMean (f ∘ e) = 0 := by
    simpa using hmean
  have hcontract := hbound.2 (f ∘ e) hmeanPullback
  rw [sqNorm_relabel, sqNorm_relabel]
  have hwalk : ((G.relabel e).walk f) ∘ e = G.walk (f ∘ e) := by
    funext x
    simp
  rw [hwalk]
  exact hcontract

/-- A full spectral-expander certificate transports through any equivalence. -/
theorem isTwoSidedSpectralExpander_relabel (G : WeightedGraph V) (e : V ≃ W)
    {lambda : ℝ} (h : G.IsTwoSidedSpectralExpander lambda) :
    (G.relabel e).IsTwoSidedSpectralExpander lambda :=
  ⟨connected_relabel G e h.1, twoSidedSpectralBound_relabel G e h.2⟩

end WeightedGraph

namespace MeasuredComplex

variable {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]

/-- Transport a measured pure complex through a vertex equivalence. -/
noncomputable def relabel (X : MeasuredComplex V) (e : V ≃ W) :
    MeasuredComplex W where
  dim := X.dim
  topFaces := X.topFaces.map e.finsetCongr.toEmbedding
  top_card T hT := by
    obtain ⟨S, hS, rfl⟩ := Finset.mem_map.mp hT
    change (e.finsetCongr S).card = X.dim + 1
    rw [Equiv.finsetCongr_apply, Finset.card_map]
    exact X.top_card S hS
  topWeight T := X.topWeight (e.symm.finsetCongr T)
  topWeight_pos T hT := by
    obtain ⟨S, hS, rfl⟩ := Finset.mem_map.mp hT
    change 0 < X.topWeight (e.finsetCongr.symm (e.finsetCongr S))
    rw [e.finsetCongr.symm_apply_apply]
    exact X.topWeight_pos S hS
  topWeight_zero T hT := by
    apply X.topWeight_zero
    intro hpreimage
    apply hT
    refine Finset.mem_map.mpr ⟨e.symm.finsetCongr T, hpreimage, ?_⟩
    change e.finsetCongr (e.finsetCongr.symm T) = T
    exact e.finsetCongr.apply_symm_apply T
  topWeight_sum := by
    rw [Finset.sum_map]
    convert X.topWeight_sum using 1
    apply Finset.sum_congr rfl
    intro T _hT
    change X.topWeight (e.finsetCongr.symm (e.finsetCongr T)) = _
    rw [e.finsetCongr.symm_apply_apply]

@[simp]
theorem relabel_dim (X : MeasuredComplex V) (e : V ≃ W) :
    (X.relabel e).dim = X.dim :=
  rfl

@[simp]
theorem relabel_topWeight (X : MeasuredComplex V) (e : V ≃ W)
    (T : Finset W) :
    (X.relabel e).topWeight T = X.topWeight (e.symm.finsetCongr T) :=
  rfl

@[simp]
theorem mem_relabel_topFaces_iff (X : MeasuredComplex V) (e : V ≃ W)
    (T : Finset W) :
    T ∈ (X.relabel e).topFaces ↔ e.symm.finsetCongr T ∈ X.topFaces := by
  constructor
  · intro hT
    obtain ⟨S, hS, hST⟩ := Finset.mem_map.mp hT
    rw [← hST]
    change e.finsetCongr.symm (e.finsetCongr S) ∈ X.topFaces
    rw [e.finsetCongr.symm_apply_apply]
    exact hS
  · intro hT
    refine Finset.mem_map.mpr ⟨e.symm.finsetCongr T, hT, ?_⟩
    change e.finsetCongr (e.finsetCongr.symm T) = T
    exact e.finsetCongr.apply_symm_apply T

/-- A face belongs to the relabeled complex exactly when its inverse image is
a face of the original complex. -/
theorem isFace_relabel_iff (X : MeasuredComplex V) (e : V ≃ W)
    (F : Finset W) :
    (X.relabel e).IsFace F ↔ X.IsFace (e.symm.finsetCongr F) := by
  constructor
  · rintro ⟨T, hT, hFT⟩
    obtain ⟨S, hS, rfl⟩ := Finset.mem_map.mp hT
    refine ⟨S, hS, ?_⟩
    have hmapped := (Finset.map_subset_map (f := e.symm.toEmbedding)).2 hFT
    simpa [Equiv.finsetCongr_apply, Finset.map_map] using hmapped
  · rintro ⟨S, hS, hFS⟩
    refine ⟨e.finsetCongr S, Finset.mem_map.mpr ⟨S, hS, rfl⟩, ?_⟩
    have hmapped := (Finset.map_subset_map (f := e.toEmbedding)).2 hFS
    simpa [Equiv.finsetCongr_apply, Finset.map_map] using hmapped

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
/-- Equivalent faces have the same cardinality after relabeling. -/
@[simp]
theorem card_finsetCongr (e : V ≃ W) (F : Finset V) :
    (e.finsetCongr F).card = F.card := by
  rw [Equiv.finsetCongr_apply, Finset.card_map]

omit [Fintype V] [Fintype W] in
@[simp]
theorem finsetCongr_insert (e : V ≃ W) (x : V) (F : Finset V) :
    e.finsetCongr (insert x F) = insert (e x) (e.finsetCongr F) := by
  ext y
  simp [Equiv.finsetCongr_apply]

/-- Relabeling induces the evident equivalence on every link's vertex set. -/
noncomputable def linkVertexEquiv (X : MeasuredComplex V) (e : V ≃ W)
    (F : Finset V) :
    X.LinkVertex F ≃ (X.relabel e).LinkVertex (e.finsetCongr F) where
  toFun u := by
    refine ⟨e u.1, ?_, ?_⟩
    · simpa [Equiv.finsetCongr_apply] using u.2.1
    · rw [← finsetCongr_insert, isFace_relabel_iff]
      change X.IsFace
        (e.finsetCongr.symm (e.finsetCongr (insert u.1 F)))
      rw [e.finsetCongr.symm_apply_apply]
      exact u.2.2
  invFun u := by
    refine ⟨e.symm u.1, ?_, ?_⟩
    · intro hmem
      apply u.2.1
      simpa [Equiv.finsetCongr_apply] using hmem
    · have hu := (isFace_relabel_iff X e
        (insert u.1 (e.finsetCongr F))).mp u.2.2
      change X.IsFace
        (e.finsetCongr.symm (insert u.1 (e.finsetCongr F))) at hu
      have hinverse :
          e.finsetCongr.symm (insert u.1 (e.finsetCongr F)) =
            insert (e.symm u.1) F := by
        ext x
        simp [Equiv.finsetCongr_apply]
      rw [hinverse] at hu
      exact hu
  left_inv u := by
    apply Subtype.ext
    simp
  right_inv u := by
    apply Subtype.ext
    simp

@[simp]
theorem linkVertexEquiv_apply_val (X : MeasuredComplex V) (e : V ≃ W)
    (F : Finset V) (u : X.LinkVertex F) :
    (linkVertexEquiv X e F u).1 = e u.1 :=
  rfl

/-- Relabeling preserves every conditioned link-edge weight exactly. -/
theorem linkEdgeWeight_relabel (X : MeasuredComplex V) (e : V ≃ W)
    (F : Finset V) (u v : X.LinkVertex F) :
    (X.relabel e).linkEdgeWeight (e.finsetCongr F)
        (linkVertexEquiv X e F u) (linkVertexEquiv X e F v) =
      X.linkEdgeWeight F u v := by
  classical
  by_cases huv : u = v
  · subst v
    simp [linkEdgeWeight]
  · have hmapped : linkVertexEquiv X e F u ≠ linkVertexEquiv X e F v :=
      (linkVertexEquiv X e F).injective.ne huv
    rw [linkEdgeWeight, linkEdgeWeight, if_neg hmapped, if_neg huv]
    have hcondition (S : Finset V) :
        insert (linkVertexEquiv X e F v).1
            (insert (linkVertexEquiv X e F u).1 (e.finsetCongr F)) ⊆
              e.finsetCongr S ↔
          insert v.1 (insert u.1 F) ⊆ S := by
      change insert (e v.1) (insert (e u.1) (e.finsetCongr F)) ⊆
          e.finsetCongr S ↔ _
      rw [← finsetCongr_insert e u.1 F,
        ← finsetCongr_insert e v.1 (insert u.1 F)]
      exact Finset.map_subset_map
    change
      (∑ T ∈
          (X.topFaces.map e.finsetCongr.toEmbedding).filter
            (fun T ↦ insert (linkVertexEquiv X e F v).1
              (insert (linkVertexEquiv X e F u).1 (e.finsetCongr F)) ⊆ T),
        X.topWeight (e.finsetCongr.symm T)) =
      ∑ T ∈ X.topFaces.filter
          (fun T ↦ insert v.1 (insert u.1 F) ⊆ T), X.topWeight T
    rw [Finset.filter_map]
    have hfilter :
        X.topFaces.filter
            ((fun T ↦ insert (linkVertexEquiv X e F v).1
              (insert (linkVertexEquiv X e F u).1 (e.finsetCongr F)) ⊆ T) ∘
                e.finsetCongr.toEmbedding) =
          X.topFaces.filter
            (fun T ↦ insert v.1 (insert u.1 F) ⊆ T) := by
      ext S
      simp only [Finset.mem_filter, Function.comp_apply]
      change (S ∈ X.topFaces ∧
          insert (linkVertexEquiv X e F v).1
              (insert (linkVertexEquiv X e F u).1 (e.finsetCongr F)) ⊆
            e.finsetCongr S) ↔
        (S ∈ X.topFaces ∧ insert v.1 (insert u.1 F) ⊆ S)
      rw [hcondition]
    rw [hfilter, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro T _hT
    change X.topWeight (e.finsetCongr.symm (e.finsetCongr T)) = _
    rw [e.finsetCongr.symm_apply_apply]

/-- A relabeled link graph is exactly the corresponding relabeling of the
original link graph. -/
theorem linkGraph_relabel (X : MeasuredComplex V) (e : V ≃ W)
    (F : Finset V) :
    (X.relabel e).linkGraph (e.finsetCongr F) =
      (X.linkGraph F).relabel (linkVertexEquiv X e F) := by
  apply WeightedGraph.ext_weight
  intro x y
  obtain ⟨u, rfl⟩ := (linkVertexEquiv X e F).surjective x
  obtain ⟨v, rfl⟩ := (linkVertexEquiv X e F).surjective y
  dsimp only [MeasuredComplex.linkGraph, WeightedGraph.relabel]
  rw [(linkVertexEquiv X e F).symm_apply_apply,
    (linkVertexEquiv X e F).symm_apply_apply]
  exact linkEdgeWeight_relabel X e F u v

/-- Connectivity of every required positive-dimensional link transports
through a vertex relabeling. -/
theorem positiveLinksConnected_relabel (X : MeasuredComplex V) (e : V ≃ W)
    (h : X.PositiveLinksConnected) :
    (X.relabel e).PositiveLinksConnected := by
  intro F hF hcard
  let F₀ := e.finsetCongr.symm F
  have hFimage : e.finsetCongr F₀ = F :=
    e.finsetCongr.apply_symm_apply F
  rw [← hFimage] at hF hcard ⊢
  have hF₀ : X.IsFace F₀ := by
    have hpreimage :=
      (isFace_relabel_iff X e (e.finsetCongr F₀)).mp hF
    change X.IsFace (e.finsetCongr.symm (e.finsetCongr F₀)) at hpreimage
    rw [e.finsetCongr.symm_apply_apply] at hpreimage
    exact hpreimage
  have hcard₀ : F₀.card + 1 ≤ X.dim := by
    simpa using hcard
  rw [linkGraph_relabel]
  exact WeightedGraph.connected_relabel (X.linkGraph F₀)
    (linkVertexEquiv X e F₀) (h F₀ hF₀ hcard₀)

/-- Every codimension-two two-sided bound transports through a vertex
relabeling. -/
theorem codimensionTwoBound_relabel (X : MeasuredComplex V) (e : V ≃ W)
    {lambda : ℝ} (h : X.CodimensionTwoBound lambda) :
    (X.relabel e).CodimensionTwoBound lambda := by
  intro F hF hcard
  let F₀ := e.finsetCongr.symm F
  have hFimage : e.finsetCongr F₀ = F :=
    e.finsetCongr.apply_symm_apply F
  rw [← hFimage] at hF hcard ⊢
  have hF₀ : X.IsFace F₀ := by
    have hpreimage :=
      (isFace_relabel_iff X e (e.finsetCongr F₀)).mp hF
    change X.IsFace (e.finsetCongr.symm (e.finsetCongr F₀)) at hpreimage
    rw [e.finsetCongr.symm_apply_apply] at hpreimage
    exact hpreimage
  have hcard₀ : F₀.card + 1 = X.dim := by
    simpa using hcard
  rw [linkGraph_relabel]
  exact WeightedGraph.twoSidedSpectralBound_relabel (X.linkGraph F₀)
    (linkVertexEquiv X e F₀) (h F₀ hF₀ hcard₀)

/-- Local spectral expansion is invariant under a vertex equivalence. -/
theorem localSpectralExpander_relabel (X : MeasuredComplex V) (e : V ≃ W)
    {lambda : ℝ} (h : X.IsTwoSidedLocalSpectralExpander lambda) :
    (X.relabel e).IsTwoSidedLocalSpectralExpander lambda :=
  ⟨positiveLinksConnected_relabel X e h.1,
    codimensionTwoBound_relabel X e h.2⟩

end MeasuredComplex

section CayleyRelabel

variable {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W] [AddCommGroup V] [AddCommGroup W]

omit [Fintype V] [Fintype W] in
/-- An additive equivalence commutes with translating a finite face. -/
theorem finsetCongr_translate (e : V ≃+ W) (g : V) (F : Finset V) :
    e.toEquiv.finsetCongr (translateFace g F) =
      translateFace (e g) (e.toEquiv.finsetCongr F) := by
  classical
  ext y
  simp only [Equiv.finsetCongr_apply, Finset.mem_map_equiv,
    mem_translateFace_iff]
  simp

namespace CayleyPresentation

/-- Transport a Cayley presentation through an additive equivalence. -/
noncomputable def relabel {X : MeasuredComplex V}
    (C : CayleyPresentation X) (e : V ≃+ W) :
    CayleyPresentation (X.relabel e.toEquiv) where
  generators := C.generators.map e.toEquiv.toEmbedding
  zero_not_mem := by
    simpa using C.zero_not_mem
  neg_mem_iff s := by
    simpa using C.neg_mem_iff (e.symm s)
  edge_iff x y := by
    rw [MeasuredComplex.isFace_relabel_iff]
    simpa [Equiv.finsetCongr_apply] using C.edge_iff (e.symm x) (e.symm y)

@[simp]
theorem degree_relabel {X : MeasuredComplex V} (C : CayleyPresentation X)
    (e : V ≃+ W) :
    (C.relabel e).degree = C.degree := by
  unfold degree relabel
  rw [Finset.card_map]

end CayleyPresentation

namespace MeasuredComplex

/-- Translation invariance transports through an additive equivalence. -/
theorem translationInvariant_relabel (X : MeasuredComplex V) (e : V ≃+ W)
    (h : TranslationInvariant X) :
    TranslationInvariant (X.relabel e.toEquiv) := by
  intro w T
  have hinverseTranslate :
      e.toEquiv.symm.finsetCongr (translateFace w T) =
        translateFace (e.symm w) (e.toEquiv.symm.finsetCongr T) := by
    simpa using finsetCongr_translate e.symm w T
  constructor
  · rw [mem_relabel_topFaces_iff, mem_relabel_topFaces_iff,
      hinverseTranslate]
    exact (h (e.symm w) (e.toEquiv.symm.finsetCongr T)).1
  · rw [relabel_topWeight, relabel_topWeight, hinverseTranslate]
    exact (h (e.symm w) (e.toEquiv.symm.finsetCongr T)).2

end MeasuredComplex

namespace CayleyComplex

/-- Transport a measured Cayley complex through an additive equivalence. -/
noncomputable def relabel (C : CayleyComplex (V := V)) (e : V ≃+ W) :
    CayleyComplex (V := W) where
  complex := C.complex.relabel e.toEquiv
  cayley := C.cayley.relabel e
  translationInvariant :=
    C.complex.translationInvariant_relabel e C.translationInvariant

@[simp]
theorem relabel_dimension (C : CayleyComplex (V := V)) (e : V ≃+ W) :
    (C.relabel e).complex.dim = C.complex.dim :=
  rfl

@[simp]
theorem relabel_degree (C : CayleyComplex (V := V)) (e : V ≃+ W) :
    (C.relabel e).cayley.degree = C.cayley.degree :=
  C.cayley.degree_relabel e

end CayleyComplex

end CayleyRelabel

end HDXLean
