import HDXLean.ConditionedLinkWeights
import HDXLean.WeightedLiftOneFiberSpectrum

/-!
# Mass formulas for vertex links of a measured two-complex

For a two-dimensional measured complex, an edge of the link at a vertex is
the unique top triangle containing its two link endpoints.  Consequently the
degree of a link vertex is the total weight of the triangles through the
corresponding base edge, and the total link volume is twice the total weight
of the triangles through the conditioned vertex.
-/

namespace HDXLean

open scoped BigOperators

namespace MeasuredComplex

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem pair_card_of_linkVertex (X : MeasuredComplex V) (x : V)
    (b : X.LinkVertex ({x} : Finset V)) :
    (insert b.1 ({x} : Finset V)).card = 2 := by
  have hbx : b.1 ≠ x := by simpa using b.2.1
  simp [hbx]

/-- In a two-complex, the degree of a vertex in the link at `x` is the total
top-face weight of the triangles containing the edge `{x, b}`. -/
theorem vertexLink_degree_eq_topWeight_sum
    (X : MeasuredComplex V) (hdim : X.dim = 2) (x : V)
    (b : X.LinkVertex ({x} : Finset V)) :
    (X.linkGraph ({x} : Finset V)).degree b =
      ∑ T ∈ X.topFaces with insert b.1 ({x} : Finset V) ⊆ T,
        X.topWeight T := by
  classical
  let P : Finset V := insert b.1 ({x} : Finset V)
  let faceOf : X.LinkVertex ({x} : Finset V) → Finset V :=
    fun c ↦ insert c.1 P
  have hPcard : P.card = 2 := by
    exact pair_card_of_linkVertex X x b
  have hcodim : ({x} : Finset V).card + 1 = X.dim := by
    simp [hdim]
  have hedge (c : X.LinkVertex ({x} : Finset V)) :
      (X.linkGraph ({x} : Finset V)).weight b c =
        if faceOf c ∈ X.topFaces then X.topWeight (faceOf c) else 0 := by
    by_cases hcb : c = b
    · subst c
      have hnotTop : faceOf b ∉ X.topFaces := by
        intro htop
        have hcard := X.top_card (faceOf b) htop
        have hface : faceOf b = P := by
          apply Finset.insert_eq_self.mpr
          simp [P]
        rw [hface, hPcard, hdim] at hcard
        omega
      rw [if_neg hnotTop]
      exact (X.linkGraph ({x} : Finset V)).weight_self b
    · have hweight :=
        X.codimensionTwo_linkEdgeWeight_eq_topWeight
          ({x} : Finset V) hcodim b c (Ne.symm hcb)
      by_cases htop : faceOf c ∈ X.topFaces
      · simpa [linkGraph, faceOf, P, htop] using hweight
      · rw [show (X.linkGraph ({x} : Finset V)).weight b c =
          X.topWeight (faceOf c) by
          simpa [linkGraph, faceOf, P] using hweight]
        simp [htop, X.topWeight_zero (faceOf c) htop]
  unfold WeightedGraph.degree
  simp_rw [hedge]
  rw [← Finset.sum_filter]
  let source : Finset (X.LinkVertex ({x} : Finset V)) :=
    Finset.univ.filter fun c ↦ faceOf c ∈ X.topFaces
  let target : Finset (Finset V) :=
    X.topFaces.filter fun T ↦ P ⊆ T
  change (∑ c ∈ source, X.topWeight (faceOf c)) =
    ∑ T ∈ target, X.topWeight T
  apply Finset.sum_bij (fun c _hc ↦ faceOf c)
  · intro c hc
    have hcTop : faceOf c ∈ X.topFaces := (Finset.mem_filter.mp hc).2
    apply Finset.mem_filter.mpr
    exact ⟨hcTop, Finset.subset_insert _ _⟩
  · intro c₁ hc₁ c₂ hc₂ heq
    have hc₁Top : faceOf c₁ ∈ X.topFaces := (Finset.mem_filter.mp hc₁).2
    have hc₂Top : faceOf c₂ ∈ X.topFaces := (Finset.mem_filter.mp hc₂).2
    have hc₁notP : c₁.1 ∉ P := by
      intro hcP
      have hface : faceOf c₁ = P := Finset.insert_eq_self.mpr hcP
      have hcard := X.top_card (faceOf c₁) hc₁Top
      rw [hface, hPcard, hdim] at hcard
      omega
    have hc₂notP : c₂.1 ∉ P := by
      intro hcP
      have hface : faceOf c₂ = P := Finset.insert_eq_self.mpr hcP
      have hcard := X.top_card (faceOf c₂) hc₂Top
      rw [hface, hPcard, hdim] at hcard
      omega
    have hc₁mem : c₁.1 ∈ faceOf c₂ := by
      rw [← heq]
      exact Finset.mem_insert_self _ _
    have hval : c₁.1 = c₂.1 := by
      rcases Finset.mem_insert.mp hc₁mem with h | h
      · exact h
      · exact False.elim (hc₁notP h)
    exact Subtype.ext hval
  · intro T hT
    have hTtop : T ∈ X.topFaces := (Finset.mem_filter.mp hT).1
    have hPT : P ⊆ T := (Finset.mem_filter.mp hT).2
    have hPproper : P ⊂ T := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hPT, ?_⟩
      intro hEq
      have hcard := X.top_card T hTtop
      rw [← hEq, hPcard, hdim] at hcard
      omega
    obtain ⟨c, hcP, hcInsert⟩ :=
      Finset.ssubset_iff_exists_cons_subset.mp hPproper
    rw [Finset.cons_eq_insert] at hcInsert
    have hcT : c ∈ T := hcInsert (Finset.mem_insert_self _ _)
    have hcx : c ≠ x := by
      intro hcx
      apply hcP
      subst c
      simp [P]
    have hcFace : X.IsFace (insert c {x}) := by
      exact ⟨T, hTtop, fun y hy ↦ by
        apply hcInsert
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Finset.mem_insert_self _ _
        · simp [P, hy]⟩
    let cLink : X.LinkVertex {x} := ⟨c, by simpa using hcx, hcFace⟩
    have hfaceEq : faceOf cLink = T := by
      change insert c P = T
      apply Finset.eq_of_subset_of_card_le hcInsert
      rw [X.top_card T hTtop, hdim]
      change 3 ≤ (insert c P).card
      rw [Finset.card_insert_of_notMem hcP, hPcard]
    refine ⟨cLink, ?_, hfaceEq⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hfaceEq ▸ hTtop⟩
  · intro c hc
    rfl

/-- Every vertex in a vertex link of a measured two-complex has strictly
positive weighted degree. -/
theorem vertexLink_degree_pos
    (X : MeasuredComplex V) (hdim : X.dim = 2) (x : V)
    (b : X.LinkVertex ({x} : Finset V)) :
    0 < (X.linkGraph ({x} : Finset V)).degree b := by
  rw [vertexLink_degree_eq_topWeight_sum X hdim x b]
  obtain ⟨T, hT, hsub⟩ := b.2.2
  apply Finset.sum_pos'
  · intro S hS
    exact le_of_lt (X.topWeight_pos S (Finset.mem_filter.mp hS).1)
  · refine ⟨T, Finset.mem_filter.mpr ⟨hT, hsub⟩, ?_⟩
    exact X.topWeight_pos T hT

/-- A top triangle through `x` contains exactly two vertices of the link at
`x`.  This is the incidence count behind the link-volume formula. -/
theorem vertexLink_incidence_card
    (X : MeasuredComplex V) (hdim : X.dim = 2) (x : V)
    {T : Finset V} (hT : T ∈ X.topFaces) (hx : x ∈ T) :
    ((Finset.univ : Finset (X.LinkVertex ({x} : Finset V))).filter
      (fun b ↦ insert b.1 ({x} : Finset V) ⊆ T)).card = 2 := by
  classical
  let source : Finset (X.LinkVertex ({x} : Finset V)) :=
    Finset.univ.filter fun b ↦ insert b.1 ({x} : Finset V) ⊆ T
  let target : Finset V := T.erase x
  have hcard : T.card = 3 := by simpa [hdim] using X.top_card T hT
  have hsourceTarget : source.card = target.card := by
    apply Finset.card_bij (fun b _hb ↦ b.1)
    · intro b hb
      have hbsub : insert b.1 ({x} : Finset V) ⊆ T :=
        (Finset.mem_filter.mp hb).2
      apply Finset.mem_erase.mpr
      exact ⟨by simpa using b.2.1,
        hbsub (Finset.mem_insert_self _ _)⟩
    · intro b₁ _hb₁ b₂ _hb₂ heq
      exact Subtype.ext heq
    · intro y hy
      have hyData := Finset.mem_erase.mp hy
      have hyFace : X.IsFace (insert y ({x} : Finset V)) := by
        exact ⟨T, hT, by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact hyData.2
          · simp only [Finset.mem_singleton] at hz
            subst z
            exact hx⟩
      let b : X.LinkVertex ({x} : Finset V) :=
        ⟨y, by simpa using hyData.1, hyFace⟩
      refine ⟨b, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hyData.2
      · simp only [Finset.mem_singleton] at hz
        subst z
        exact hx
  change source.card = 2
  rw [hsourceTarget]
  dsimp [target]
  rw [Finset.card_erase_of_mem hx, hcard]

/-- The total weighted volume of the link at a vertex of a two-complex is
twice the total top-face weight of the triangles containing that vertex. -/
theorem vertexLink_graphVolume_eq_two_mul_topWeight_sum
    (X : MeasuredComplex V) (hdim : X.dim = 2) (x : V) :
    WeightedLift.graphVolume (X.linkGraph ({x} : Finset V)) =
      2 * ∑ T ∈ X.topFaces with x ∈ T, X.topWeight T := by
  classical
  unfold WeightedLift.graphVolume
  simp_rw [vertexLink_degree_eq_topWeight_sum X hdim x]
  calc
    (∑ b : X.LinkVertex ({x} : Finset V),
        ∑ T ∈ X.topFaces with insert b.1 ({x} : Finset V) ⊆ T,
          X.topWeight T) =
        ∑ T ∈ X.topFaces,
          ∑ b ∈ (Finset.univ :
              Finset (X.LinkVertex ({x} : Finset V))) with
            insert b.1 ({x} : Finset V) ⊆ T, X.topWeight T := by
      apply Finset.sum_comm'
      intro b T
      simp [and_comm]
    _ = ∑ T ∈ X.topFaces,
          if x ∈ T then 2 * X.topWeight T else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      by_cases hx : x ∈ T
      · rw [if_pos hx]
        rw [Finset.sum_const, vertexLink_incidence_card X hdim x hT hx]
        norm_num
      · rw [if_neg hx]
        apply Finset.sum_eq_zero
        intro b hb
        exfalso
        exact hx ((Finset.mem_filter.mp hb).2 (by simp))
    _ = 2 * ∑ T ∈ X.topFaces with x ∈ T, X.topWeight T := by
      rw [Finset.mul_sum]
      rw [Finset.sum_filter]

end MeasuredComplex

end HDXLean
