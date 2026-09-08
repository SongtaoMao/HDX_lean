import HDXLean.ProductFaces
import HDXLean.UniversalLinkLowerBound

namespace HDXLean.GolowichProduct
variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]

/-- Connectivity of the actual product one-skeleton, proved without invoking
the global-gap clause of the cited spectral theorem. -/
theorem ProductData.empty_link_connected (G : WeightedGraph V) (K : ℕ)
    (Z : ProductData G K A) (hK : 2 ≤ K) (hA : K + 1 ≤ Fintype.card A)
    (hc : G.Connected) (hneigh : ∀ u, ∃ v, G.Adj u v) :
    (Z.complex.linkGraph ∅).Connected := by
  classical
  let vertex (z : V × A) : Z.complex.LinkVertex ∅ :=
    ⟨z, by simp, by
      have h := (product_face_pair_iff G K Z hK hA hneigh z z).mpr (Or.inl rfl)
      simpa using h⟩
  have hedge (x y : V × A) (hlab : x.2 ≠ y.2)
      (hbase : x.1 = y.1 ∨ G.Adj x.1 y.1) :
      (Z.complex.linkGraph ∅).Adj (vertex x) (vertex y) := by
    apply (Z.complex.linkGraph_adj_iff ∅ _ _).mpr
    refine ⟨fun h ↦ hlab (congrArg (fun z : Z.complex.LinkVertex ∅ ↦ z.1.2) h), ?_⟩
    have h := (product_face_pair_iff G K Z hK hA hneigh x y).mpr (Or.inr ⟨hlab, hbase⟩)
    simpa [vertex, Finset.pair_comm] using h
  intro x y
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card
    (by omega : 1 < Fintype.card A) x.1.2
  have hbase := hc x.1.1 y.1.1
  have hpath : ∀ {u v}, Relation.ReflTransGen G.Adj u v →
      Relation.ReflTransGen (Z.complex.linkGraph ∅).Adj
        (vertex (u, x.1.2)) (vertex (v, x.1.2)) := by
    intro u v h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail v w _ hvw ih =>
      exact (ih.tail (hedge (v, x.1.2) (w, b) hb.symm (Or.inr hvw))).tail
        (hedge (w, b) (w, x.1.2) hb (Or.inl rfl))
  have hp := hpath hbase
  have hx : vertex (x.1.1, x.1.2) = x := Subtype.ext rfl
  rw [hx] at hp
  by_cases hy : x.1.2 = y.1.2
  · have he : vertex (y.1.1, x.1.2) = y := Subtype.ext (by
      change (y.1.1, x.1.2) = y.1
      rw [hy])
    rwa [he] at hp
  · have he : vertex (y.1.1, y.1.2) = y := Subtype.ext rfl
    have h := hp.tail (hedge (y.1.1, x.1.2) (y.1.1, y.1.2) hy (Or.inl rfl))
    rwa [he] at h

end HDXLean.GolowichProduct
