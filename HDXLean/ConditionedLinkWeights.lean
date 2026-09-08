import HDXLean.WeightedLiftLinks

/-!
# Edge weights in codimension-two links

For a codimension-two conditioned face, adjoining two distinct link vertices
already gives a top-dimensional set.  Hence the link-edge sum contains at
most that one top face.  This elementary reduction is shared by all three
weighted-lift spectral cases.
-/

namespace HDXLean

open scoped BigOperators

namespace MeasuredComplex

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In a codimension-two link, the edge weight is exactly the weight of the
unique enlarged top face (and is zero when that set is not a top face). -/
theorem codimensionTwo_linkEdgeWeight_eq_topWeight
    (X : MeasuredComplex V) (F : Finset V)
    (hcodim : F.card + 1 = X.dim) (u v : X.LinkVertex F)
    (huv : u ≠ v) :
    X.linkEdgeWeight F u v = X.topWeight (insert v.1 (insert u.1 F)) := by
  classical
  let E : Finset V := insert v.1 (insert u.1 F)
  have huvValue : u.1 ≠ v.1 := by
    intro heq
    exact huv (Subtype.ext heq)
  have hvInsert : v.1 ∉ insert u.1 F := by
    simp [Ne.symm huvValue, v.2.1]
  have hEcard : E.card = X.dim + 1 := by
    dsimp [E]
    rw [Finset.card_insert_of_notMem hvInsert,
      Finset.card_insert_of_notMem u.2.1, hcodim]
  unfold linkEdgeWeight
  rw [if_neg huv]
  by_cases hE : E ∈ X.topFaces
  · have hfilter :
        X.topFaces.filter (fun T ↦ E ⊆ T) = {E} := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hT, hsub⟩
        exact (Finset.eq_of_subset_of_card_le hsub (by
          rw [X.top_card T hT, hEcard])).symm
      · rintro rfl
        exact ⟨hE, Finset.Subset.rfl⟩
    change (∑ T ∈ X.topFaces.filter (fun T ↦ E ⊆ T), X.topWeight T) =
      X.topWeight E
    rw [hfilter]
    simp
  · have hfilter :
        X.topFaces.filter (fun T ↦ E ⊆ T) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro T hT
      obtain ⟨hTtop, hsub⟩ := Finset.mem_filter.mp hT
      have hTE : E = T := Finset.eq_of_subset_of_card_le hsub (by
        rw [X.top_card T hTtop, hEcard])
      exact hE (hTE ▸ hTtop)
    change (∑ T ∈ X.topFaces.filter (fun T ↦ E ⊆ T), X.topWeight T) =
      X.topWeight E
    rw [hfilter, X.topWeight_zero E hE]
    simp

end MeasuredComplex

end HDXLean
