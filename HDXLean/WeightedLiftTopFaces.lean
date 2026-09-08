import HDXLean.Basic
import Mathlib.Data.Finset.Card

/-!
# Top faces of the weighted dimension lift

This file defines the underlying simple pure complex in Section 5.  A lifted
top face is literally a `(d+1)`-element subset of the three fibers above some
base triangle.  Equal subsets arising from different parent triangles are
identified automatically because top faces form a `Finset`.
-/

namespace HDXLean

namespace WeightedLift

variable {Gamma A : Type*}
  [Fintype Gamma] [DecidableEq Gamma]
  [Fintype A] [DecidableEq A]

/-- The union of the complete fibers above a finite set of base vertices. -/
def fibersAbove (tau : Finset Gamma) : Finset (Gamma × A) :=
  tau.product Finset.univ

omit [Fintype Gamma] [DecidableEq Gamma] [DecidableEq A] in
@[simp]
theorem mem_fibersAbove {tau : Finset Gamma} {z : Gamma × A} :
    z ∈ fibersAbove (A := A) tau ↔ z.1 ∈ tau := by
  simp [fibersAbove]

omit [Fintype Gamma] [DecidableEq Gamma] [DecidableEq A] in
theorem card_fibersAbove (tau : Finset Gamma) :
    (fibersAbove (A := A) tau).card = tau.card * Fintype.card A := by
  simp [fibersAbove]

/-- A base top face is compatible with a proposed lifted face when all lifted
vertices lie in its three fibers. -/
def CompatibleParent (tau : Finset Gamma) (T : Finset (Gamma × A)) : Prop :=
  T ⊆ fibersAbove (A := A) tau

/-- The set `Y(d)` from Section 5. -/
noncomputable def topFaces (X : MeasuredComplex Gamma) (d : ℕ) :
    Finset (Finset (Gamma × A)) := by
  classical
  exact Finset.univ.filter fun T ↦
    T.card = d + 1 ∧
      ∃ tau ∈ X.topFaces, CompatibleParent (A := A) tau T

omit [DecidableEq A] in
@[simp]
theorem mem_topFaces {X : MeasuredComplex Gamma} {d : ℕ}
    {T : Finset (Gamma × A)} :
    T ∈ topFaces (A := A) X d ↔
      T.card = d + 1 ∧
        ∃ tau ∈ X.topFaces, CompatibleParent (A := A) tau T := by
  classical
  simp [topFaces]

omit [DecidableEq A] in
/-- Every lifted top face has the required cardinality. -/
theorem topFace_card {X : MeasuredComplex Gamma} {d : ℕ}
    (T : Finset (Gamma × A)) (hT : T ∈ topFaces (A := A) X d) :
    T.card = d + 1 :=
  (mem_topFaces.mp hT).1

/-- A measured complex has at least one top face because its positive top
weights sum to one. -/
theorem base_topFaces_nonempty (X : MeasuredComplex Gamma) :
    X.topFaces.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hsum := X.topWeight_sum
  simp [h] at hsum

omit [DecidableEq A] in
/-- Under the paper's size assumptions there is room for a lifted top face
inside every base triangle. -/
theorem topFaces_nonempty (X : MeasuredComplex Gamma) (d : ℕ)
    (hdimension : X.dim = 2) (hd : 1 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) :
    (topFaces (A := A) X d).Nonempty := by
  obtain ⟨tau, htau⟩ := base_topFaces_nonempty X
  have htauCard : tau.card = 3 := by
    simpa [hdimension] using X.top_card tau htau
  have hcapacity : d + 1 ≤ (fibersAbove (A := A) tau).card := by
    rw [card_fibersAbove, htauCard]
    have hm' : 2 * d ≤ Fintype.card A := hm
    omega
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq hcapacity
  refine ⟨T, mem_topFaces.mpr ⟨hTcard, tau, htau, ?_⟩⟩
  exact hTsub

/-- Occupancy of the fiber above `x`. -/
def occupancy (T : Finset (Gamma × A)) (x : Gamma) : ℕ :=
  (Finset.univ.filter fun a : A ↦ (x, a) ∈ T).card

omit [Fintype Gamma] in
/-- Occupancy never exceeds the fiber size. -/
theorem occupancy_le_card (T : Finset (Gamma × A)) (x : Gamma) :
    occupancy T x ≤ Fintype.card A := by
  exact Finset.card_filter_le _ _

omit [Fintype Gamma] in
/-- Positive occupancy is equivalent to the presence of a lifted vertex over
the base vertex. -/
theorem occupancy_pos_iff (T : Finset (Gamma × A)) (x : Gamma) :
    0 < occupancy T x ↔ ∃ a : A, (x, a) ∈ T := by
  rw [occupancy, Finset.card_pos, Finset.filter_nonempty_iff]
  simp

/-- The occupied part of a proposed parent triangle. -/
def occupiedSupport (tau : Finset Gamma) (T : Finset (Gamma × A)) :
    Finset Gamma :=
  tau.filter fun x ↦ 0 < occupancy T x

omit [Fintype Gamma] in
theorem mem_occupiedSupport {tau : Finset Gamma}
    {T : Finset (Gamma × A)} {x : Gamma} :
    x ∈ occupiedSupport (A := A) tau T ↔
      x ∈ tau ∧ ∃ a : A, (x, a) ∈ T := by
  simp [occupiedSupport, occupancy_pos_iff]

omit [Fintype Gamma] in
/-- A nonempty compatible lifted set occupies at least one parent fiber. -/
theorem occupiedSupport_nonempty {tau : Finset Gamma}
    {T : Finset (Gamma × A)}
    (hcompatible : CompatibleParent (A := A) tau T)
    (hT : T.Nonempty) :
    (occupiedSupport (A := A) tau T).Nonempty := by
  obtain ⟨z, hz⟩ := hT
  refine ⟨z.1, mem_occupiedSupport.mpr ⟨?_, z.2, hz⟩⟩
  exact mem_fibersAbove.mp (hcompatible hz)

end WeightedLift

end HDXLean
