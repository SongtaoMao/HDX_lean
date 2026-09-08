import HDXLean.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Order

/-!
# Generator set of the weighted dimension lift

This file proves formula (5.2) and its two immediate algebraic consequences at
the level of finite binary vector spaces: the lifted generator set has size
`m (|S| + 1) - 1` and spans the product whenever the base set spans.
-/

namespace HDXLean

namespace WeightedLift

variable {Gamma A : Type*}
  [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma] [DecidableEq Gamma]
  [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A]

/-- The generator set in equation (5.2). -/
def generators (S : Finset Gamma) : Finset (Gamma × A) :=
  (({0} : Finset Gamma).product (Finset.univ.erase 0)) ∪
    (S.product Finset.univ)

omit [Module F₂ Gamma] [Fintype Gamma] [Module F₂ A] in
theorem mem_generators_iff {S : Finset Gamma} {g : Gamma} {a : A} :
    (g, a) ∈ generators (A := A) S ↔
      (g = 0 ∧ a ≠ 0) ∨ g ∈ S := by
  constructor
  · intro hz
    rcases Finset.mem_union.mp hz with hleft | hright
    · have hparts := Finset.mem_product.mp hleft
      left
      exact ⟨Finset.mem_singleton.mp hparts.1,
        (Finset.mem_erase.mp hparts.2).1⟩
    · exact Or.inr (Finset.mem_product.mp hright).1
  · rintro (h | h)
    · apply Finset.mem_union_left
      exact Finset.mem_product.mpr
        ⟨Finset.mem_singleton.mpr h.1,
          Finset.mem_erase.mpr ⟨h.2, Finset.mem_univ _⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩

omit [Module F₂ Gamma] [Fintype Gamma] [Module F₂ A] in
theorem zero_not_mem_generators {S : Finset Gamma} (hzero : 0 ∉ S) :
    (0, 0) ∉ generators (A := A) S := by
  simp [mem_generators_iff, hzero]

omit [Module F₂ Gamma] [Fintype Gamma] [DecidableEq Gamma] [Module F₂ A] in
/-- The two pieces of the union in (5.2) are disjoint. -/
theorem generator_parts_disjoint {S : Finset Gamma} (hzero : 0 ∉ S) :
    Disjoint (({0} : Finset Gamma).product (Finset.univ.erase (0 : A)))
      (S.product Finset.univ) := by
  refine Finset.disjoint_left.mpr ?_
  intro z hzLeft hzRight
  have hz0 : z.1 = 0 := by simpa using (Finset.mem_product.mp hzLeft).1
  have hzS : z.1 ∈ S := (Finset.mem_product.mp hzRight).1
  exact hzero (hz0 ▸ hzS)

omit [Module F₂ Gamma] [Fintype Gamma] [Module F₂ A] in
/-- Exact degree formula from Theorem 5.1. -/
theorem card_generators {S : Finset Gamma} (hzero : 0 ∉ S) :
    (generators (A := A) S).card =
      Fintype.card A * (S.card + 1) - 1 := by
  rw [generators, Finset.card_union_of_disjoint (generator_parts_disjoint (A := A) hzero)]
  have hApos : 0 < Fintype.card A := Fintype.card_pos
  have hfirst :
      (({0} : Finset Gamma).product (Finset.univ.erase (0 : A))).card =
        Fintype.card A - 1 := by simp
  have hsecond : (S.product (Finset.univ : Finset A)).card =
      S.card * Fintype.card A := by simp
  rw [hfirst, hsecond]
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm (Fintype.card A) S.card]
  omega

omit [Module F₂ Gamma] [Fintype Gamma] [Module F₂ A] in
/-- Negation symmetry is preserved by the lift. -/
theorem neg_mem_generators_iff {S : Finset Gamma}
    (hneg : ∀ s, -s ∈ S ↔ s ∈ S) (z : Gamma × A) :
    -z ∈ generators (A := A) S ↔ z ∈ generators (A := A) S := by
  rcases z with ⟨g, a⟩
  simp only [Prod.neg_mk, mem_generators_iff]
  rw [hneg]
  constructor
  · rintro (h | h)
    · left
      exact ⟨neg_eq_zero.mp h.1, fun ha ↦ h.2 (neg_eq_zero.mpr ha)⟩
    · exact Or.inr h
  · rintro (h | h)
    · left
      exact ⟨neg_eq_zero.mpr h.1, fun ha ↦ h.2 (neg_eq_zero.mp ha)⟩
    · exact Or.inr h

omit [Fintype Gamma] in
/-- If `S` spans the base binary vector space, (5.2) spans the product. -/
theorem span_generators_eq_top {S : Finset Gamma}
    (hspan : Submodule.span F₂ (S : Set Gamma) = ⊤) :
    Submodule.span F₂ (generators (A := A) S : Set (Gamma × A)) = ⊤ := by
  apply top_unique
  intro z _
  rcases z with ⟨g, a⟩
  let W := Submodule.span F₂ (generators (A := A) S : Set (Gamma × A))
  have hg : g ∈ Submodule.span F₂ (S : Set Gamma) := by rw [hspan]; trivial
  have hbase : (g, 0) ∈ W := by
    refine Submodule.span_induction (p := fun x _ ↦ (x, 0) ∈ W) ?_ ?_ ?_ ?_ hg
    · intro s hs
      apply Submodule.subset_span
      simpa [W, mem_generators_iff] using (show s ∈ S from hs)
    · exact W.zero_mem
    · intro x y _ _ hx hy
      simpa only [Prod.mk_add_mk, add_zero] using W.add_mem hx hy
    · intro scalar x _ hx
      simpa only [Prod.smul_mk, smul_zero] using W.smul_mem scalar hx
  have hfiber : (0, a) ∈ W := by
    by_cases ha : a = 0
    · subst a
      exact W.zero_mem
    · apply Submodule.subset_span
      exact mem_generators_iff.mpr (Or.inl ⟨rfl, ha⟩)
  have hadd := W.add_mem hbase hfiber
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using hadd

end WeightedLift

end HDXLean
