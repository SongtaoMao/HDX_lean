import HDXLean.Basic
import HDXLean.CharTwoTriples
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FinCases

namespace HDXLean.GolowichProduct
open scoped BigOperators

abbrev Cube (k : ℕ) := Fin k → F₂
def cubeBasis (k : ℕ) (i : Fin k) : Cube k := Pi.single i 1

theorem cubeBasis_ne_zero (k : ℕ) (i : Fin k) : cubeBasis k i ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [cubeBasis] at hi

theorem cubeBasis_injective (k : ℕ) : Function.Injective (cubeBasis k) := by
  intro i j h
  by_contra hij
  have hi := congrFun h i
  simp [cubeBasis, hij] at hi

theorem cube_add_self (k : ℕ) (x : Cube k) : x + x = 0 := by
  funext i
  change x i + x i = 0
  generalize x i = a
  fin_cases a <;> decide

def CubeAdj (k : ℕ) (x y : Cube k) : Prop := ∃ i, y = x + cubeBasis k i

theorem cubeAdj_symm (k : ℕ) {x y : Cube k} (h : CubeAdj k x y) : CubeAdj k y x := by
  obtain ⟨i, rfl⟩ := h
  exact ⟨i, by rw [add_assoc, cube_add_self, add_zero]⟩

noncomputable def cubeGraph (k : ℕ) : WeightedGraph (Cube k) := by
  classical
  exact
    { weight x y := if CubeAdj k x y then 1 else 0
      weight_symm x y := by
        have : CubeAdj k x y ↔ CubeAdj k y x := ⟨cubeAdj_symm k, cubeAdj_symm k⟩
        simp only [this]
      weight_self x := by
        have hn : ¬ CubeAdj k x x := by
          rintro ⟨i, hi⟩
          apply cubeBasis_ne_zero k i
          exact (add_left_cancel (show x + cubeBasis k i = x + 0 by simpa using hi.symm))
        simp [hn]
      weight_nonneg x y := by split_ifs <;> norm_num }

@[simp] theorem cubeGraph_adj (k : ℕ) (x y : Cube k) :
    (cubeGraph k).Adj x y ↔ CubeAdj k x y := by
  classical
  change (0 < (if CubeAdj k x y then (1 : ℝ) else 0)) ↔ CubeAdj k x y
  split_ifs <;> simp_all

theorem cubeGraph_translation (k : ℕ) (g x y : Cube k) :
    (cubeGraph k).weight (g + x) (g + y) = (cubeGraph k).weight x y := by
  classical
  have h : CubeAdj k (g + x) (g + y) ↔ CubeAdj k x y := by
    simp only [CubeAdj, add_assoc, add_right_inj]
  change (if CubeAdj k (g + x) (g + y) then (1 : ℝ) else 0) =
    (if CubeAdj k x y then 1 else 0)
  simp only [h]

theorem cubeGraph_neighbor (k : ℕ) (hk : 1 ≤ k) (x : Cube k) :
    ∃ y, (cubeGraph k).Adj x y :=
  ⟨x + cubeBasis k ⟨0, by omega⟩, (cubeGraph_adj k _ _).mpr ⟨_, rfl⟩⟩

/-- A coordinate-by-coordinate path, independent of any spectral input. -/
theorem cubeGraph_connected (k : ℕ) : (cubeGraph k).Connected := by
  classical
  intro x y
  have hpath : ∀ (S : Finset (Fin k)) (z : Cube k),
      Relation.ReflTransGen (cubeGraph k).Adj x (x + ∑ i ∈ S, Pi.single i (z i)) := by
    intro S z
    induction S using Finset.induction_on with
    | empty => simpa using (Relation.ReflTransGen.refl (a := x) (r := (cubeGraph k).Adj))
    | @insert i S hi ih =>
      rw [Finset.sum_insert hi]
      have hz : z i = 0 ∨ z i = 1 := by
        generalize z i = a
        fin_cases a
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hz with hz | hz
      · simpa [hz] using ih
      · apply ih.tail
        apply (cubeGraph_adj k _ _).mpr
        refine ⟨i, ?_⟩
        simp only [hz, cubeBasis]
        ac_rfl
  have h := hpath Finset.univ (y - x)
  rw [Finset.univ_sum_single] at h
  have hxy : x + (y - x) = y := by
    rw [add_comm, sub_add_cancel]
  rwa [hxy] at h

theorem cube_card_ge_four (k : ℕ) (hk : 2 ≤ k) : 4 ≤ Fintype.card (Cube k) := by
  have hc : Fintype.card (Cube k) = 2 ^ k := by simp [Cube, F₂]
  rw [hc]
  exact (show 4 = 2 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right (by omega) hk

end HDXLean.GolowichProduct
