import HDXLean.WeightedRayleigh
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp

/-! The sum-of-squares argument in Lemma 5.1, for a positive mixture of
cliques of a common size. No literature assumption is used. -/
namespace HDXLean.WeightedGraph
open scoped BigOperators
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

theorem clique_row_sum (T : Finset V) (u : V) (f : V → ℝ) :
    (∑ v, if u ≠ v ∧ u ∈ T ∧ v ∈ T then f v else 0) =
      if u ∈ T then (∑ v ∈ T, f v) - f u else 0 := by
  classical
  by_cases hu : u ∈ T
  · have he : ∀ v, (u ≠ v ∧ u ∈ T ∧ v ∈ T) ↔ v ∈ T.erase u := by
      intro v; simp [hu, Finset.mem_erase, ne_comm]
    simp_rw [he]
    rw [Finset.sum_ite_mem, Finset.univ_inter, if_pos hu, Finset.sum_erase_eq_sub hu]
  · simp [hu]

theorem clique_energy_sum (T : Finset V) (f : V → ℝ) :
    (∑ u, ∑ v, if u ≠ v ∧ u ∈ T ∧ v ∈ T then f u * f v else 0) =
      (∑ u ∈ T, f u) ^ 2 - ∑ u ∈ T, (f u) ^ 2 := by
  have hrow : ∀ u,
      (∑ v, if u ≠ v ∧ u ∈ T ∧ v ∈ T then f u * f v else 0) =
      if u ∈ T then f u * ((∑ v ∈ T, f v) - f u) else 0 := by
    intro u
    have h := clique_row_sum T u f
    have hm := congrArg (fun x : ℝ ↦ f u * x) h
    simpa only [Finset.mul_sum, mul_ite, mul_zero] using hm
  simp_rw [hrow]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, pow_two]

/-- The clique-incidence representation is checked by the caller against its
actual graph weights. It is not a spectral certificate. -/
theorem lowerRayleighBound_of_clique_mixture (G : WeightedGraph V)
    (C : I → Finset V) (w : I → ℝ) (ell : ℕ) (hell : 0 < ell)
    (hcard : ∀ i, (C i).card = ell + 1) (hw : ∀ i, 0 ≤ w i)
    (hweight : ∀ u v, G.weight u v =
      ∑ i, if u ≠ v ∧ u ∈ C i ∧ v ∈ C i then w i else 0) :
    G.LowerRayleighBound (-1 / (ell : ℝ)) := by
  intro f
  have hdeg : ∀ u, G.degree u =
      (ell : ℝ) * ∑ i, if u ∈ C i then w i else 0 := by
    intro u
    unfold degree
    simp_rw [hweight]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [clique_row_sum]
    by_cases hu : u ∈ C i
    · simp [hu, hcard, Nat.cast_add, Nat.cast_one]
      ring
    · simp [hu]
  have hn : G.sqNorm f = (ell : ℝ) *
      ∑ i, w i * ∑ u ∈ C i, (f u) ^ 2 := by
    unfold sqNorm
    simp_rw [hdeg, mul_assoc, Finset.sum_mul]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    simp only [ite_mul, zero_mul]
    simp only [Finset.sum_ite_mem, Finset.univ_inter]
  have he : G.energy f f =
      ∑ i, w i * ((∑ u ∈ C i, f u) ^ 2 - ∑ u ∈ C i, (f u) ^ 2) := by
    unfold energy
    simp_rw [hweight, Finset.sum_mul]
    conv_lhs =>
      arg 2
      ext u
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← clique_energy_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> ring
  have hpos : 0 ≤ ∑ i, w i * (∑ u ∈ C i, f u) ^ 2 :=
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hw i) (sq_nonneg _))
  rw [hn, he]
  have hellR : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  rw [← mul_assoc, div_mul_cancel₀ _ hellR]
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

end HDXLean.WeightedGraph
