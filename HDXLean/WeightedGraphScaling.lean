import HDXLean.FiniteRegularSpectrum

/-!
# Positive rescaling of finite weighted graphs

Conditioned link calculations naturally determine edge weights only up to a
common positive factor.  This file proves once and for all that such a factor
does not change the random walk, connectedness, or a two-sided spectral bound.
-/

namespace HDXLean

open scoped BigOperators

namespace WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A positive global rescaling leaves the random-walk operator unchanged. -/
theorem walk_scale (G : WeightedGraph V) (c : ℝ) (hc : 0 < c)
    (f : V → ℝ) (u : V) :
    (G.scale c hc.le).walk f u = G.walk f u := by
  unfold walk
  rw [degree_scale]
  change (∑ v : V, c * G.weight u v * f v) / (c * G.degree u) = _
  rw [show (∑ v : V, c * G.weight u v * f v) =
      c * ∑ v : V, G.weight u v * f v by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    ring]
  exact mul_div_mul_left _ _ hc.ne'

/-- The unnormalized stationary mean scales by the common edge factor. -/
theorem weightedMean_scale (G : WeightedGraph V) (c : ℝ) (hc : 0 ≤ c)
    (f : V → ℝ) :
    (G.scale c hc).weightedMean f = c * G.weightedMean f := by
  unfold weightedMean
  simp_rw [degree_scale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _hu
  ring

/-- The squared stationary seminorm scales by the common edge factor. -/
theorem sqNorm_scale (G : WeightedGraph V) (c : ℝ) (hc : 0 ≤ c)
    (f : V → ℝ) :
    (G.scale c hc).sqNorm f = c * G.sqNorm f := by
  unfold sqNorm
  simp_rw [degree_scale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _hu
  ring

/-- Positive rescaling preserves the positive-weight adjacency relation. -/
theorem adj_scale_iff (G : WeightedGraph V) (c : ℝ) (hc : 0 < c)
    (u v : V) :
    (G.scale c hc.le).Adj u v ↔ G.Adj u v := by
  unfold Adj
  change 0 < c * G.weight u v ↔ 0 < G.weight u v
  exact mul_pos_iff_of_pos_left hc

/-- Positive rescaling preserves combinatorial connectedness. -/
theorem connected_scale (G : WeightedGraph V) (c : ℝ) (hc : 0 < c)
    (hconnected : G.Connected) :
    (G.scale c hc.le).Connected := by
  intro u v
  have huv := hconnected u v
  induction huv with
  | refl => exact Relation.ReflTransGen.refl
  | tail _hpath hedge ih =>
      exact ih.tail ((adj_scale_iff G c hc _ _).2 hedge)

/-- A two-sided spectral bound is invariant under positive global scaling. -/
theorem twoSidedSpectralBound_scale (G : WeightedGraph V) (c : ℝ)
    (hc : 0 < c) {lambda : ℝ} (hbound : G.TwoSidedSpectralBound lambda) :
    (G.scale c hc.le).TwoSidedSpectralBound lambda := by
  refine ⟨hbound.1, ?_⟩
  intro f hmeanScaled
  have hmean : G.weightedMean f = 0 := by
    rw [weightedMean_scale] at hmeanScaled
    exact (mul_eq_zero.mp hmeanScaled).resolve_left hc.ne'
  have hcontract := hbound.2 f hmean
  have hwalk : (G.scale c hc.le).walk f = G.walk f := by
    funext u
    exact walk_scale G c hc f u
  rw [sqNorm_scale, hwalk, sqNorm_scale]
  calc
    c * G.sqNorm (G.walk f) ≤
        c * (lambda ^ 2 * G.sqNorm f) :=
      mul_le_mul_of_nonneg_left hcontract hc.le
    _ = lambda ^ 2 * (c * G.sqNorm f) := by ring

/-- Positive rescaling preserves a full spectral-expander certificate. -/
theorem isTwoSidedSpectralExpander_scale (G : WeightedGraph V) (c : ℝ)
    (hc : 0 < c) {lambda : ℝ}
    (hexpander : G.IsTwoSidedSpectralExpander lambda) :
    (G.scale c hc.le).IsTwoSidedSpectralExpander lambda :=
  ⟨connected_scale G c hc hexpander.1,
    twoSidedSpectralBound_scale G c hc hexpander.2⟩

end WeightedGraph

end HDXLean
