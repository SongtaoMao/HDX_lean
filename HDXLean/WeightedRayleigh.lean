import HDXLean.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! A one-sided Rayleigh bound and a lower bound imply the native two-sided
walk norm bound. This elementary polarization proof works for nonregular
weighted graphs and uses no assumed spectral-decomposition certificate. -/
namespace HDXLean.WeightedGraph
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def energy (G : WeightedGraph V) (f g : V → ℝ) : ℝ :=
  ∑ u, ∑ v, G.weight u v * f u * g v

def UpperRayleighBound (G : WeightedGraph V) (a : ℝ) : Prop :=
  ∀ f : V → ℝ, G.weightedMean f = 0 → G.energy f f ≤ a * G.sqNorm f

def LowerRayleighBound (G : WeightedGraph V) (a : ℝ) : Prop :=
  ∀ f : V → ℝ, a * G.sqNorm f ≤ G.energy f f

theorem energy_symm (G : WeightedGraph V) (f g : V → ℝ) :
    G.energy f g = G.energy g f := by
  unfold energy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [G.weight_symm]
  ring

theorem degree_mul_walk (G : WeightedGraph V) (hdeg : ∀ u, 0 < G.degree u)
    (f : V → ℝ) (u : V) :
    G.degree u * G.walk f u = ∑ v, G.weight u v * f v := by
  unfold walk
  exact mul_div_cancel₀ _ (hdeg u).ne'

theorem energy_walk (G : WeightedGraph V) (hdeg : ∀ u, 0 < G.degree u)
    (f g : V → ℝ) : G.energy f g = ∑ u, G.degree u * f u * G.walk g u := by
  unfold energy
  apply Finset.sum_congr rfl
  intro u _
  calc
    _ = f u * ∑ v, G.weight u v * g v := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    _ = _ := by rw [← G.degree_mul_walk hdeg]; ring

theorem weightedMean_walk (G : WeightedGraph V) (hdeg : ∀ u, 0 < G.degree u)
    (f : V → ℝ) : G.weightedMean (G.walk f) = G.weightedMean f := by
  unfold weightedMean
  simp_rw [G.degree_mul_walk hdeg]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl (fun u _ ↦ G.weight_symm u v)

theorem energy_polarization (G : WeightedGraph V) (f g : V → ℝ) :
    G.energy (fun u ↦ f u + g u) (fun u ↦ f u + g u) -
      G.energy (fun u ↦ f u - g u) (fun u ↦ f u - g u) =
      4 * G.energy f g := by
  have h : G.energy (fun u ↦ f u + g u) (fun u ↦ f u + g u) -
      G.energy (fun u ↦ f u - g u) (fun u ↦ f u - g u) =
      2 * G.energy f g + 2 * G.energy g f := by
    unfold energy
    simp only [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [G.energy_symm g f] at h
  linarith

theorem sqNorm_parallelogram (G : WeightedGraph V) (f g : V → ℝ) :
    G.sqNorm (fun u ↦ f u + g u) + G.sqNorm (fun u ↦ f u - g u) =
      2 * (G.sqNorm f + G.sqNorm g) := by
  unfold sqNorm
  rw [mul_add]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem energy_cross_le (G : WeightedGraph V) {a : ℝ}
    (hu : G.UpperRayleighBound a) (hl : G.LowerRayleighBound (-a))
    (f g : V → ℝ) (hf : G.weightedMean f = 0) (hg : G.weightedMean g = 0) :
    2 * G.energy f g ≤ a * (G.sqNorm f + G.sqNorm g) := by
  have hp : G.weightedMean (fun u ↦ f u + g u) = 0 := by
    simpa [weightedMean, mul_add, Finset.sum_add_distrib] using congrArg₂ (· + ·) hf hg
  have hupper := hu _ hp
  have hlower := hl (fun u ↦ f u - g u)
  have he := G.energy_polarization f g
  have hn := G.sqNorm_parallelogram f g
  have hna := congrArg (fun x : ℝ ↦ a * x) hn
  nlinarith

theorem twoSidedSpectralBound_of_rayleigh (G : WeightedGraph V)
    (hdeg : ∀ u, 0 < G.degree u) {a : ℝ} (ha : 0 < a)
    (hu : G.UpperRayleighBound a) (hl : G.LowerRayleighBound (-a)) :
    G.TwoSidedSpectralBound a := by
  refine ⟨ha.le, fun f hf ↦ ?_⟩
  have hscaled : G.weightedMean (fun u ↦ a * f u) = 0 := by
    calc
      _ = a * G.weightedMean f := by
        unfold weightedMean
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intros; ring
      _ = 0 := by rw [hf, mul_zero]
  have hcross := G.energy_cross_le hu hl (fun u ↦ a * f u) (G.walk f)
    hscaled (by rw [G.weightedMean_walk hdeg, hf])
  have he : G.energy (fun u ↦ a * f u) (G.walk f) = a * G.sqNorm (G.walk f) := by
    rw [G.energy_symm, G.energy_walk hdeg]
    have hw : G.walk (fun u ↦ a * f u) = fun u ↦ a * G.walk f u := by
      funext u
      unfold walk
      rw [← mul_div_assoc]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intros; ring
    rw [hw]
    unfold sqNorm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intros; ring
  have hn : G.sqNorm (fun u ↦ a * f u) = a ^ 2 * G.sqNorm f := by
    unfold sqNorm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intros; ring
  rw [he, hn] at hcross
  nlinarith

end HDXLean.WeightedGraph
