import HDXLean.WeightedGraphScaling
import HDXLean.MeasuredSkeleton

/-!
# Exact spectral gaps and their geometric transport

An exact spectral gap is a statement about the native random-walk operator,
not a numerical surrogate. The largest eigenvalue on the stationary mean-zero
subspace is specified by its universal bound and an attained eigenvalue.
-/
namespace HDXLean.WeightedGraph
open scoped BigOperators
open AffineRelationSpectrum
variable {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]

/-- The usual one-sided gap `1 - lambda_2`, specified without ordering a
matrix spectrum. The witness prevents vacuous spectral assertions. -/
def HasSpectralGap (G : WeightedGraph V) (gap : ℝ) : Prop :=
  IsMeanZeroEigenvalue G (1 - gap) ∧
    ∀ μ : ℝ, IsMeanZeroEigenvalue G μ → μ ≤ 1 - gap

theorem HasSpectralGap.unique {G : WeightedGraph V} {gap gap' : ℝ}
    (h : G.HasSpectralGap gap) (h' : G.HasSpectralGap gap') : gap = gap' := by
  have hle := h.2 _ h'.1
  have hge := h'.2 _ h.1
  linarith

theorem meanZeroEigenvalue_scale_iff (G : WeightedGraph V) (c : ℝ) (hc : 0 < c)
    (μ : ℝ) : IsMeanZeroEigenvalue (G.scale c hc.le) μ ↔
      IsMeanZeroEigenvalue G μ := by
  constructor <;> rintro ⟨f, hn, hm, hw⟩ <;> refine ⟨f, hn, ?_, ?_⟩
  · rw [weightedMean_scale] at hm
    exact (mul_eq_zero.mp hm).resolve_left hc.ne'
  · funext u
    have h := congrFun hw u
    simpa only [walk_scale G c hc] using h
  · rw [weightedMean_scale, hm, mul_zero]
  · funext u
    rw [walk_scale G c hc]
    exact congrFun hw u

theorem meanZeroEigenvalue_relabel_iff (G : WeightedGraph V) (e : V ≃ W)
    (μ : ℝ) : IsMeanZeroEigenvalue (G.relabel e) μ ↔
      IsMeanZeroEigenvalue G μ := by
  constructor
  · rintro ⟨f, hn, hm, hw⟩
    refine ⟨f ∘ e, ?_, ?_, ?_⟩
    · intro h
      apply hn
      funext w
      simpa using congrFun h (e.symm w)
    · simpa only [weightedMean_relabel] using hm
    · funext v
      have h := congrFun hw (e v)
      simpa only [walk_relabel, Equiv.symm_apply_apply, Function.comp_apply] using h
  · rintro ⟨f, hn, hm, hw⟩
    refine ⟨f ∘ e.symm, ?_, ?_, ?_⟩
    · intro h
      apply hn
      funext v
      simpa using congrFun h (e v)
    · simpa only [weightedMean_relabel, Function.comp_def,
        Equiv.symm_apply_apply] using hm
    · funext w
      simpa only [walk_relabel, Function.comp_def, Equiv.symm_apply_apply]
        using congrFun hw (e.symm w)

theorem HasSpectralGap.scale {G : WeightedGraph V} {gap : ℝ}
    (h : G.HasSpectralGap gap) (c : ℝ) (hc : 0 < c) :
    (G.scale c hc.le).HasSpectralGap gap :=
  ⟨(meanZeroEigenvalue_scale_iff G c hc _).mpr h.1,
    fun μ hμ ↦ h.2 μ ((meanZeroEigenvalue_scale_iff G c hc _).mp hμ)⟩

theorem HasSpectralGap.relabel {G : WeightedGraph V} {gap : ℝ}
    (h : G.HasSpectralGap gap) (e : V ≃ W) :
    (G.relabel e).HasSpectralGap gap :=
  ⟨(meanZeroEigenvalue_relabel_iff G e _).mpr h.1,
    fun μ hμ ↦ h.2 μ ((meanZeroEigenvalue_relabel_iff G e _).mp hμ)⟩

end HDXLean.WeightedGraph

namespace HDXLean.MeasuredComplex
open AffineRelationSpectrum
variable {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]

theorem link_eigenvalue_relabel (X : MeasuredComplex V) (e : V ≃ W)
    (F : Finset V) {μ : ℝ} (h : IsMeanZeroEigenvalue (X.linkGraph F) μ) :
    IsMeanZeroEigenvalue ((X.relabel e).linkGraph (e.finsetCongr F)) μ := by
  rw [X.linkGraph_relabel]
  exact (WeightedGraph.meanZeroEigenvalue_relabel_iff _ _ _).mpr h

theorem link_spectralGap_relabel (X : MeasuredComplex V) (e : V ≃ W)
    (F : Finset V) {gap : ℝ} (h : (X.linkGraph F).HasSpectralGap gap) :
    ((X.relabel e).linkGraph (e.finsetCongr F)).HasSpectralGap gap := by
  rw [X.linkGraph_relabel]
  exact h.relabel _

/-- Passing to an induced measured skeleton preserves every link eigenvalue
in the range where the link graph exists. -/
theorem skeleton_link_eigenvalue (X : MeasuredComplex V) (d : ℕ) (hd : d ≤ X.dim)
    (F : Finset V) (hF : F.card + 1 ≤ d) {μ : ℝ}
    (h : IsMeanZeroEigenvalue (X.linkGraph F) μ) :
    IsMeanZeroEigenvalue ((X.skeleton d hd).linkGraph F) μ := by
  rw [X.skeleton_linkGraph_eq d hd F hF]
  apply (WeightedGraph.meanZeroEigenvalue_scale_iff _ _
    (X.skeletonLinkScale_pos d hd F hF) _).mpr
  exact (WeightedGraph.meanZeroEigenvalue_relabel_iff _ _ _).mpr h

/-- The exact spectral gap, including attainment, survives the skeleton
operation. This includes the empty-face link, i.e. the global graph. -/
theorem skeleton_link_spectralGap (X : MeasuredComplex V) (d : ℕ) (hd : d ≤ X.dim)
    (F : Finset V) (hF : F.card + 1 ≤ d) {gap : ℝ}
    (h : (X.linkGraph F).HasSpectralGap gap) :
    ((X.skeleton d hd).linkGraph F).HasSpectralGap gap := by
  rw [X.skeleton_linkGraph_eq d hd F hF]
  exact (h.relabel _).scale _ (X.skeletonLinkScale_pos d hd F hF)

end HDXLean.MeasuredComplex
