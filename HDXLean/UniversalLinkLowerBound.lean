import HDXLean.CliqueMixture
import HDXLean.WeightedLiftLinks

/-! Lemma 5.1 applied to the actual conditioned link graph of any measured
pure complex. Top faces containing the conditioned face are the clique
mixture; this identification is proved, not assumed. -/
namespace HDXLean.MeasuredComplex
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def linkClique (X : MeasuredComplex V) (F σ : Finset V) :
    Finset (X.LinkVertex F) := by
  classical
  exact Finset.univ.filter (fun u ↦ u.1 ∈ σ)

theorem linkClique_card (X : MeasuredComplex V) (F σ : Finset V)
    (hσ : σ ∈ X.topFaces) (hF : F ⊆ σ) :
    (X.linkClique F σ).card = X.dim + 1 - F.card := by
  classical
  have heq : (X.linkClique F σ).card = (σ \ F).card := by
    apply Finset.card_bij (fun u _ ↦ u.1)
    · intro u hu
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hu).2, u.2.1⟩
    · intro u _ v _ h
      exact Subtype.ext h
    · intro v hv
      obtain ⟨hvσ, hvF⟩ := Finset.mem_sdiff.mp hv
      let u : X.LinkVertex F := ⟨v, hvF, σ, hσ, Finset.insert_subset hvσ hF⟩
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvσ⟩, rfl⟩
  rw [heq, Finset.card_sdiff_of_subset hF, X.top_card σ hσ]

theorem linkGraph_clique_mixture (X : MeasuredComplex V) (F : Finset V)
    (u v : X.LinkVertex F) :
    (X.linkGraph F).weight u v =
      ∑ σ : {σ : Finset V // σ ∈ X.topFaces ∧ F ⊆ σ},
        if u ≠ v ∧ u ∈ X.linkClique F σ.1 ∧ v ∈ X.linkClique F σ.1
        then X.topWeight σ.1 else 0 := by
  classical
  rw [← Finset.sum_subtype (X.topFaces.filter (F ⊆ ·))
    (p := fun σ ↦ σ ∈ X.topFaces ∧ F ⊆ σ) (by intro σ; simp)
    (f := fun σ ↦ if u ≠ v ∧ u ∈ X.linkClique F σ ∧ v ∈ X.linkClique F σ
      then X.topWeight σ else 0)]
  simp only [Finset.sum_filter, linkClique, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases huv : u = v
  · subst v
    simp [linkGraph, linkEdgeWeight]
  · simp only [linkGraph, linkEdgeWeight, if_neg huv, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [Finset.insert_subset_iff]
    by_cases hF : F ⊆ σ <;> by_cases hu : u.1 ∈ σ <;> by_cases hv : v.1 ∈ σ <;>
      simp [hF, hu, hv, huv]

/-- The universal lower Rayleigh bound for the native link operator. -/
theorem linkGraph_lowerRayleigh (X : MeasuredComplex V) (F : Finset V)
    (hF : F.card + 1 ≤ X.dim) :
    (X.linkGraph F).LowerRayleighBound (-1 / ((X.dim - F.card : ℕ) : ℝ)) := by
  classical
  apply WeightedGraph.lowerRayleighBound_of_clique_mixture (X.linkGraph F)
    (fun σ : {σ : Finset V // σ ∈ X.topFaces ∧ F ⊆ σ} ↦ X.linkClique F σ.1)
    (fun σ ↦ X.topWeight σ.1) (X.dim - F.card) (by omega)
  · intro σ
    rw [X.linkClique_card F σ.1 σ.2.1 σ.2.2]
    omega
  · intro σ
    exact (X.topWeight_pos σ.1 σ.2.1).le
  · exact X.linkGraph_clique_mixture F

theorem linkGraph_degree_pos (X : MeasuredComplex V) (F : Finset V)
    (hF : F.card + 1 ≤ X.dim) (u : X.LinkVertex F) :
    0 < (X.linkGraph F).degree u := by
  classical
  obtain ⟨σ, hσ, hsub⟩ := u.2.2
  have hFS : F ⊆ σ := (Finset.subset_insert _ _).trans hsub
  have huC : u ∈ X.linkClique F σ := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub (Finset.mem_insert_self _ _)⟩
  have hc : 1 < (X.linkClique F σ).card := by
    rw [X.linkClique_card F σ hσ hFS]; omega
  obtain ⟨v, hvC, hvu⟩ := Finset.exists_mem_ne hc u
  have hvσ : v.1 ∈ σ := (Finset.mem_filter.mp hvC).2
  have he : (X.linkGraph F).Adj u v := (X.linkGraph_adj_iff F u v).mpr
    ⟨hvu.symm, σ, hσ, Finset.insert_subset hvσ hsub⟩
  exact he.trans_le (Finset.single_le_sum
    (fun v _ ↦ (X.linkGraph F).weight_nonneg u v) (Finset.mem_univ v))

/-- In the Section 5 choice `K=2d`, Golowich's one-sided cited bound suffices:
the lower bound and conversion to the two-sided norm are internal proofs. -/
theorem sectionFive_twoSided_of_upper (X : MeasuredComplex V) (d : ℕ)
    (hd : 2 ≤ d) (hX : X.dim = 2 * d) (F : Finset V)
    (hF : F.card + 1 = d)
    (hupper : (X.linkGraph F).UpperRayleighBound (1 / (d : ℝ))) :
    (X.linkGraph F).TwoSidedSpectralBound (1 / (d : ℝ)) := by
  have hrange : F.card + 1 ≤ X.dim := by omega
  apply WeightedGraph.twoSidedSpectralBound_of_rayleigh _
    (X.linkGraph_degree_pos F hrange) (by positivity) hupper
  have hlower := X.linkGraph_lowerRayleigh F hrange
  have hdim : X.dim - F.card = d + 1 := by omega
  rw [hdim] at hlower
  intro f
  have hrec : -(1 / (d : ℝ)) ≤ -1 / ((d + 1 : ℕ) : ℝ) := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hle : (1 : ℝ) / ((d : ℝ) + 1) ≤ 1 / (d : ℝ) :=
      one_div_le_one_div_of_le hdR (by linarith)
    push_cast
    rw [neg_div]
    linarith
  exact (mul_le_mul_of_nonneg_right hrec ((X.linkGraph F).sqNorm_nonneg f)).trans
    (hlower f)

end HDXLean.MeasuredComplex
