import HDXLean.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring

/-! The unnormalized marginal-weight identity added to Section 5.
All subsets and all face weights are literal finite sums. -/
namespace HDXLean.MeasuredComplex
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The induced weight formula, used below on sets of cardinality `d + 1`.
For such sets it vanishes when they belong to no top face. -/
noncomputable def skeletonWeight (X : MeasuredComplex V) (d : ℕ)
    (T : Finset V) : ℝ :=
  (Nat.choose (X.dim + 1) (d + 1) : ℝ)⁻¹ *
    ∑ σ ∈ X.topFaces, if T ⊆ σ then X.topWeight σ else 0

/-- Counting all `d`-faces containing a fixed small set `E` yields a common
binomial factor, independent of the particular vertices of `E`. -/
theorem skeletonWeight_superset_sum (X : MeasuredComplex V)
    (d : ℕ) (E : Finset V) (hE : E.card ≤ d + 1) :
    (∑ T ∈ (Finset.univ : Finset V).powersetCard (d + 1),
      if E ⊆ T then X.skeletonWeight d T else 0) =
    ((Nat.choose (X.dim + 1 - E.card) (d + 1 - E.card) : ℝ) /
      (Nat.choose (X.dim + 1) (d + 1) : ℝ)) *
      ∑ σ ∈ X.topFaces, if E ⊆ σ then X.topWeight σ else 0 := by
  classical
  let C : ℝ := (Nat.choose (X.dim + 1) (d + 1) : ℝ)⁻¹
  have hinner (σ : Finset V) (hσ : σ ∈ X.topFaces) :
      (∑ T ∈ (Finset.univ : Finset V).powersetCard (d + 1),
        if E ⊆ T ∧ T ⊆ σ then X.topWeight σ else 0) =
      (Nat.choose (X.dim + 1 - E.card) (d + 1 - E.card) : ℝ) *
        (if E ⊆ σ then X.topWeight σ else 0) := by
    by_cases hsub : E ⊆ σ
    · have hfilter :
          ((Finset.univ : Finset V).powersetCard (d + 1)).filter
            (fun T ↦ E ⊆ T ∧ T ⊆ σ) =
          (σ.powersetCard (d + 1)).filter (E ⊆ ·) := by
        ext T
        simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
          true_and]
        tauto
      rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul,
        Finset.card_filter_powersetCard_subset E σ (d + 1) hsub hE,
        X.top_card σ hσ, if_pos hsub]
    · have hnone (T : Finset V) : ¬(E ⊆ T ∧ T ⊆ σ) :=
        fun h ↦ hsub (h.1.trans h.2)
      simp [hnone, hsub]
  have hexpand (T : Finset V) :
      (if E ⊆ T then X.skeletonWeight d T else 0) =
        C * ∑ σ ∈ X.topFaces,
          if E ⊆ T ∧ T ⊆ σ then X.topWeight σ else 0 := by
    by_cases h : E ⊆ T <;> simp [skeletonWeight, C, h]
  simp_rw [hexpand]
  rw [← Finset.mul_sum, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun σ hσ ↦ hinner σ hσ)]
  rw [← Finset.mul_sum]
  dsimp [C]
  ring

/-- The coefficient in the manuscript is strictly positive in the stated
range, so normalization really does preserve the walk. -/
theorem skeletonLinkFactor_pos (X : MeasuredComplex V) (d t : ℕ)
    (hd : d ≤ X.dim) (ht : t + 2 ≤ d) :
    0 < (Nat.choose (X.dim - t - 2) (d - t - 2) : ℝ) /
      (Nat.choose (X.dim + 1) (d + 1) : ℝ) := by
  apply div_pos
  · exact_mod_cast (Nat.choose_pos (by omega : d - t - 2 ≤ X.dim - t - 2))
  · exact_mod_cast (Nat.choose_pos (by omega : d + 1 ≤ X.dim + 1))

/-- The exact displayed Section 5 formula, for a `t`-face and two distinct
vertices outside it.  The left side sums the induced top weights of all
`d`-faces containing the link edge. -/
theorem skeleton_link_edge_formula (X : MeasuredComplex V) (d t : ℕ)
    (F : Finset V) (hF : F.card = t + 1) (u v : V)
    (hu : u ∉ F) (hv : v ∉ F) (huv : u ≠ v) (ht : t + 2 ≤ d) :
    (∑ T ∈ (Finset.univ : Finset V).powersetCard (d + 1),
      if insert v (insert u F) ⊆ T then X.skeletonWeight d T else 0) =
    ((Nat.choose (X.dim - t - 2) (d - t - 2) : ℝ) /
      (Nat.choose (X.dim + 1) (d + 1) : ℝ)) *
      ∑ σ ∈ X.topFaces with insert v (insert u F) ⊆ σ, X.topWeight σ := by
  have hcard : (insert v (insert u F)).card = t + 3 := by
    simp [Finset.card_insert_of_notMem, hu, hv, Ne.symm huv, hF]
  have he := X.skeletonWeight_superset_sum d (insert v (insert u F)) (by omega)
  rw [hcard] at he
  have htop : X.dim + 1 - (t + 3) = X.dim - t - 2 := by omega
  have hdim : d + 1 - (t + 3) = d - t - 2 := by omega
  simpa only [htop, hdim, Finset.sum_filter] using he

end HDXLean.MeasuredComplex
