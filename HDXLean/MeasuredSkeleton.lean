import HDXLean.SkeletonWeights
import HDXLean.Relabeling
import HDXLean.WeightedGraphScaling

/-! The actual induced measured skeleton, with its native link graphs. -/
namespace HDXLean.MeasuredComplex
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem skeletonWeight_eq_zero_of_not_face (X : MeasuredComplex V) (d : ℕ)
    (T : Finset V) (hT : ¬ X.IsFace T) : X.skeletonWeight d T = 0 := by
  have hnone : ∀ σ ∈ X.topFaces, ¬ T ⊆ σ := fun σ hσ h ↦ hT ⟨σ, hσ, h⟩
  simp [skeletonWeight, Finset.sum_eq_zero (fun σ hσ ↦ if_neg (hnone σ hσ))]

theorem skeletonWeight_pos (X : MeasuredComplex V) (d : ℕ) (hd : d ≤ X.dim)
    (T : Finset V) (hT : X.IsFace T) : 0 < X.skeletonWeight d T := by
  obtain ⟨σ, hσ, hsub⟩ := hT
  apply mul_pos
  · exact inv_pos.mpr (by exact_mod_cast Nat.choose_pos (by omega : d + 1 ≤ X.dim + 1))
  · apply Finset.sum_pos'
    · intro τ hτ
      split_ifs <;> first | exact (X.topWeight_pos τ hτ).le | rfl
    · exact ⟨σ, hσ, by simpa [hsub] using X.topWeight_pos σ hσ⟩

noncomputable def skeletonTopFaces (X : MeasuredComplex V) (d : ℕ) : Finset (Finset V) := by
  classical
  exact (Finset.univ.powersetCard (d + 1)).filter X.IsFace

@[simp] theorem mem_skeletonTopFaces (X : MeasuredComplex V) (d : ℕ) (T : Finset V) :
    T ∈ X.skeletonTopFaces d ↔ T.card = d + 1 ∧ X.IsFace T := by
  classical
  simp [skeletonTopFaces]

theorem skeletonWeight_sum (X : MeasuredComplex V) (d : ℕ) (hd : d ≤ X.dim) :
    ∑ T ∈ X.skeletonTopFaces d, X.skeletonWeight d T = 1 := by
  classical
  have hchoose : (Nat.choose (X.dim + 1) (d + 1) : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast Nat.choose_pos (by omega : d + 1 ≤ X.dim + 1))
  have h := X.skeletonWeight_superset_sum d ∅ (by simp)
  simp only [Finset.card_empty, Nat.sub_zero, Finset.empty_subset, if_true,
    div_self hchoose, one_mul, X.topWeight_sum] at h
  rw [skeletonTopFaces, Finset.sum_filter]
  convert h using 1
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : X.IsFace T
  · simp [hT]
  · simp [hT, X.skeletonWeight_eq_zero_of_not_face d T hT]

/-- Induced top-face probability distribution; all purity, support, and
normalization obligations are proved rather than supplied as inputs. -/
noncomputable def skeleton (X : MeasuredComplex V) (d : ℕ) (hd : d ≤ X.dim) :
    MeasuredComplex V where
  dim := d
  topFaces := X.skeletonTopFaces d
  top_card T hT := ((X.mem_skeletonTopFaces d T).mp hT).1
  topWeight T := if T ∈ X.skeletonTopFaces d then X.skeletonWeight d T else 0
  topWeight_pos T hT := by
    simp only [hT, if_true]
    exact X.skeletonWeight_pos d hd T ((X.mem_skeletonTopFaces d T).mp hT).2
  topWeight_zero T hT := if_neg hT
  topWeight_sum := by
    convert X.skeletonWeight_sum d hd using 1
    exact Finset.sum_congr rfl (fun T hT ↦ if_pos hT)

@[simp] theorem skeleton_dim (X : MeasuredComplex V) (d : ℕ) (hd : d ≤ X.dim) :
    (X.skeleton d hd).dim = d := rfl

theorem skeleton_isFace_iff (X : MeasuredComplex V) (d : ℕ) (hd : d ≤ X.dim)
    (F : Finset V) : (X.skeleton d hd).IsFace F ↔ X.IsFace F ∧ F.card ≤ d + 1 := by
  constructor
  · rintro ⟨T, hT, hFT⟩
    obtain ⟨hc, hf⟩ := (X.mem_skeletonTopFaces d T).mp hT
    exact ⟨X.isFace_mono hf hFT, hc ▸ Finset.card_le_card hFT⟩
  · rintro ⟨⟨T, hT, hFT⟩, hc⟩
    obtain ⟨S, hFS, hST, hS⟩ := Finset.exists_subsuperset_card_eq hFT hc
      (show d + 1 ≤ T.card by rw [X.top_card T hT]; omega)
    exact ⟨S, (X.mem_skeletonTopFaces d S).mpr ⟨hS, ⟨T, hT, hST⟩⟩, hFS⟩

/-- Below the skeleton cutoff, link vertices are literally the same vertices. -/
noncomputable def skeletonLinkEquiv (X : MeasuredComplex V) (d : ℕ)
    (hd : d ≤ X.dim) (F : Finset V) (hF : F.card ≤ d) :
    (X.skeleton d hd).LinkVertex F ≃ X.LinkVertex F where
  toFun u := ⟨u.1, u.2.1, ((X.skeleton_isFace_iff d hd _).mp u.2.2).1⟩
  invFun u := ⟨u.1, u.2.1, (X.skeleton_isFace_iff d hd _).mpr
    ⟨u.2.2, by rw [Finset.card_insert_of_notMem u.2.1]; omega⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem skeleton_superset_sum (X : MeasuredComplex V) (d : ℕ) (hd : d ≤ X.dim)
    (E : Finset V) (hE : E.card ≤ d + 1) :
    (∑ T ∈ (X.skeleton d hd).topFaces with E ⊆ T, (X.skeleton d hd).topWeight T) =
    ((Nat.choose (X.dim + 1 - E.card) (d + 1 - E.card) : ℝ) /
      Nat.choose (X.dim + 1) (d + 1)) *
      ∑ σ ∈ X.topFaces with E ⊆ σ, X.topWeight σ := by
  classical
  rw [Finset.sum_filter]
  have hw : ∀ T ∈ X.skeletonTopFaces d,
      (X.skeleton d hd).topWeight T = X.skeletonWeight d T :=
    fun T hT ↦ if_pos hT
  rw [Finset.sum_congr rfl (fun T hT ↦ by rw [hw T hT])]
  change (∑ T ∈ X.skeletonTopFaces d, if E ⊆ T then X.skeletonWeight d T else 0) = _
  rw [skeletonTopFaces, Finset.sum_filter]
  have heq : ∀ T : Finset V,
      (if X.IsFace T then (if E ⊆ T then X.skeletonWeight d T else 0) else 0) =
      (if E ⊆ T then X.skeletonWeight d T else 0) := by
    intro T
    by_cases hT : X.IsFace T
    · simp [hT]
    · simp [hT, X.skeletonWeight_eq_zero_of_not_face d T hT]
  simp_rw [heq]
  simpa only [Finset.sum_filter] using X.skeletonWeight_superset_sum d E hE

/-- A single formula covering the empty link as well as all nonempty links. -/
noncomputable def skeletonLinkScale (X : MeasuredComplex V) (d : ℕ) (F : Finset V) : ℝ :=
  (Nat.choose (X.dim + 1 - (F.card + 2)) (d + 1 - (F.card + 2)) : ℝ) /
    Nat.choose (X.dim + 1) (d + 1)

theorem skeletonLinkScale_pos (X : MeasuredComplex V) (d : ℕ) (hd : d ≤ X.dim)
    (F : Finset V) (hF : F.card + 1 ≤ d) : 0 < X.skeletonLinkScale d F := by
  apply div_pos
  · exact_mod_cast Nat.choose_pos (by omega : d + 1 - (F.card + 2) ≤ X.dim + 1 - (F.card + 2))
  · exact_mod_cast Nat.choose_pos (by omega : d + 1 ≤ X.dim + 1)

theorem skeleton_linkGraph_eq (X : MeasuredComplex V) (d : ℕ) (hd : d ≤ X.dim)
    (F : Finset V) (hF : F.card + 1 ≤ d) :
    (X.skeleton d hd).linkGraph F =
      ((X.linkGraph F).relabel (X.skeletonLinkEquiv d hd F (by omega)).symm).scale
        (X.skeletonLinkScale d F) (X.skeletonLinkScale_pos d hd F hF).le := by
  classical
  apply WeightedGraph.ext_weight
  intro u v
  by_cases huv : u = v
  · subst v
    simp [WeightedGraph.scale, WeightedGraph.relabel, WeightedGraph.weight_self]
  · have he : (X.skeletonLinkEquiv d hd F (by omega)) u ≠
        (X.skeletonLinkEquiv d hd F (by omega)) v :=
        fun h ↦ huv ((X.skeletonLinkEquiv d hd F (by omega)).injective h)
    have hval : v.1 ≠ u.1 := fun h ↦ huv (Subtype.ext h.symm)
    have hc : (insert v.1 (insert u.1 F)).card = F.card + 2 := by
      simp [Finset.card_insert_of_notMem, u.2.1, v.2.1, hval]
    change (if u = v then 0 else _) =
      X.skeletonLinkScale d F * (if _ = _ then 0 else _)
    rw [Equiv.symm_symm, if_neg huv, if_neg he]
    change (∑ T ∈ (X.skeleton d hd).topFaces with insert v.1 (insert u.1 F) ⊆ T,
      (X.skeleton d hd).topWeight T) = X.skeletonLinkScale d F *
      ∑ T ∈ X.topFaces with insert v.1 (insert u.1 F) ⊆ T, X.topWeight T
    have h := X.skeleton_superset_sum d hd (insert v.1 (insert u.1 F)) (by omega)
    simpa only [hc, skeletonLinkScale] using h

theorem skeleton_link_connected (X : MeasuredComplex V) (d : ℕ) (hd : d ≤ X.dim)
    (F : Finset V) (hF : F.card + 1 ≤ d) (hc : (X.linkGraph F).Connected) :
    ((X.skeleton d hd).linkGraph F).Connected := by
  rw [X.skeleton_linkGraph_eq d hd F hF]
  exact WeightedGraph.connected_scale _ _ (X.skeletonLinkScale_pos d hd F hF)
    (WeightedGraph.connected_relabel _ _ hc)

theorem skeleton_link_bound (X : MeasuredComplex V) (d : ℕ) (hd : d ≤ X.dim)
    (F : Finset V) (hF : F.card + 1 ≤ d) {a : ℝ}
    (hb : (X.linkGraph F).TwoSidedSpectralBound a) :
    ((X.skeleton d hd).linkGraph F).TwoSidedSpectralBound a := by
  rw [X.skeleton_linkGraph_eq d hd F hF]
  exact WeightedGraph.twoSidedSpectralBound_scale _ _ (X.skeletonLinkScale_pos d hd F hF)
    (WeightedGraph.twoSidedSpectralBound_relabel _ _ hb)

end HDXLean.MeasuredComplex
