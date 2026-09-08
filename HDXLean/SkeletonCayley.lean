import HDXLean.MeasuredSkeleton

namespace HDXLean
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]

omit [Fintype V] in
theorem translateFace_card (g : V) (T : Finset V) :
    (translateFace g T).card = T.card := by
  exact Finset.card_image_of_injective _ (add_right_injective g)

omit [Fintype V] in
theorem translateFace_subset_iff (g : V) (S T : Finset V) :
    translateFace g S ⊆ translateFace g T ↔ S ⊆ T :=
  Finset.image_subset_image_iff (add_right_injective g)

omit [Fintype V] in
theorem translateFace_neg_cancel (g : V) (T : Finset V) :
    translateFace g (translateFace (-g) T) = T := by
  ext x
  simp [mem_translateFace_iff, sub_eq_add_neg, add_assoc]

namespace MeasuredComplex

theorem isFace_translate_iff (X : MeasuredComplex V) (hX : TranslationInvariant X)
    (g : V) (T : Finset V) : X.IsFace (translateFace g T) ↔ X.IsFace T := by
  constructor
  · rintro ⟨σ, hσ, hTσ⟩
    refine ⟨translateFace (-g) σ, (hX (-g) σ).1.mpr hσ, ?_⟩
    have h := (translateFace_subset_iff (-g) _ _).mpr hTσ
    have hc : translateFace (-g) (translateFace g T) = T := by
      simpa only [neg_neg] using translateFace_neg_cancel (-g) T
    rwa [hc] at h
  · rintro ⟨σ, hσ, hTσ⟩
    exact ⟨translateFace g σ, (hX g σ).1.mpr hσ,
      (translateFace_subset_iff g T σ).mpr hTσ⟩

theorem skeletonWeight_translate (X : MeasuredComplex V) (hX : TranslationInvariant X)
    (d : ℕ) (g : V) (T : Finset V) :
    X.skeletonWeight d (translateFace g T) = X.skeletonWeight d T := by
  classical
  unfold skeletonWeight
  congr 1
  apply Finset.sum_bij (fun σ _ ↦ translateFace (-g) σ)
  · intro σ hσ
    exact (hX (-g) σ).1.mpr hσ
  · intro σ _ τ _ h
    have := congrArg (translateFace g) h
    simpa only [translateFace_neg_cancel] using this
  · intro τ hτ
    refine ⟨translateFace g τ, (hX g τ).1.mpr hτ, ?_⟩
    simpa using translateFace_neg_cancel (-g) τ
  · intro σ _
    have hsub : translateFace g T ⊆ σ ↔ T ⊆ translateFace (-g) σ := by
      conv_lhs => rhs; rw [← translateFace_neg_cancel g σ]
      exact translateFace_subset_iff g T (translateFace (-g) σ)
    simp only [hsub, (hX (-g) σ).2]

theorem skeleton_translationInvariant (X : MeasuredComplex V)
    (hX : TranslationInvariant X) (d : ℕ) (hd : d ≤ X.dim) :
    TranslationInvariant (X.skeleton d hd) := by
  intro g T
  have hmem : translateFace g T ∈ X.skeletonTopFaces d ↔ T ∈ X.skeletonTopFaces d := by
    simp only [mem_skeletonTopFaces, translateFace_card, X.isFace_translate_iff hX]
  refine ⟨hmem, ?_⟩
  change (if translateFace g T ∈ X.skeletonTopFaces d then _ else 0) =
    (if T ∈ X.skeletonTopFaces d then _ else 0)
  simp only [hmem, X.skeletonWeight_translate hX]

end MeasuredComplex

/-- Cayley generators and their degree are preserved by any skeleton of
positive dimension; its translation-invariant probability measure is proved. -/
noncomputable def CayleyComplex.skeleton (C : CayleyComplex (V := V))
    (d : ℕ) (hd : d ≤ C.complex.dim) (hdpos : 1 ≤ d) : CayleyComplex (V := V) where
  complex := C.complex.skeleton d hd
  translationInvariant := C.complex.skeleton_translationInvariant C.translationInvariant d hd
  cayley :=
    { generators := C.cayley.generators
      zero_not_mem := C.cayley.zero_not_mem
      neg_mem_iff := C.cayley.neg_mem_iff
      edge_iff := by
        intro x y
        rw [C.complex.skeleton_isFace_iff, C.cayley.edge_iff]
        have hc : ({x, y} : Finset V).card ≤ d + 1 :=
          (Finset.card_insert_le x {y}).trans (by simp; omega)
        simp only [hc, and_true] }

@[simp] theorem CayleyComplex.skeleton_degree (C : CayleyComplex (V := V))
    (d : ℕ) (hd : d ≤ C.complex.dim) (hdpos : 1 ≤ d) :
    (C.skeleton d hd hdpos).cayley.degree = C.cayley.degree := rfl

end HDXLean
