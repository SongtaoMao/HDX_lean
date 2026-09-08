import HDXLean.WeightedLiftCayley

/-!
# Translation invariance of the weighted lift

This file proves that the set of lifted top faces and the full pushforward
measure (including sums over duplicate compatible parents) are invariant
under translation by the product group.
-/

namespace HDXLean

open scoped BigOperators

namespace WeightedLift

variable {Gamma A : Type*}
  [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma] [DecidableEq Gamma]
  [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A]

omit [Module F₂ Gamma] [Module F₂ A] [Fintype Gamma] [Fintype A] in
theorem translateFace_card (z : Gamma × A) (T : Finset (Gamma × A)) :
    (translateFace z T).card = T.card := by
  unfold translateFace
  rw [Finset.card_image_of_injective]
  intro x y hxy
  exact add_left_cancel hxy

omit [Module F₂ Gamma] [Module F₂ A] [Fintype Gamma] [Fintype A] in
theorem translateBaseFace_card (g : Gamma) (tau : Finset Gamma) :
    (translateFace g tau).card = tau.card := by
  unfold translateFace
  rw [Finset.card_image_of_injective]
  intro x y hxy
  exact add_left_cancel hxy

omit [Module F₂ Gamma] [Module F₂ A] [Fintype Gamma] [Fintype A] in
theorem translateBaseFace_add (g h : Gamma) (tau : Finset Gamma) :
    translateFace g (translateFace h tau) =
      translateFace (g + h) tau := by
  classical
  ext x
  simp only [mem_translateFace_iff]
  constructor <;> intro hx
  · simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx
  · simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx

omit [Module F₂ Gamma] [Module F₂ A] [Fintype Gamma] [Fintype A] in
@[simp]
theorem translateBaseFace_zero (tau : Finset Gamma) :
    translateFace 0 tau = tau := by
  classical
  ext x
  simp [mem_translateFace_iff]

omit [Module F₂ Gamma] [Module F₂ A] [Fintype Gamma] [Fintype A] in
@[simp]
theorem translateBaseFace_neg (g : Gamma) (tau : Finset Gamma) :
    translateFace (-g) (translateFace g tau) = tau := by
  rw [translateBaseFace_add, neg_add_cancel, translateBaseFace_zero]

omit [Module F₂ Gamma] [Module F₂ A] [Fintype Gamma] [Fintype A] in
theorem translateFace_add (z w : Gamma × A) (T : Finset (Gamma × A)) :
    translateFace z (translateFace w T) =
      translateFace (z + w) T := by
  classical
  ext x
  simp only [mem_translateFace_iff]
  constructor <;> intro hx
  · simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx
  · simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx

omit [Module F₂ Gamma] [Module F₂ A] [Fintype Gamma] [Fintype A] in
@[simp]
theorem translateFace_zero (T : Finset (Gamma × A)) :
    translateFace 0 T = T := by
  classical
  ext x
  simp

omit [Module F₂ Gamma] [Module F₂ A] [Fintype Gamma] [Fintype A] in
@[simp]
theorem translateFace_neg (z : Gamma × A) (T : Finset (Gamma × A)) :
    translateFace (-z) (translateFace z T) = T := by
  rw [translateFace_add, neg_add_cancel, translateFace_zero]

omit [Module F₂ Gamma] [Module F₂ A] [Fintype Gamma] in
/-- Translation maps the fibers over `tau` onto the fibers over the translated
base face. -/
theorem translate_fibersAbove (g : Gamma) (a : A) (tau : Finset Gamma) :
    translateFace (g, a) (fibersAbove (A := A) tau) =
      fibersAbove (A := A) (translateFace g tau) := by
  classical
  ext z
  simp [mem_translateFace_iff, mem_fibersAbove]

omit [Module F₂ Gamma] [Module F₂ A] [Fintype Gamma] in
/-- Compatibility with a parent is preserved by simultaneous translation. -/
theorem compatible_translate_iff (g : Gamma) (a : A)
    (tau : Finset Gamma) (T : Finset (Gamma × A)) :
    CompatibleParent (A := A) (translateFace g tau)
        (translateFace (g, a) T) ↔
      CompatibleParent (A := A) tau T := by
  constructor
  · intro h z hz
    have hzTranslated : (g, a) + z ∈
        translateFace (g, a) T := by
      apply Finset.mem_image.mpr
      exact ⟨z, hz, rfl⟩
    have hmem := mem_fibersAbove.mp (h hzTranslated)
    have : z.1 ∈ tau := by
      have := mem_translateFace_iff g (g + z.1) tau |>.mp hmem
      simpa using this
    exact mem_fibersAbove.mpr this
  · intro h z hz
    have hzBack : z - (g, a) ∈ T :=
      (mem_translateFace_iff (g, a) z T).mp hz
    have hbase : (z - (g, a)).1 ∈ tau :=
      mem_fibersAbove.mp (h hzBack)
    apply mem_fibersAbove.mpr
    apply (mem_translateFace_iff g z.1 tau).mpr
    simpa using hbase

omit [Module F₂ Gamma] [Module F₂ A] in
/-- The lifted top-face set is translation invariant. -/
theorem topFaces_translate_iff (base : CayleyComplex (V := Gamma))
    (d : ℕ) (g : Gamma) (a : A) (T : Finset (Gamma × A)) :
    translateFace (g, a) T ∈ topFaces (A := A) base.complex d ↔
      T ∈ topFaces (A := A) base.complex d := by
  constructor
  · intro htranslated
    obtain ⟨hcard, sigma, hsigma, hcompatible⟩ :=
      mem_topFaces.mp htranslated
    let tau := translateFace (-g) sigma
    have htau : tau ∈ base.complex.topFaces :=
      (base.translationInvariant (-g) sigma).1.mpr hsigma
    have hTcard : T.card = d + 1 := by
      rw [← translateFace_card (g, a) T]
      exact hcard
    have hTcompatible : CompatibleParent (A := A) tau T := by
      intro z hz
      have hzTranslated : (g, a) + z ∈
          translateFace (g, a) T := by
        apply Finset.mem_image.mpr
        exact ⟨z, hz, rfl⟩
      have hbase := mem_fibersAbove.mp (hcompatible hzTranslated)
      apply mem_fibersAbove.mpr
      apply (mem_translateFace_iff (-g) z.1 sigma).mpr
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hbase
    exact mem_topFaces.mpr ⟨hTcard, tau, htau, hTcompatible⟩
  · intro hT
    obtain ⟨hcard, tau, htau, hcompatible⟩ := mem_topFaces.mp hT
    refine mem_topFaces.mpr ⟨?_, translateFace g tau,
      (base.translationInvariant g tau).1.mpr htau, ?_⟩
    · rw [translateFace_card]
      exact hcard
    · exact (compatible_translate_iff g a tau T).2 hcompatible

/-- The section of a lifted set inside one fiber. -/
def fiberSection (T : Finset (Gamma × A)) (x : Gamma) : Finset A :=
  Finset.univ.filter fun b ↦ (x, b) ∈ T

omit [Fintype Gamma] [Module F₂ Gamma] [Module F₂ A]
    [AddCommGroup Gamma] [AddCommGroup A] in
theorem occupancy_eq_card_fiberSection (T : Finset (Gamma × A)) (x : Gamma) :
    occupancy T x = (fiberSection T x).card :=
  rfl

omit [Fintype Gamma] [Module F₂ Gamma] [Module F₂ A] in
/-- Fiber sections are carried bijectively to fiber sections by translation. -/
theorem fiberSection_translate (g : Gamma) (a : A)
    (T : Finset (Gamma × A)) (x : Gamma) :
    fiberSection (translateFace (g, a) T) (g + x) =
      (fiberSection T x).image fun b ↦ a + b := by
  classical
  ext b
  simp only [fiberSection, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · intro hb
    refine ⟨b - a, ?_, ?_⟩
    · have := (mem_translateFace_iff (g, a) (g + x, b) T).mp hb
      simpa using this
    · simp
  · rintro ⟨c, hc, rfl⟩
    apply (mem_translateFace_iff (g, a) (g + x, a + c) T).mpr
    simpa

omit [Fintype Gamma] [Module F₂ Gamma] [Module F₂ A] in
/-- Occupancy is invariant after translating both the lifted set and its base
fiber. -/
theorem occupancy_translate (g : Gamma) (a : A)
    (T : Finset (Gamma × A)) (x : Gamma) :
    occupancy (translateFace (g, a) T) (g + x) =
      occupancy T x := by
  rw [occupancy_eq_card_fiberSection, occupancy_eq_card_fiberSection,
    fiberSection_translate, Finset.card_image_of_injective]
  intro b c hbc
  exact add_left_cancel hbc

omit [Module F₂ Gamma] [Module F₂ A] [Fintype Gamma] in
/-- The occupied support is translated bijectively with the base face. -/
theorem occupiedSupport_translate (g : Gamma) (a : A)
    (tau : Finset Gamma) (T : Finset (Gamma × A)) :
    occupiedSupport (A := A) (translateFace g tau)
        (translateFace (g, a) T) =
      translateFace g (occupiedSupport (A := A) tau T) := by
  classical
  ext y
  rw [mem_occupiedSupport]
  rw [mem_translateFace_iff g y tau,
    mem_translateFace_iff g y (occupiedSupport (A := A) tau T)]
  rw [mem_occupiedSupport]
  constructor
  · rintro ⟨hy, b, hb⟩
    refine ⟨hy, b - a, ?_⟩
    exact (mem_translateFace_iff (g, a) (y, b) T).mp hb
  · rintro ⟨hy, b, hb⟩
    refine ⟨hy, a + b, ?_⟩
    apply (mem_translateFace_iff (g, a) (y, a + b) T).mpr
    simpa using hb

omit [Module F₂ Gamma] [Module F₂ A] [Fintype Gamma] in
/-- The product of the fiber factors in (5.1) is unchanged by translation. -/
theorem occupancyProduct_translate (g : Gamma) (a : A)
    (tau : Finset Gamma) (T : Finset (Gamma × A)) :
    (∏ y ∈ occupiedSupport (A := A) (translateFace g tau)
          (translateFace (g, a) T),
        WeightedLift.g (Fintype.card A)
          (occupancy (translateFace (g, a) T) y)) =
      ∏ x ∈ occupiedSupport (A := A) tau T,
        WeightedLift.g (Fintype.card A) (occupancy T x) := by
  classical
  rw [occupiedSupport_translate]
  change
    (∏ y ∈ (occupiedSupport (A := A) tau T).image (fun x ↦ g + x),
        WeightedLift.g (Fintype.card A)
          (occupancy (translateFace (g, a) T) y)) = _
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro x _hx
    exact congrArg (WeightedLift.g (Fintype.card A))
      (occupancy_translate g a T x)
  · intro x _hx y _hy hxy
    exact add_left_cancel hxy

omit [Module F₂ Gamma] [Module F₂ A] in
/-- Every individual summand in equation (5.1) is translation invariant. -/
theorem parentWeight_translate (base : CayleyComplex (V := Gamma))
    (d : ℕ) (g : Gamma) (a : A)
    (tau : Finset Gamma) (T : Finset (Gamma × A)) :
    parentWeight (A := A) base.complex d (translateFace g tau)
        (translateFace (g, a) T) =
      parentWeight (A := A) base.complex d tau T := by
  unfold parentWeight
  rw [(base.translationInvariant g tau).2,
    occupancyProduct_translate, occupiedSupport_translate,
    translateBaseFace_card]

omit [Module F₂ Gamma] [Module F₂ A] in
/-- The entire unnormalized sum in equation (5.1), including duplicate
parents, is invariant under translation. -/
theorem rawTopWeight_translate (base : CayleyComplex (V := Gamma))
    (d : ℕ) (g : Gamma) (a : A) (T : Finset (Gamma × A)) :
    rawTopWeight (A := A) base.complex d (translateFace (g, a) T) =
      rawTopWeight (A := A) base.complex d T := by
  classical
  unfold rawTopWeight
  symm
  apply Finset.sum_bij (fun tau _htau ↦ translateFace g tau)
  · intro tau htau
    exact (base.translationInvariant g tau).1.mpr htau
  · intro tau₁ _h₁ tau₂ _h₂ heq
    have hback := congrArg (translateFace (-g)) heq
    simpa using hback
  · intro sigma hsigma
    refine ⟨translateFace (-g) sigma,
      (base.translationInvariant (-g) sigma).1.mpr hsigma, ?_⟩
    rw [translateBaseFace_add, add_neg_cancel, translateBaseFace_zero]
  · intro tau _htau
    by_cases hcompatible : CompatibleParent (A := A) tau T
    · rw [if_pos hcompatible,
        if_pos ((compatible_translate_iff g a tau T).2 hcompatible),
        parentWeight_translate]
    · rw [if_neg hcompatible,
        if_neg (fun htranslated ↦ hcompatible
          ((compatible_translate_iff g a tau T).1 htranslated))]

omit [Module F₂ Gamma] [Module F₂ A] in
/-- The normalized top-face measure of the lift is translation invariant. -/
theorem liftedTopWeight_translate (base : CayleyComplex (V := Gamma))
    (d : ℕ) (g : Gamma) (a : A) (T : Finset (Gamma × A)) :
    liftedTopWeight (A := A) base.complex d (translateFace (g, a) T) =
      liftedTopWeight (A := A) base.complex d T := by
  by_cases hT : T ∈ topFaces (A := A) base.complex d
  · have htranslated : translateFace (g, a) T ∈
        topFaces (A := A) base.complex d :=
      (topFaces_translate_iff base d g a T).2 hT
    simp only [liftedTopWeight, hT, htranslated, if_true]
    rw [rawTopWeight_translate]
  · have htranslated : translateFace (g, a) T ∉
        topFaces (A := A) base.complex d := by
      intro htranslated
      exact hT ((topFaces_translate_iff base d g a T).1 htranslated)
    simp [liftedTopWeight, hT, htranslated]

omit [Module F₂ Gamma] [Module F₂ A] in
/-- Both the lifted top-face set and the exact pushforward measure in (5.1)
are invariant under the product-group action. -/
theorem measuredComplex_translationInvariant
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) :
    TranslationInvariant
      (measuredComplex (A := A) base.complex d hdimension hd hm) := by
  rintro ⟨g, a⟩ T
  exact ⟨topFaces_translate_iff base d g a T,
    liftedTopWeight_translate base d g a T⟩

/-- The full weighted lift, now packaged as a measured Cayley complex. -/
noncomputable def cayleyComplex
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) : CayleyComplex (V := Gamma × A) where
  complex := measuredComplex (A := A) base.complex d hdimension hd hm
  cayley := cayleyPresentation (A := A) base d hdimension hd hm
  translationInvariant :=
    measuredComplex_translationInvariant base d hdimension hd hm

end WeightedLift

end HDXLean
