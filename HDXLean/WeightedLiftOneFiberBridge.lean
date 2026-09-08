import HDXLean.WeightedLiftOneFiberSpectrum
import HDXLean.WeightedLiftOccupancy
import HDXLean.ConditionedLinkWeights
import HDXLean.WeightedLiftParentSums
import HDXLean.WeightedLiftInsertion
import HDXLean.VertexLinkMass
import HDXLean.WeightedLiftCodimensionTwo

/-!
# Concrete bridge for the one-fiber conditioned link

This module enumerates the vertices of an actual codimension-two lifted link
whose conditioned face lies in one base fiber.  It then packages an exact
common-factor edge calculation as a `OneFiberLinkCertificate`, so the direct
weighted `L²` estimate in `WeightedLiftOneFiberSpectrum` applies verbatim.
-/

namespace HDXLean

open scoped BigOperators

namespace WeightedLift

variable {Gamma A : Type*}
  [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma] [DecidableEq Gamma]
  [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A]

omit [AddCommGroup Gamma] [Module F₂ Gamma]
    [AddCommGroup A] [Module F₂ A] in
/-- Compatibility with a base parent depends only on projection support. -/
theorem compatibleParent_iff_projectionSupport_subset
    (tau : Finset Gamma) (E : Finset (Gamma × A)) :
    CompatibleParent (A := A) tau E ↔ projectionSupport E ⊆ tau := by
  constructor
  · exact projectionSupport_subset_of_compatible
  · intro hsubset z hz
    exact mem_fibersAbove.mpr
      (hsubset (mem_projectionSupport.mpr ⟨z.2, hz⟩))

/-- Total base-triangle mass of the parents containing a prescribed support. -/
noncomputable def compatibleParentMass (X : MeasuredComplex Gamma)
    (S : Finset Gamma) : ℝ :=
  ∑ tau ∈ X.topFaces, if S ⊆ tau then X.topWeight tau else 0

omit [AddCommGroup Gamma] [Module F₂ Gamma]
    [AddCommGroup A] [Module F₂ A] in
/-- Equation (5.1) factors into its support correction, its occupancy product,
and the total mass of compatible base parents. -/
theorem rawTopWeight_eq_gamma_mul_gProduct_mul_compatibleParentMass
    (X : MeasuredComplex Gamma) (d : ℕ) (E : Finset (Gamma × A)) :
    rawTopWeight (A := A) X d E =
      gamma d (projectionSupport E).card *
        (∏ x ∈ projectionSupport E,
          g (Fintype.card A) (occupancy E x)) *
        compatibleParentMass X (projectionSupport E) := by
  classical
  unfold rawTopWeight
  calc
    (∑ tau ∈ X.topFaces,
        if CompatibleParent (A := A) tau E then
          parentWeight (A := A) X d tau E else 0) =
      ∑ tau ∈ X.topFaces,
        if projectionSupport E ⊆ tau then
          X.topWeight tau * gamma d (projectionSupport E).card *
            ∏ x ∈ projectionSupport E,
              g (Fintype.card A) (occupancy E x)
        else 0 := by
          apply Finset.sum_congr rfl
          intro tau htau
          by_cases hcompatible : CompatibleParent (A := A) tau E
          · have hsubset : projectionSupport E ⊆ tau :=
              (compatibleParent_iff_projectionSupport_subset
                (A := A) tau E).mp hcompatible
            rw [if_pos hcompatible, if_pos hsubset]
            unfold parentWeight
            rw [occupiedSupport_eq_projectionSupport hcompatible]
          · have hsubset : ¬ projectionSupport E ⊆ tau := by
              exact fun h ↦ hcompatible
                ((compatibleParent_iff_projectionSupport_subset
                  (A := A) tau E).mpr h)
            rw [if_neg hcompatible, if_neg hsubset]
    _ = gamma d (projectionSupport E).card *
        (∏ x ∈ projectionSupport E,
          g (Fintype.card A) (occupancy E x)) *
        compatibleParentMass X (projectionSupport E) := by
          unfold compatibleParentMass
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro tau _htau
          split_ifs <;> ring

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Adjoining two distinct link vertices to a codimension-two face gives a
set of top cardinality. -/
theorem codimensionTwo_enlarged_card
    {X : MeasuredComplex (Gamma × A)} {F : Finset (Gamma × A)}
    (hFcard : F.card + 1 = X.dim) (u v : X.LinkVertex F) (huv : u ≠ v) :
    (insert v.1 (insert u.1 F)).card = X.dim + 1 := by
  have huvValue : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
  have hvnot : v.1 ∉ insert u.1 F := by
    simp [v.2.1, Ne.symm huvValue]
  rw [Finset.card_insert_of_notMem hvnot,
    Finset.card_insert_of_notMem u.2.1, hFcard]

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- On a set already having lifted top-face cardinality, the defining
piecewise top weight is always `rawTopWeight / normalizer`: off the top-face
set there cannot be any compatible parent, so the raw sum is zero. -/
theorem liftedTopWeight_eq_raw_div_of_card
    (X : MeasuredComplex Gamma) (d : ℕ) (E : Finset (Gamma × A))
    (hcard : E.card = d + 1) :
    liftedTopWeight (A := A) X d E =
      rawTopWeight (A := A) X d E / normalizer (A := A) X d := by
  classical
  by_cases htop : E ∈ topFaces (A := A) X d
  · exact liftedTopWeight_eq X d htop
  · have hraw : rawTopWeight (A := A) X d E = 0 := by
      unfold rawTopWeight
      apply Finset.sum_eq_zero
      intro tau htau
      rw [if_neg]
      intro hcompatible
      exact htop (mem_topFaces.mpr ⟨hcard, tau, htau, hcompatible⟩)
    simp [liftedTopWeight, htop, hraw]

/-- Every distinct edge of the actual codimension-two link admits a uniform
factorized form.  The remaining case analysis only has to simplify the
support, occupancies, and compatible-parent mass. -/
theorem concreteOneFiberLink_weight_factorized
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hFcard : F.card + 1 = d)
    (u v : (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex F)
    (huv : u ≠ v) :
    ((measuredComplex (A := A) base.complex d hdimension hd hm).linkGraph F).weight u v =
      (gamma d (projectionSupport (insert v.1 (insert u.1 F))).card *
          (∏ x ∈ projectionSupport (insert v.1 (insert u.1 F)),
            g (Fintype.card A)
              (occupancy (insert v.1 (insert u.1 F)) x)) *
          compatibleParentMass base.complex
            (projectionSupport (insert v.1 (insert u.1 F)))) /
        normalizer (A := A) base.complex d := by
  change MeasuredComplex.linkEdgeWeight
    (measuredComplex (A := A) base.complex d hdimension hd hm) F u v = _
  rw [MeasuredComplex.codimensionTwo_linkEdgeWeight_eq_topWeight _ F
    hFcard u v huv]
  change liftedTopWeight (A := A) base.complex d
    (insert v.1 (insert u.1 F)) = _
  have hcard := codimensionTwo_enlarged_card hFcard u v huv
  change (insert v.1 (insert u.1 F)).card = d + 1 at hcard
  rw [liftedTopWeight_eq_raw_div_of_card base.complex d _ hcard]
  rw [rawTopWeight_eq_gamma_mul_gProduct_mul_compatibleParentMass]

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- For two distinct base-link vertices, compatible-parent mass is exactly
their base-link edge weight. -/
theorem compatibleParentMass_three_eq_baseLink_weight
    (X : MeasuredComplex Gamma) (x : Gamma)
    (b c : X.LinkVertex {x}) (hbc : b ≠ c) :
    compatibleParentMass X (insert c.1 (insert b.1 {x})) =
      (X.linkGraph {x}).weight b c := by
  classical
  change compatibleParentMass X (insert c.1 (insert b.1 {x})) =
    X.linkEdgeWeight {x} b c
  unfold compatibleParentMass MeasuredComplex.linkEdgeWeight
  rw [if_neg hbc]
  rw [Finset.sum_filter]

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Compatible-parent mass through a base edge is the degree of the
corresponding vertex in the base vertex link. -/
theorem compatibleParentMass_pair_eq_baseLink_degree
    (X : MeasuredComplex Gamma) (hdimension : X.dim = 2) (x : Gamma)
    (b : X.LinkVertex {x}) :
    compatibleParentMass X (insert b.1 {x}) =
      (X.linkGraph {x}).degree b := by
  rw [MeasuredComplex.vertexLink_degree_eq_topWeight_sum X hdimension x b]
  unfold compatibleParentMass
  rw [Finset.sum_filter]

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Compatible-parent mass through the occupied point is half the total
weighted volume of its base vertex link. -/
theorem compatibleParentMass_singleton_eq_half_graphVolume
    (X : MeasuredComplex Gamma) (hdimension : X.dim = 2) (x : Gamma) :
    compatibleParentMass X {x} =
      graphVolume (X.linkGraph {x}) / 2 := by
  have hvolume :=
    MeasuredComplex.vertexLink_graphVolume_eq_two_mul_topWeight_sum
      X hdimension x
  unfold compatibleParentMass
  simp only [Finset.singleton_subset_iff]
  rw [← Finset.sum_filter]
  linarith

/-- The unused labels over the unique occupied base point. -/
def OneFiberRemainingLabel (F : Finset (Gamma × A)) (x : Gamma) :=
  {a : A // (x, a) ∉ F}

noncomputable instance (F : Finset (Gamma × A)) (x : Gamma) :
    Fintype (OneFiberRemainingLabel F x) := by
  letI : Finite (OneFiberRemainingLabel F x) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance (F : Finset (Gamma × A)) (x : Gamma) :
    DecidableEq (OneFiberRemainingLabel F x) := Classical.decEq _

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Every point of a lifted face with singleton projection support lies over
that single base point. -/
theorem fst_eq_of_mem_of_projectionSupport_eq_singleton
    {F : Finset (Gamma × A)} {x : Gamma}
    (hsupport : projectionSupport F = {x}) {z : Gamma × A} (hz : z ∈ F) :
    z.1 = x := by
  have hzSupport : z.1 ∈ projectionSupport F :=
    mem_projectionSupport.mpr ⟨z.2, hz⟩
  rw [hsupport] at hzSupport
  simpa using hzSupport

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- The unique occupied fiber contains every vertex of the conditioned face. -/
theorem occupancy_eq_card_of_projectionSupport_eq_singleton
    (F : Finset (Gamma × A)) (x : Gamma)
    (hsupport : projectionSupport F = {x}) :
    occupancy F x = F.card := by
  classical
  let used : Finset A := Finset.univ.filter fun a ↦ (x, a) ∈ F
  let e : {z // z ∈ F} ≃ {a // a ∈ used} := {
    toFun z := ⟨z.1.2, by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hx := fst_eq_of_mem_of_projectionSupport_eq_singleton
        hsupport z.2
      have hpair : (x, z.1.2) = z.1 := Prod.ext hx.symm rfl
      rw [hpair]
      exact z.2⟩
    invFun a := ⟨(x, a.1), (Finset.mem_filter.mp a.2).2⟩
    left_inv z := by
      apply Subtype.ext
      apply Prod.ext
      · exact (fst_eq_of_mem_of_projectionSupport_eq_singleton
          hsupport z.2).symm
      · rfl
    right_inv a := by
      apply Subtype.ext
      rfl
  }
  change used.card = F.card
  simpa only [Fintype.card_coe] using (Fintype.card_congr e).symm

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Used and unused labels partition the unique occupied fiber. -/
theorem oneFiberRemainingLabel_card_add_occupancy
    (F : Finset (Gamma × A)) (x : Gamma) :
    Fintype.card (OneFiberRemainingLabel F x) + occupancy F x =
      Fintype.card A := by
  classical
  let used : Finset A := Finset.univ.filter fun a ↦ (x, a) ∈ F
  let unused : Finset A := Finset.univ.filter fun a ↦ (x, a) ∉ F
  have hdisjoint : Disjoint unused used := by
    rw [Finset.disjoint_left]
    intro a haUnused haUsed
    exact (Finset.mem_filter.mp haUnused).2 (Finset.mem_filter.mp haUsed).2
  have hunion : unused ∪ used = Finset.univ := by
    ext a
    simp [unused, used]
    simpa [or_comm] using Classical.em ((x, a) ∈ F)
  have hremaining : Fintype.card (OneFiberRemainingLabel F x) = unused.card := by
    let e : OneFiberRemainingLabel F x ≃ {a // a ∈ unused} := {
      toFun := fun a ↦ ⟨a.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.2⟩⟩
      invFun := fun a ↦ ⟨a.1, (Finset.mem_filter.mp a.2).2⟩
      left_inv := fun a ↦ by apply Subtype.ext; rfl
      right_inv := fun a ↦ by apply Subtype.ext; rfl
    }
    simpa only [Fintype.card_coe] using Fintype.card_congr e
  have hcard := Finset.card_union_of_disjoint hdisjoint
  rw [hunion] at hcard
  change Fintype.card (OneFiberRemainingLabel F x) + used.card =
    Fintype.card A
  rw [hremaining, ← hcard]
  rfl

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- The canonical occupied-label cardinality identity. -/
theorem oneFiberRemainingLabel_card_identity
    (d : ℕ) (F : Finset (Gamma × A)) (x : Gamma)
    (hFcard : F.card + 1 = d)
    (hsupport : projectionSupport F = {x}) :
    Fintype.card (OneFiberRemainingLabel F x) + d =
      Fintype.card A + 1 := by
  have hpartition := oneFiberRemainingLabel_card_add_occupancy F x
  have hoccupancy := occupancy_eq_card_of_projectionSupport_eq_singleton
    F x hsupport
  omega

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- An unused label over the already occupied point is an actual link
vertex. -/
theorem oneFiber_insert_sameBase_isFace
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFcard : F.card + 1 = d) (x : Gamma)
    (hsupport : projectionSupport F = {x})
    {a : A} (ha : (x, a) ∉ F) :
    (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace
      (insert (x, a) F) := by
  obtain ⟨_hcard, tau, htau, hcompatible⟩ :=
    (lifted_isFace_iff base d hdimension hd hm F).mp hF
  have hxSupport : x ∈ projectionSupport F := by
    rw [hsupport]
    simp
  have hxTau : x ∈ tau :=
    projectionSupport_subset_of_compatible hcompatible hxSupport
  rw [lifted_isFace_iff base d hdimension hd hm]
  refine ⟨?_, tau, htau, ?_⟩
  · rw [Finset.card_insert_of_notMem ha]
    omega
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact mem_fibersAbove.mpr hxTau
    · exact hcompatible hz

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Every label over a base-link vertex outside the occupied point gives an
actual lifted-link vertex. -/
theorem oneFiber_insert_otherBase_isFace
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hFcard : F.card + 1 = d) (x : Gamma)
    (hsupport : projectionSupport F = {x})
    (b : base.complex.LinkVertex {x}) (a : A) :
    (b.1, a) ∉ F ∧
      (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace
        (insert (b.1, a) F) := by
  have hbne : b.1 ≠ x := by simpa using b.2.1
  have hnot : (b.1, a) ∉ F := by
    intro hmem
    exact hbne (fst_eq_of_mem_of_projectionSupport_eq_singleton
      hsupport hmem)
  obtain ⟨tau, htau, hpair⟩ := b.2.2
  have hxTau : x ∈ tau := hpair (by simp)
  have hbTau : b.1 ∈ tau := hpair (by simp)
  refine ⟨hnot, ?_⟩
  rw [lifted_isFace_iff base d hdimension hd hm]
  refine ⟨?_, tau, htau, ?_⟩
  · rw [Finset.card_insert_of_notMem hnot]
    omega
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact mem_fibersAbove.mpr hbTau
    · exact mem_fibersAbove.mpr
        (fst_eq_of_mem_of_projectionSupport_eq_singleton hsupport hz ▸ hxTau)

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- A concrete lifted-link vertex outside the occupied fiber projects to a
vertex of the base link at the occupied point. -/
noncomputable def oneFiberProjectOtherBase
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (x : Gamma) (hsupport : projectionSupport F = {x})
    (u : (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex F)
    (hu : u.1.1 ≠ x) : base.complex.LinkVertex {x} := by
  refine ⟨u.1.1, by simpa using hu, ?_⟩
  obtain ⟨_hcard, tau, htau, hcompatible⟩ :=
    (lifted_isFace_iff base d hdimension hd hm (insert u.1 F)).mp u.2.2
  have hcompatibleF : CompatibleParent (A := A) tau F :=
    fun z hz ↦ hcompatible (Finset.mem_insert_of_mem hz)
  have hxSupport : x ∈ projectionSupport F := by
    rw [hsupport]
    simp
  have hxTau : x ∈ tau :=
    projectionSupport_subset_of_compatible hcompatibleF hxSupport
  have huTau : u.1.1 ∈ tau :=
    mem_fibersAbove.mp (hcompatible (Finset.mem_insert_self _ _))
  exact ⟨tau, htau, by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact huTau
    · exact hxTau⟩

/-- The concrete link-vertex enumeration for singleton projection support:
unused labels in the occupied fiber form the left summand, while every other
vertex is a base-link vertex paired with an arbitrary fiber label. -/
noncomputable def concreteOneFiberLinkEquiv
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFcard : F.card + 1 = d) (x : Gamma)
    (hsupport : projectionSupport F = {x}) :
    (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex F ≃
      OneFiberVertex (OneFiberRemainingLabel F x)
        (base.complex.LinkVertex {x}) A where
  toFun u := if hu : u.1.1 = x then
      Sum.inl ⟨u.1.2, by
        intro hmem
        apply u.2.1
        have hp : (x, u.1.2) = u.1 := Prod.ext hu.symm rfl
        rwa [← hp]⟩
    else
      Sum.inr (oneFiberProjectOtherBase base d hdimension hd hm F x
        hsupport u hu, u.1.2)
  invFun z := match z with
    | Sum.inl a =>
        ⟨(x, a.1), a.2,
          oneFiber_insert_sameBase_isFace base d hdimension hd hm F hF
            hFcard x hsupport a.2⟩
    | Sum.inr (b, a) =>
        ⟨(b.1, a),
          (oneFiber_insert_otherBase_isFace base d hdimension hd hm F
            hFcard x hsupport b a).1,
          (oneFiber_insert_otherBase_isFace base d hdimension hd hm F
            hFcard x hsupport b a).2⟩
  left_inv u := by
    by_cases hu : u.1.1 = x
    · simp only [dif_pos hu]
      apply Subtype.ext
      exact Prod.ext hu.symm rfl
    · simp only [dif_neg hu]
      apply Subtype.ext
      rfl
  right_inv z := by
    rcases z with a | ⟨b, a⟩
    · simp only [dif_pos rfl]
      congr 1
    · have hbne : b.1 ≠ x := by simpa using b.2.1
      simp only [dif_neg hbne]
      congr 1

/-- Evaluation of the concrete enumeration on the occupied fiber. -/
theorem concreteOneFiberLinkEquiv_eq_inl_of_fst_eq
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFcard : F.card + 1 = d) (x : Gamma)
    (hsupport : projectionSupport F = {x})
    (u : (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex F)
    (hu : u.1.1 = x) :
    ∃ i : OneFiberRemainingLabel F x,
      concreteOneFiberLinkEquiv base d hdimension hd hm F hF hFcard x
        hsupport u = Sum.inl i := by
  let i : OneFiberRemainingLabel F x := ⟨u.1.2, by
    intro hmem
    apply u.2.1
    have hp : (x, u.1.2) = u.1 := Prod.ext hu.symm rfl
    rwa [← hp]⟩
  refine ⟨i, ?_⟩
  apply (concreteOneFiberLinkEquiv base d hdimension hd hm F hF hFcard x
    hsupport).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  exact Prod.ext hu rfl

/-- Evaluation of the concrete enumeration off the occupied fiber. -/
theorem concreteOneFiberLinkEquiv_eq_inr_of_fst_ne
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFcard : F.card + 1 = d) (x : Gamma)
    (hsupport : projectionSupport F = {x})
    (u : (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex F)
    (hu : u.1.1 ≠ x) :
    concreteOneFiberLinkEquiv base d hdimension hd hm F hF hFcard x
        hsupport u =
      Sum.inr (oneFiberProjectOtherBase base d hdimension hd hm F x
        hsupport u hu, u.1.2) := by
  apply (concreteOneFiberLinkEquiv base d hdimension hd hm F hF hFcard x
    hsupport).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  rfl

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- The base vertex link at the unique occupied point is nonempty, since that
point lies in a base triangle supporting the lifted face. -/
theorem oneFiber_baseLink_nonempty
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (x : Gamma) (hsupport : projectionSupport F = {x}) :
    Nonempty (base.complex.LinkVertex {x}) := by
  obtain ⟨_hcard, tau, htau, hcompatible⟩ :=
    (lifted_isFace_iff base d hdimension hd hm F).mp hF
  have hxSupport : x ∈ projectionSupport F := by
    rw [hsupport]
    simp
  have hxTau : x ∈ tau :=
    projectionSupport_subset_of_compatible hcompatible hxSupport
  have htauCard : tau.card = 3 := by
    simpa [hdimension] using base.complex.top_card tau htau
  have heraseCard : (tau.erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hxTau, htauCard]
  have heraseNonempty : (tau.erase x).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨y, hy⟩ := heraseNonempty
  have hyTau : y ∈ tau := (Finset.mem_erase.mp hy).2
  have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
  exact ⟨⟨y, by simpa using hyne, ⟨tau, htau, by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hyTau
    · exact hxTau⟩⟩⟩

/-- The common scalar predicted by the one-fiber edge calculation.  After
the two local `g` cancellations, a base-link edge has canonical weight
`G.weight / m`, leaving this factor. -/
noncomputable def concreteOneFiberCommonScale
    (base : CayleyComplex (V := Gamma)) (d : ℕ) : ℝ :=
  g (Fintype.card A) (d - 1) /
    ((Fintype.card A : ℝ) *
      normalizer (A := A) base.complex d)

theorem concreteOneFiberCommonScale_pos
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) :
    0 < concreteOneFiberCommonScale (A := A) base d := by
  unfold concreteOneFiberCommonScale
  apply div_pos
  · apply g_pos
    · omega
    · omega
  · exact mul_pos (by positivity)
      (normalizer_pos (A := A) base.complex d hdimension (by omega) hm)

/-- Exact common-factor identity for an edge internal to the occupied
fiber. -/
theorem concreteOneFiberLink_weight_occupied_occupied
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d) (x : Gamma)
    (hsupport : projectionSupport F = {x})
    (u v : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).LinkVertex F)
    (hu : u.1.1 = x) (hv : v.1.1 = x) (huv : u ≠ v) :
    ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).weight u v =
      concreteOneFiberCommonScale (A := A) base d *
        (conditionedOneFiberGraph d hd hm
          (oneFiberRemainingLabel_card_identity d F x hFcard hsupport)
          (base.complex.linkGraph {x})).weight
            (concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
              hFcard x hsupport u)
            (concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
              hFcard x hsupport v) := by
  classical
  let eu := concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
    hFcard x hsupport
  obtain ⟨i, hi⟩ := concreteOneFiberLinkEquiv_eq_inl_of_fst_eq
    base d hdimension (by omega) hm F hF hFcard x hsupport u hu
  obtain ⟨j, hj⟩ := concreteOneFiberLinkEquiv_eq_inl_of_fst_eq
    base d hdimension (by omega) hm F hF hFcard x hsupport v hv
  have hij : i ≠ j := by
    intro hij
    apply huv
    apply eu.injective
    rw [hi, hj, hij]
  have huvValue : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
  have hoccF : occupancy F x = d - 1 := by
    rw [occupancy_eq_card_of_projectionSupport_eq_singleton F x hsupport]
    omega
  have hoccE : occupancy (insert v.1 (insert u.1 F)) x = d + 1 := by
    calc
      occupancy (insert v.1 (insert u.1 F)) x =
          occupancy F x + 1 + 1 := by
        rw [occupancy_insert_insert F u.1 v.1 u.2.1 v.2.1 huvValue x,
          hu, hv]
        simp
      _ = d + 1 := by rw [hoccF]; omega
  have hproj : projectionSupport (insert v.1 (insert u.1 F)) = {x} := by
    simp [hsupport, hu, hv]
  rw [concreteOneFiberLink_weight_factorized base d hdimension (by omega) hm
    F hFcard u v huv]
  rw [hproj]
  simp only [Finset.card_singleton, Finset.prod_singleton]
  rw [hoccE, compatibleParentMass_singleton_eq_half_graphVolume
    base.complex hdimension x]
  rw [show d + 1 = (d - 1) + 2 by omega,
    g_add_two_eq_mul_ratio (m := Fintype.card A) (t := d - 1)
      (by omega) (by omega)]
  rw [hi, hj]
  simp only [conditionedOneFiberGraph, oneFiberGraph, hij, if_false]
  unfold concreteOneFiberCommonScale gamma
  rw [if_pos rfl]
  have hcapacity : d - 1 + Fintype.card (OneFiberRemainingLabel F x) =
      Fintype.card A := by
    have hpartition := oneFiberRemainingLabel_card_add_occupancy F x
    rw [hoccF] at hpartition
    omega
  rw [cast_card_sub_occupancy_eq hcapacity]
  have hdOne : 1 ≤ d := by omega
  have hcastD : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hdOne]
    norm_num
  have hcastSucc : ((((d - 1) + 1 : ℕ) : ℝ)) = (d : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hdOne
  simp only [hcastD, hcastSucc]
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hm0 : (Fintype.card A : ℝ) ≠ 0 := by positivity
  have hn0 : (Fintype.card (OneFiberRemainingLabel F x) : ℝ) ≠ 0 := by
    have hn : 2 ≤ Fintype.card (OneFiberRemainingLabel F x) := by omega
    exact_mod_cast (show Fintype.card (OneFiberRemainingLabel F x) ≠ 0 by omega)
  have hn10 : (Fintype.card (OneFiberRemainingLabel F x) : ℝ) - 1 ≠ 0 := by
    have hn : 2 ≤ Fintype.card (OneFiberRemainingLabel F x) := by omega
    exact sub_ne_zero.mpr (by exact_mod_cast (show Fintype.card
      (OneFiberRemainingLabel F x) ≠ 1 by omega))
  have hZ0 : normalizer (A := A) base.complex d ≠ 0 :=
    (normalizer_pos (A := A) base.complex d hdimension (by omega) hm).ne'
  field_simp [hd0, hm0, hn0, hn10, hZ0]

/-- Exact common-factor identity for an edge from the occupied fiber to a
new base fiber. -/
theorem concreteOneFiberLink_weight_occupied_other
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d) (x : Gamma)
    (hsupport : projectionSupport F = {x})
    (u v : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).LinkVertex F)
    (hu : u.1.1 = x) (hv : v.1.1 ≠ x) :
    ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).weight u v =
      concreteOneFiberCommonScale (A := A) base d *
        (conditionedOneFiberGraph d hd hm
          (oneFiberRemainingLabel_card_identity d F x hFcard hsupport)
          (base.complex.linkGraph {x})).weight
            (concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
              hFcard x hsupport u)
            (concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
              hFcard x hsupport v) := by
  classical
  let e := concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
    hFcard x hsupport
  let b := oneFiberProjectOtherBase base d hdimension (by omega) hm F x
    hsupport v hv
  obtain ⟨i, hi⟩ := concreteOneFiberLinkEquiv_eq_inl_of_fst_eq
    base d hdimension (by omega) hm F hF hFcard x hsupport u hu
  have hj := concreteOneFiberLinkEquiv_eq_inr_of_fst_ne
    base d hdimension (by omega) hm F hF hFcard x hsupport v hv
  change e v = Sum.inr (b, v.1.2) at hj
  have huv : u ≠ v := by
    intro huv
    subst v
    exact hv hu
  have huvValue : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
  have hxSupport : x ∈ projectionSupport F := by
    rw [hsupport]
    simp
  have huSupport : u.1.1 ∈ projectionSupport F := by
    rw [hu]
    exact hxSupport
  have hvNotSupport : v.1.1 ∉ projectionSupport F := by
    rw [hsupport]
    simpa using hv
  have hsupportU : projectionSupport (insert u.1 F) = projectionSupport F :=
    projectionSupport_insert_eq F u.1 huSupport
  have hvFresh : v.1 ∉ insert u.1 F := by
    simp [v.2.1, Ne.symm huvValue]
  have hvNotSupportU : v.1.1 ∉ projectionSupport (insert u.1 F) := by
    rw [hsupportU]
    exact hvNotSupport
  have hnew := g_product_insert_new (insert u.1 F) v.1.1 v.1.2
    hvFresh hvNotSupportU
  change
    (∏ y ∈ projectionSupport (insert v.1 (insert u.1 F)),
        g (Fintype.card A) (occupancy (insert v.1 (insert u.1 F)) y)) = _
      at hnew
  rw [hsupportU] at hnew
  have hold := g_product_insert_existing F u.1.1 u.1.2 u.2.1 huSupport
  have hoccF : occupancy F x = d - 1 := by
    rw [occupancy_eq_card_of_projectionSupport_eq_singleton F x hsupport]
    omega
  have hproj : projectionSupport (insert v.1 (insert u.1 F)) =
      insert b.1 {x} := by
    dsimp only [b, oneFiberProjectOtherBase]
    simp [hsupport, hu]
  rw [concreteOneFiberLink_weight_factorized base d hdimension (by omega) hm
    F hFcard u v huv]
  rw [hnew, hold, hproj]
  have hbx : b.1 ∉ ({x} : Finset Gamma) := b.2.1
  rw [Finset.card_insert_of_notMem hbx, Finset.card_singleton]
  rw [compatibleParentMass_pair_eq_baseLink_degree
    base.complex hdimension x b]
  rw [hi, hj]
  simp only [conditionedOneFiberGraph, oneFiberGraph]
  unfold concreteOneFiberCommonScale gamma
  rw [if_neg (by omega : (2 : ℕ) ≠ 1)]
  simp only [one_mul]
  rw [hu, hoccF]
  rw [hsupport]
  simp only [Finset.prod_singleton, hoccF]
  have hcapacity : d - 1 + Fintype.card (OneFiberRemainingLabel F x) =
      Fintype.card A := by
    have hpartition := oneFiberRemainingLabel_card_add_occupancy F x
    rw [hoccF] at hpartition
    omega
  rw [cast_card_sub_occupancy_eq hcapacity]
  have hdOne : 1 ≤ d := by omega
  have hcastD : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hdOne]
    norm_num
  simp only [hcastD]
  have hm0 : (Fintype.card A : ℝ) ≠ 0 := by positivity
  have hn0 : (Fintype.card (OneFiberRemainingLabel F x) : ℝ) ≠ 0 := by
    have hn : 2 ≤ Fintype.card (OneFiberRemainingLabel F x) := by omega
    exact_mod_cast (show Fintype.card (OneFiberRemainingLabel F x) ≠ 0 by omega)
  have hZ0 : normalizer (A := A) base.complex d ≠ 0 :=
    (normalizer_pos (A := A) base.complex d hdimension (by omega) hm).ne'
  field_simp [hm0, hn0, hZ0]

/-- Exact common-factor identity for two distinct labels over the same new
base vertex. -/
theorem concreteOneFiberLink_weight_other_sameBase
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d) (x : Gamma)
    (hsupport : projectionSupport F = {x})
    (u v : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).LinkVertex F)
    (hu : u.1.1 ≠ x) (hv : v.1.1 ≠ x) (hbase : u.1.1 = v.1.1)
    (huv : u ≠ v) :
    ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).weight u v =
      concreteOneFiberCommonScale (A := A) base d *
        (conditionedOneFiberGraph d hd hm
          (oneFiberRemainingLabel_card_identity d F x hFcard hsupport)
          (base.complex.linkGraph {x})).weight
            (concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
              hFcard x hsupport u)
            (concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
              hFcard x hsupport v) := by
  classical
  let e := concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
    hFcard x hsupport
  let b := oneFiberProjectOtherBase base d hdimension (by omega) hm F x
    hsupport u hu
  let c := oneFiberProjectOtherBase base d hdimension (by omega) hm F x
    hsupport v hv
  have hi := concreteOneFiberLinkEquiv_eq_inr_of_fst_ne
    base d hdimension (by omega) hm F hF hFcard x hsupport u hu
  have hj := concreteOneFiberLinkEquiv_eq_inr_of_fst_ne
    base d hdimension (by omega) hm F hF hFcard x hsupport v hv
  change e u = Sum.inr (b, u.1.2) at hi
  change e v = Sum.inr (c, v.1.2) at hj
  have hbc : b = c := by
    apply Subtype.ext
    exact hbase
  have hlabel : u.1.2 ≠ v.1.2 := by
    intro hlabel
    apply huv
    apply Subtype.ext
    exact Prod.ext hbase hlabel
  have huvValue : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
  have huNotSupport : u.1.1 ∉ projectionSupport F := by
    rw [hsupport]
    simpa using hu
  have hoccFU : occupancy F u.1.1 = 0 := by
    exact Nat.eq_zero_of_not_pos (fun hpos ↦
      huNotSupport (mem_projectionSupport.mpr ((occupancy_pos_iff F u.1.1).mp hpos)))
  have hnewU := g_product_insert_new F u.1.1 u.1.2 u.2.1 huNotSupport
  change
    (∏ y ∈ projectionSupport (insert u.1 F),
        g (Fintype.card A) (occupancy (insert u.1 F) y)) = _ at hnewU
  have hvFresh : v.1 ∉ insert u.1 F := by
    simp [v.2.1, Ne.symm huvValue]
  have hvSupportU : v.1.1 ∈ projectionSupport (insert u.1 F) := by
    rw [projectionSupport_insert]
    simp [← hbase]
  have hexistingV := g_product_insert_existing (insert u.1 F)
    v.1.1 v.1.2 hvFresh hvSupportU
  change
    (∏ y ∈ projectionSupport (insert u.1 F),
        g (Fintype.card A) (occupancy (insert v.1 (insert u.1 F)) y)) = _
      at hexistingV
  have hsupportV : projectionSupport (insert v.1 (insert u.1 F)) =
      projectionSupport (insert u.1 F) :=
    projectionSupport_insert_eq (insert u.1 F) v.1 hvSupportU
  have hoccInsert : occupancy (insert u.1 F) v.1.1 = 1 := by
    have hoccFV : occupancy F v.1.1 = 0 := by
      rw [← hbase]
      exact hoccFU
    rw [occupancy_insert_of_notMem F u.1 u.2.1 v.1.1]
    simp [hbase, hoccFV]
  have hproj : projectionSupport (insert v.1 (insert u.1 F)) =
      insert b.1 {x} := by
    dsimp only [b, oneFiberProjectOtherBase]
    simp [hsupport, hbase]
  have hprojU : projectionSupport (insert u.1 F) = insert b.1 {x} :=
    hsupportV.symm.trans hproj
  have hoccF : occupancy F x = d - 1 := by
    rw [occupancy_eq_card_of_projectionSupport_eq_singleton F x hsupport]
    omega
  rw [concreteOneFiberLink_weight_factorized base d hdimension (by omega) hm
    F hFcard u v huv]
  rw [hsupportV, hexistingV, hnewU, hprojU]
  have hbx : b.1 ∉ ({x} : Finset Gamma) := b.2.1
  rw [Finset.card_insert_of_notMem hbx, Finset.card_singleton]
  rw [compatibleParentMass_pair_eq_baseLink_degree
    base.complex hdimension x b]
  rw [hi, hj]
  simp only [conditionedOneFiberGraph, oneFiberGraph, hbc, hlabel,
    if_pos, if_false]
  unfold concreteOneFiberCommonScale gamma
  rw [if_neg (by omega : (2 : ℕ) ≠ 1)]
  simp only [one_mul]
  rw [hoccInsert, hsupport]
  simp only [Finset.prod_singleton, hoccF]
  have hm0 : (Fintype.card A : ℝ) ≠ 0 := by positivity
  have hm10 : (Fintype.card A : ℝ) - 1 ≠ 0 := by
    have hmTwo : 2 ≤ Fintype.card A := by omega
    exact sub_ne_zero.mpr (by exact_mod_cast
      (show Fintype.card A ≠ 1 by omega))
  have hZ0 : normalizer (A := A) base.complex d ≠ 0 :=
    (normalizer_pos (A := A) base.complex d hdimension (by omega) hm).ne'
  field_simp [hm0, hm10, hZ0]
  ring

/-- Exact common-factor identity for an edge joining two different new base
fibers. -/
theorem concreteOneFiberLink_weight_other_distinctBase
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d) (x : Gamma)
    (hsupport : projectionSupport F = {x})
    (u v : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).LinkVertex F)
    (hu : u.1.1 ≠ x) (hv : v.1.1 ≠ x) (hbase : u.1.1 ≠ v.1.1) :
    ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).weight u v =
      concreteOneFiberCommonScale (A := A) base d *
        (conditionedOneFiberGraph d hd hm
          (oneFiberRemainingLabel_card_identity d F x hFcard hsupport)
          (base.complex.linkGraph {x})).weight
            (concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
              hFcard x hsupport u)
            (concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
              hFcard x hsupport v) := by
  classical
  let e := concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
    hFcard x hsupport
  let b := oneFiberProjectOtherBase base d hdimension (by omega) hm F x
    hsupport u hu
  let c := oneFiberProjectOtherBase base d hdimension (by omega) hm F x
    hsupport v hv
  have hi := concreteOneFiberLinkEquiv_eq_inr_of_fst_ne
    base d hdimension (by omega) hm F hF hFcard x hsupport u hu
  have hj := concreteOneFiberLinkEquiv_eq_inr_of_fst_ne
    base d hdimension (by omega) hm F hF hFcard x hsupport v hv
  change e u = Sum.inr (b, u.1.2) at hi
  change e v = Sum.inr (c, v.1.2) at hj
  have hbc : b ≠ c := by
    intro hbc
    apply hbase
    exact congrArg Subtype.val hbc
  have huv : u ≠ v := by
    intro huv
    apply hbase
    exact congrArg (fun z ↦ z.1.1) huv
  have huvValue : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
  have huNotSupport : u.1.1 ∉ projectionSupport F := by
    rw [hsupport]
    simpa using hu
  have hvNotSupport : v.1.1 ∉ projectionSupport F := by
    rw [hsupport]
    simpa using hv
  have hnewU := g_product_insert_new F u.1.1 u.1.2 u.2.1 huNotSupport
  change
    (∏ y ∈ projectionSupport (insert u.1 F),
        g (Fintype.card A) (occupancy (insert u.1 F) y)) = _ at hnewU
  have hvFresh : v.1 ∉ insert u.1 F := by
    simp [v.2.1, Ne.symm huvValue]
  have hvNotSupportU : v.1.1 ∉ projectionSupport (insert u.1 F) := by
    rw [projectionSupport_insert]
    simp [hvNotSupport, Ne.symm hbase]
  have hnewV := g_product_insert_new (insert u.1 F) v.1.1 v.1.2
    hvFresh hvNotSupportU
  change
    (∏ y ∈ projectionSupport (insert v.1 (insert u.1 F)),
        g (Fintype.card A) (occupancy (insert v.1 (insert u.1 F)) y)) = _
      at hnewV
  have hproj : projectionSupport (insert v.1 (insert u.1 F)) =
      insert c.1 (insert b.1 {x}) := by
    dsimp only [b, c, oneFiberProjectOtherBase]
    simp [hsupport]
  have hoccF : occupancy F x = d - 1 := by
    rw [occupancy_eq_card_of_projectionSupport_eq_singleton F x hsupport]
    omega
  rw [concreteOneFiberLink_weight_factorized base d hdimension (by omega) hm
    F hFcard u v huv]
  rw [hnewV, hnewU, hproj]
  have hbnot : b.1 ∉ ({x} : Finset Gamma) := b.2.1
  have hcb : c.1 ≠ b.1 := fun h ↦ hbc (Subtype.ext h.symm)
  have hcnot : c.1 ∉ insert b.1 ({x} : Finset Gamma) := by
    simp [hcb, c.2.1]
  rw [Finset.card_insert_of_notMem hcnot,
    Finset.card_insert_of_notMem hbnot, Finset.card_singleton]
  rw [compatibleParentMass_three_eq_baseLink_weight
    base.complex x b c hbc]
  rw [hi, hj]
  simp only [conditionedOneFiberGraph, oneFiberGraph, hbc, if_false]
  unfold concreteOneFiberCommonScale gamma
  rw [if_neg (by omega : (3 : ℕ) ≠ 1)]
  simp only [one_mul]
  rw [hsupport]
  simp only [Finset.prod_singleton, hoccF]
  have hm0 : (Fintype.card A : ℝ) ≠ 0 := by positivity
  have hZ0 : normalizer (A := A) base.complex d ≠ 0 :=
    (normalizer_pos (A := A) base.complex d hdimension (by omega) hm).ne'
  field_simp [hm0, hZ0]

/-- Uniform common-factor identity for every pair of vertices in a concrete
singleton-support link. -/
theorem concreteOneFiberLink_weight_eq
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d) (x : Gamma)
    (hsupport : projectionSupport F = {x})
    (u v : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).LinkVertex F) :
    ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).weight u v =
      concreteOneFiberCommonScale (A := A) base d *
        (conditionedOneFiberGraph d hd hm
          (oneFiberRemainingLabel_card_identity d F x hFcard hsupport)
          (base.complex.linkGraph {x})).weight
            (concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
              hFcard x hsupport u)
            (concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
              hFcard x hsupport v) := by
  classical
  let H := (measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F
  let M := conditionedOneFiberGraph d hd hm
    (oneFiberRemainingLabel_card_identity d F x hFcard hsupport)
    (base.complex.linkGraph {x})
  let e := concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
    hFcard x hsupport
  by_cases huv : u = v
  · subst v
    change H.weight u u = concreteOneFiberCommonScale (A := A) base d *
      M.weight (e u) (e u)
    rw [H.weight_self, M.weight_self, mul_zero]
  · by_cases hu : u.1.1 = x
    · by_cases hv : v.1.1 = x
      · exact concreteOneFiberLink_weight_occupied_occupied
          base d hdimension hd hm F hF hFcard x hsupport u v hu hv huv
      · exact concreteOneFiberLink_weight_occupied_other
          base d hdimension hd hm F hF hFcard x hsupport u v hu hv
    · by_cases hv : v.1.1 = x
      · change H.weight u v = concreteOneFiberCommonScale (A := A) base d *
          M.weight (e u) (e v)
        calc
          H.weight u v = H.weight v u := H.weight_symm u v
          _ = concreteOneFiberCommonScale (A := A) base d *
              M.weight (e v) (e u) :=
            concreteOneFiberLink_weight_occupied_other
              base d hdimension hd hm F hF hFcard x hsupport v u hv hu
          _ = concreteOneFiberCommonScale (A := A) base d *
              M.weight (e u) (e v) := by rw [M.weight_symm]
      · by_cases hbase : u.1.1 = v.1.1
        · exact concreteOneFiberLink_weight_other_sameBase
            base d hdimension hd hm F hF hFcard x hsupport u v hu hv hbase huv
        · exact concreteOneFiberLink_weight_other_distinctBase
            base d hdimension hd hm F hF hFcard x hsupport u v hu hv hbase

/-- An exact common-factor formula for actual link edges produces the
transport certificate required by the canonical one-fiber calculation. -/
noncomputable def concreteOneFiberLinkCertificate_of_weight_formula
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d) (x : Gamma)
    (hsupport : projectionSupport F = {x})
    [Nonempty (base.complex.LinkVertex {x})]
    (hweight : ∀ u v :
      (measuredComplex (A := A) base.complex d hdimension (by omega) hm).LinkVertex F,
      ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).weight u v =
        concreteOneFiberCommonScale (A := A) base d *
          (conditionedOneFiberGraph d hd hm
            (oneFiberRemainingLabel_card_identity d F x hFcard hsupport)
            (base.complex.linkGraph {x})).weight
              (concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
                hFcard x hsupport u)
              (concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
                hFcard x hsupport v)) :
    OneFiberLinkCertificate
      (O := OneFiberRemainingLabel F x)
      (B := base.complex.LinkVertex {x}) (A := A)
      ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F)
      d (base.complex.linkGraph {x}) where
  dimension_ge_three := hd
  fiber_size := hm
  occupied_card := oneFiberRemainingLabel_card_identity d F x hFcard hsupport
  enumerate := concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
    hFcard x hsupport
  commonScale := concreteOneFiberCommonScale (A := A) base d
  commonScale_pos := concreteOneFiberCommonScale_pos base d hdimension hd hm
  relabel_eq := by
    apply WeightedGraph.ext_weight
    intro u v
    rw [WeightedGraph.relabel_weight]
    change _ = concreteOneFiberCommonScale (A := A) base d *
      (conditionedOneFiberGraph d hd hm
        (oneFiberRemainingLabel_card_identity d F x hFcard hsupport)
        (base.complex.linkGraph {x})).weight
          (concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
            hFcard x hsupport u)
          (concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
            hFcard x hsupport v)
    exact hweight u v

/-- The actual singleton-support codimension-two link has the full two-sided
`1/d` bound once its explicit edge formula is matched with the canonical
weights.  The only spectral input is the corresponding base vertex link. -/
theorem concreteOneFiberLink_twoSidedSpectralBound_of_weight_formula
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d) (x : Gamma)
    (hsupport : projectionSupport F = {x})
    (hdegree : ∀ b : base.complex.LinkVertex {x},
      0 < (base.complex.linkGraph {x}).degree b)
    (hbase : (base.complex.linkGraph {x}).TwoSidedSpectralBound
      (1 / (d : ℝ)))
    (hweight : ∀ u v :
      (measuredComplex (A := A) base.complex d hdimension (by omega) hm).LinkVertex F,
      ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).weight u v =
        concreteOneFiberCommonScale (A := A) base d *
          (conditionedOneFiberGraph d hd hm
            (oneFiberRemainingLabel_card_identity d F x hFcard hsupport)
            (base.complex.linkGraph {x})).weight
              (concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
                hFcard x hsupport u)
              (concreteOneFiberLinkEquiv base d hdimension (by omega) hm F hF
                hFcard x hsupport v)) :
    WeightedGraph.TwoSidedSpectralBound
      ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F)
      (1 / (d : ℝ)) := by
  letI : Nonempty (base.complex.LinkVertex {x}) :=
    oneFiber_baseLink_nonempty base d hdimension (by omega) hm F hF x hsupport
  exact (concreteOneFiberLinkCertificate_of_weight_formula
    base d hdimension hd hm F hF hFcard x hsupport hweight).twoSidedSpectralBound
      hdegree hbase

/-- Unconditional singleton-support link bound: the exact edge calculation
above and positivity of vertex-link degrees discharge all bridge hypotheses. -/
theorem concreteOneFiberLink_twoSidedSpectralBound
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d) (x : Gamma)
    (hsupport : projectionSupport F = {x})
    (hbase : (base.complex.linkGraph {x}).TwoSidedSpectralBound
      (1 / (d : ℝ))) :
    WeightedGraph.TwoSidedSpectralBound
      ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F)
      (1 / (d : ℝ)) := by
  apply concreteOneFiberLink_twoSidedSpectralBound_of_weight_formula
    base d hdimension hd hm F hF hFcard x hsupport
  · exact MeasuredComplex.vertexLink_degree_pos base.complex hdimension x
  · exact hbase
  · exact concreteOneFiberLink_weight_eq
      base d hdimension hd hm F hF hFcard x hsupport

/-- The complete `r(F)=1` row of Theorem 5.1, in the interface consumed by
the exhaustive codimension-two assembly. -/
theorem occupancyCaseBound_one
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A)
    (hbase : base.complex.CodimensionTwoBound (1 / (d : ℝ))) :
    OccupancyCaseBound (A := A) base d hdimension hd hm 1 := by
  intro F hF hFcard hsupportCard
  obtain ⟨x, hsupport⟩ := Finset.card_eq_one.mp hsupportCard
  have hxFace : base.complex.IsFace ({x} : Finset Gamma) := by
    have hprojection := projectionSupport_isFace
      (A := A) base d hdimension (by omega) hm F hF
    rwa [hsupport] at hprojection
  have hxCard : ({x} : Finset Gamma).card + 1 = base.complex.dim := by
    simp [hdimension]
  exact concreteOneFiberLink_twoSidedSpectralBound
    base d hdimension hd hm F hF hFcard x hsupport
      (hbase {x} hxFace hxCard)

end WeightedLift

end HDXLean
