import HDXLean.WeightedLiftTwoFiberSpectrum
import HDXLean.WeightedLiftThreeFiberBridge
import HDXLean.WeightedLiftOneFiberBridge

/-!
# Concrete data for the two-fiber conditioned link

This module supplies the finite geometry and the vertex enumeration needed to
apply `WeightedLiftTwoFiberSpectrum` to a codimension-two lifted face whose
projection support has cardinality two.  The edge-weight calculation is kept
separate: the constructions here do not make any regularity assumption on the
base complex.
-/

namespace HDXLean

open scoped BigOperators

namespace WeightedLift

variable {Gamma A : Type*}
  [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma] [DecidableEq Gamma]
  [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A]

/-- A possible third base vertex above a fixed two-point support.  The witness
triangle is not part of the data, since a two-point support and its third
vertex determine that triangle uniquely. -/
def CompatibleThirdVertex (X : MeasuredComplex Gamma) (S : Finset Gamma) :=
  {z : Gamma // z ∉ S ∧ ∃ tau ∈ X.topFaces, S ⊆ tau ∧ z ∈ tau}

/-- Base triangles containing a prescribed support. -/
def CompatibleBaseTriangle (X : MeasuredComplex Gamma) (S : Finset Gamma) :=
  {tau : Finset Gamma // tau ∈ X.topFaces ∧ S ⊆ tau}

noncomputable instance (X : MeasuredComplex Gamma) (S : Finset Gamma) :
    Fintype (CompatibleBaseTriangle X S) := by
  letI : Finite (CompatibleBaseTriangle X S) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance (X : MeasuredComplex Gamma) (S : Finset Gamma) :
    Fintype (CompatibleThirdVertex X S) := by
  letI : Finite (CompatibleThirdVertex X S) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance (X : MeasuredComplex Gamma) (S : Finset Gamma) :
    DecidableEq (CompatibleThirdVertex X S) := Classical.decEq _

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- The triangle determined by a compatible third vertex. -/
theorem compatibleThirdVertex_parent_mem
    (X : MeasuredComplex Gamma) (hdimension : X.dim = 2)
    (S : Finset Gamma) (hS : S.card = 2)
    (z : CompatibleThirdVertex X S) :
    insert z.1 S ∈ X.topFaces := by
  obtain ⟨tau, htau, hStau, hztau⟩ := z.2.2
  have hparentCard : (insert z.1 S).card = 3 := by
    rw [Finset.card_insert_of_notMem z.2.1, hS]
  have htauCard : tau.card = 3 := by
    simpa [hdimension] using X.top_card tau htau
  have hsubset : insert z.1 S ⊆ tau := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hztau
    · exact hStau hx
  have heq : insert z.1 S = tau :=
    Finset.eq_of_subset_of_card_le hsubset (by omega)
  rwa [heq]

omit [AddCommGroup Gamma] [Module F₂ Gamma]
    [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A] in
/-- Different third vertices determine different parent triangles. -/
theorem compatibleThirdVertex_parent_injective
    (S : Finset Gamma) :
    Function.Injective
      (fun z : CompatibleThirdVertex X S ↦ insert z.1 S) := by
  intro z w hparent
  change insert z.1 S = insert w.1 S at hparent
  apply Subtype.ext
  have hz : z.1 ∈ insert w.1 S := by
    rw [← hparent]
    exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp hz with h | h
  · exact h
  · exact (z.2.1 h).elim

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- A two-point face contained in a base top face has at least one compatible
third vertex. -/
theorem compatibleThirdVertex_nonempty_of_isFace
    (X : MeasuredComplex Gamma) (hdimension : X.dim = 2)
    (S : Finset Gamma) (hS : S.card = 2) (hface : X.IsFace S) :
    Nonempty (CompatibleThirdVertex X S) := by
  obtain ⟨tau, htau, hStau⟩ := hface
  have htauCard : tau.card = 3 := by
    simpa [hdimension] using X.top_card tau htau
  have hnsub : ¬ tau ⊆ S := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  rw [Finset.not_subset] at hnsub
  obtain ⟨z, hztau, hzS⟩ := hnsub
  exact ⟨⟨z, hzS, tau, htau, hStau, hztau⟩⟩

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- The unique vertex of a compatible triangle outside a two-point support. -/
noncomputable def compatibleTriangleThird
    (X : MeasuredComplex Gamma) (hdimension : X.dim = 2)
    (S : Finset Gamma) (hS : S.card = 2)
    (tau : CompatibleBaseTriangle X S) : CompatibleThirdVertex X S := by
  have htauCard : tau.1.card = 3 := by
    simpa [hdimension] using X.top_card tau.1 tau.2.1
  have hnsub : ¬ tau.1 ⊆ S := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  rw [Finset.not_subset] at hnsub
  let z : Gamma := Classical.choose hnsub
  have hztau : z ∈ tau.1 := (Classical.choose_spec hnsub).1
  have hzS : z ∉ S := (Classical.choose_spec hnsub).2
  exact ⟨z, hzS, tau.1, tau.2.1, tau.2.2, hztau⟩

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
theorem compatibleTriangleThird_mem
    (X : MeasuredComplex Gamma) (hdimension : X.dim = 2)
    (S : Finset Gamma) (hS : S.card = 2)
    (tau : CompatibleBaseTriangle X S) :
    (compatibleTriangleThird X hdimension S hS tau).1 ∈ tau.1 := by
  classical
  have htauCard : tau.1.card = 3 := by
    simpa [hdimension] using X.top_card tau.1 tau.2.1
  have hnsub : ¬ tau.1 ⊆ S := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  rw [Finset.not_subset] at hnsub
  unfold compatibleTriangleThird
  exact (Classical.choose_spec hnsub).1

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Compatible triangles and possible third vertices are canonically
equivalent once the support has cardinality two. -/
noncomputable def compatibleTriangleEquivThird
    (X : MeasuredComplex Gamma) (hdimension : X.dim = 2)
    (S : Finset Gamma) (hS : S.card = 2) :
    CompatibleBaseTriangle X S ≃ CompatibleThirdVertex X S where
  toFun := compatibleTriangleThird X hdimension S hS
  invFun z := ⟨insert z.1 S,
    compatibleThirdVertex_parent_mem X hdimension S hS z,
    Finset.subset_insert _ _⟩
  left_inv tau := by
    apply Subtype.ext
    have htauCard : tau.1.card = 3 := by
      simpa [hdimension] using X.top_card tau.1 tau.2.1
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact compatibleTriangleThird_mem X hdimension S hS tau
      · exact tau.2.2 hx
    · rw [Finset.card_insert_of_notMem
          (compatibleTriangleThird X hdimension S hS tau).2.1,
        hS, htauCard]
  right_inv z := by
    apply Subtype.ext
    have hzmem : (compatibleTriangleThird X hdimension S hS
        ⟨insert z.1 S,
          compatibleThirdVertex_parent_mem X hdimension S hS z,
          Finset.subset_insert _ _⟩).1 ∈ insert z.1 S :=
      compatibleTriangleThird_mem X hdimension S hS _
    rcases Finset.mem_insert.mp hzmem with h | h
    · exact h
    · exact ((compatibleTriangleThird X hdimension S hS _).2.1 h).elim

/-- A fixed enumeration of the two occupied base points. -/
noncomputable def twoSupportIndexEquiv (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 2) :
    Fin 2 ≃ {x : Gamma // x ∈ projectionSupport F} :=
  (Equiv.cast (congrArg Fin hsupport.symm)).trans
    (Finset.equivFin (projectionSupport F)).symm

/-- The `i`-th occupied base point. -/
noncomputable def twoSupportBase (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 2) (i : Fin 2) : Gamma :=
  (twoSupportIndexEquiv F hsupport i).1

omit [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma]
    [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A] in
theorem twoSupportBase_mem (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 2) (i : Fin 2) :
    twoSupportBase F hsupport i ∈ projectionSupport F :=
  (twoSupportIndexEquiv F hsupport i).2

omit [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma]
    [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A] in
theorem twoSupportBase_injective (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 2) :
    Function.Injective (twoSupportBase F hsupport) := by
  intro i j hij
  apply (twoSupportIndexEquiv F hsupport).injective
  apply Subtype.ext
  exact hij

omit [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma]
    [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A] in
/-- Membership in a two-point support is exhausted by its fixed enumeration. -/
theorem mem_projectionSupport_iff_twoSupportBase
    (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 2) (x : Gamma) :
    x ∈ projectionSupport F ↔
      x = twoSupportBase F hsupport 0 ∨
      x = twoSupportBase F hsupport 1 := by
  constructor
  · intro hx
    let i := (twoSupportIndexEquiv F hsupport).symm ⟨x, hx⟩
    have hi : i.1 = 0 ∨ i.1 = 1 := by omega
    rcases hi with hi | hi
    · left
      have hieq : i = 0 := Fin.ext hi
      change x = ((twoSupportIndexEquiv F hsupport) 0).1
      have he := congrArg Subtype.val
        ((twoSupportIndexEquiv F hsupport).apply_symm_apply ⟨x, hx⟩)
      change ((twoSupportIndexEquiv F hsupport) i).1 = x at he
      rw [hieq] at he
      exact he.symm
    · right
      have hieq : i = 1 := Fin.ext hi
      change x = ((twoSupportIndexEquiv F hsupport) 1).1
      have he := congrArg Subtype.val
        ((twoSupportIndexEquiv F hsupport).apply_symm_apply ⟨x, hx⟩)
      change ((twoSupportIndexEquiv F hsupport) i).1 = x at he
      rw [hieq] at he
      exact he.symm
  · rintro (rfl | rfl)
    · exact twoSupportBase_mem F hsupport 0
    · exact twoSupportBase_mem F hsupport 1

/-- Occupancy of the `i`-th occupied fiber. -/
noncomputable def concreteTwoOccupancy (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 2) (i : Fin 2) : ℕ :=
  occupancy F (twoSupportBase F hsupport i)

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
theorem concreteTwoOccupancy_pos (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 2) (i : Fin 2) :
    0 < concreteTwoOccupancy F hsupport i := by
  apply (occupancy_pos_iff F _).mpr
  exact mem_projectionSupport.mp (twoSupportBase_mem F hsupport i)

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
theorem concreteTwoOccupancy_sum (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 2) :
    ∑ i : Fin 2, concreteTwoOccupancy F hsupport i = F.card := by
  let e := twoSupportIndexEquiv F hsupport
  calc
    (∑ i : Fin 2, concreteTwoOccupancy F hsupport i) =
        ∑ x : {x : Gamma // x ∈ projectionSupport F}, occupancy F x.1 := by
      exact e.sum_comp (fun x ↦ occupancy F x.1)
    _ = ∑ x ∈ projectionSupport F, occupancy F x := by
      symm
      apply Finset.sum_subtype (projectionSupport F)
      intro x
      rfl
    _ = F.card := sum_occupancy_projectionSupport F

/-- The unused labels in one of the two occupied fibers. -/
abbrev TwoFiberRemainingLabel (F : Finset (Gamma × A)) (x : Gamma) :=
  OneFiberRemainingLabel F x

/-- Explicitly enumerate unused labels by the `Fin (m - occupancy)` type of
the canonical two-fiber model. -/
noncomputable def twoFiberRemainingLabelEquivFin
    (F : Finset (Gamma × A)) (x : Gamma) :
    TwoFiberRemainingLabel F x ≃ Fin (Fintype.card A - occupancy F x) := by
  have hcard : Fintype.card (TwoFiberRemainingLabel F x) =
      Fintype.card A - occupancy F x := by
    exact Nat.eq_sub_of_add_eq
      (oneFiberRemainingLabel_card_add_occupancy F x)
  exact (Fintype.equivFin (TwoFiberRemainingLabel F x)).trans
    (Equiv.cast (congrArg Fin hcard))

/-- Total unnormalized mass of the compatible base parents. -/
noncomputable def compatibleThirdMass (X : MeasuredComplex Gamma)
    (S : Finset Gamma) : ℝ :=
  ∑ z : CompatibleThirdVertex X S, X.topWeight (insert z.1 S)

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Enumerating compatible parents by their unique third vertex does not
change their total mass. -/
theorem compatibleParentMass_eq_compatibleThirdMass
    (X : MeasuredComplex Gamma) (hdimension : X.dim = 2)
    (S : Finset Gamma) (hS : S.card = 2) :
    compatibleParentMass X S = compatibleThirdMass X S := by
  classical
  let e := compatibleTriangleEquivThird X hdimension S hS
  calc
    compatibleParentMass X S =
        ∑ tau ∈ X.topFaces.filter (fun tau ↦ S ⊆ tau), X.topWeight tau := by
      unfold compatibleParentMass
      rw [Finset.sum_filter]
    _ = ∑ tau : CompatibleBaseTriangle X S, X.topWeight tau.1 := by
      apply Finset.sum_subtype (X.topFaces.filter (fun tau ↦ S ⊆ tau))
      intro tau
      simp [CompatibleBaseTriangle]
    _ = ∑ z : CompatibleThirdVertex X S,
        X.topWeight ((e.symm z).1) :=
      (e.symm.sum_comp
        (fun tau : CompatibleBaseTriangle X S ↦ X.topWeight tau.1)).symm
    _ = compatibleThirdMass X S := by
      unfold compatibleThirdMass e compatibleTriangleEquivThird
      rfl

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- A compatible three-point support has exactly its own top weight as total
compatible-parent mass. -/
theorem compatibleParentMass_eq_topWeight_of_mem
    (X : MeasuredComplex Gamma) (hdimension : X.dim = 2)
    (T : Finset Gamma) (hT : T ∈ X.topFaces) :
    compatibleParentMass X T = X.topWeight T := by
  classical
  unfold compatibleParentMass
  rw [Finset.sum_eq_single T]
  · simp [hT]
  · intro U hU hne
    have hUcard : U.card = 3 := by
      simpa [hdimension] using X.top_card U hU
    have hTcard : T.card = 3 := by
      simpa [hdimension] using X.top_card T hT
    rw [if_neg]
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  · exact fun hnot ↦ (hnot hT).elim

theorem compatibleThirdMass_pos
    (X : MeasuredComplex Gamma) (hdimension : X.dim = 2)
    (S : Finset Gamma) (hS : S.card = 2)
    [Nonempty (CompatibleThirdVertex X S)] :
    0 < compatibleThirdMass X S := by
  classical
  let z : CompatibleThirdVertex X S := Classical.choice inferInstance
  apply Finset.sum_pos'
  · intro w _hw
    exact (X.topWeight_pos _
      (compatibleThirdVertex_parent_mem X hdimension S hS w)).le
  · exact ⟨z, Finset.mem_univ _, X.topWeight_pos _
      (compatibleThirdVertex_parent_mem X hdimension S hS z)⟩

/-- The normalized positive distribution on possible third base vertices. -/
noncomputable def concreteTwoOmega (X : MeasuredComplex Gamma)
    (S : Finset Gamma) (z : CompatibleThirdVertex X S) : ℝ :=
  X.topWeight (insert z.1 S) / compatibleThirdMass X S

theorem concreteTwoOmega_pos
    (X : MeasuredComplex Gamma) (hdimension : X.dim = 2)
    (S : Finset Gamma) (hS : S.card = 2)
    [Nonempty (CompatibleThirdVertex X S)]
    (z : CompatibleThirdVertex X S) :
    0 < concreteTwoOmega X S z := by
  exact div_pos
    (X.topWeight_pos _ (compatibleThirdVertex_parent_mem X hdimension S hS z))
    (compatibleThirdMass_pos X hdimension S hS)

theorem concreteTwoOmega_sum
    (X : MeasuredComplex Gamma) (hdimension : X.dim = 2)
    (S : Finset Gamma) (hS : S.card = 2)
    [Nonempty (CompatibleThirdVertex X S)] :
    ∑ z : CompatibleThirdVertex X S, concreteTwoOmega X S z = 1 := by
  classical
  unfold concreteTwoOmega compatibleThirdMass
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (compatibleThirdMass_pos X hdimension S hS))

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Adjoining an unused label over either occupied base point stays in the
actual lifted link. -/
theorem twoFiber_insert_occupied_isFace
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFcard : F.card + 1 = d) {x : Gamma}
    (hx : x ∈ projectionSupport F) {a : A} (ha : (x, a) ∉ F) :
    (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace
      (insert (x, a) F) := by
  obtain ⟨_hcard, tau, htau, hcompatible⟩ :=
    (lifted_isFace_iff base d hdimension hd hm F).mp hF
  have hxTau := projectionSupport_subset_of_compatible hcompatible hx
  rw [lifted_isFace_iff base d hdimension hd hm]
  refine ⟨?_, tau, htau, ?_⟩
  · rw [Finset.card_insert_of_notMem ha]
    omega
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact mem_fibersAbove.mpr hxTau
    · exact hcompatible hz

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Every label over a compatible third vertex gives an actual link vertex. -/
theorem twoFiber_insert_third_isFace
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 2)
    (z : CompatibleThirdVertex base.complex (projectionSupport F)) (a : A) :
    (z.1, a) ∉ F ∧
      (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace
        (insert (z.1, a) F) := by
  have hnot : (z.1, a) ∉ F := by
    intro hmem
    exact z.2.1 (mem_projectionSupport.mpr ⟨a, hmem⟩)
  refine ⟨hnot, ?_⟩
  rw [lifted_isFace_iff base d hdimension hd hm]
  refine ⟨?_, insert z.1 (projectionSupport F),
    compatibleThirdVertex_parent_mem base.complex hdimension _ hsupport z, ?_⟩
  · rw [Finset.card_insert_of_notMem hnot]
    omega
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact mem_fibersAbove.mpr (Finset.mem_insert_self _ _)
    · exact mem_fibersAbove.mpr (Finset.mem_insert_of_mem
        (mem_projectionSupport.mpr ⟨w.2, hw⟩))

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- A link vertex outside the occupied support is a compatible third base
vertex. -/
noncomputable def twoFiberThirdOfLinkVertex
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (u : (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex F)
    (hu : u.1.1 ∉ projectionSupport F) :
    CompatibleThirdVertex base.complex (projectionSupport F) := by
  refine ⟨u.1.1, hu, ?_⟩
  obtain ⟨_hcard, tau, htau, hcompatible⟩ :=
    (lifted_isFace_iff base d hdimension hd hm (insert u.1 F)).mp u.2.2
  refine ⟨tau, htau, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha⟩ := mem_projectionSupport.mp hx
    exact mem_fibersAbove.mp (hcompatible (Finset.mem_insert_of_mem ha))
  · exact mem_fibersAbove.mp (hcompatible (Finset.mem_insert_self _ _))

/-- First classify an actual link vertex by its base fiber, retaining its
original label. -/
noncomputable def concreteTwoFiberSemanticEquiv
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 2) :
    (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex F ≃
      TwoFiberRemainingLabel F (twoSupportBase F hsupport 0) ⊕
        (TwoFiberRemainingLabel F (twoSupportBase F hsupport 1) ⊕
          (CompatibleThirdVertex base.complex (projectionSupport F) × A)) := by
  let x := twoSupportBase F hsupport 0
  let y := twoSupportBase F hsupport 1
  refine {
    toFun := fun u ↦ if hx : u.1.1 = x then
        Sum.inl ⟨u.1.2, ?_⟩
      else if hy : u.1.1 = y then
        Sum.inr (Sum.inl ⟨u.1.2, ?_⟩)
      else
        Sum.inr (Sum.inr
          (twoFiberThirdOfLinkVertex base d hdimension hd hm F u ?_, u.1.2))
    invFun := fun q ↦ match q with
      | Sum.inl a =>
          ⟨(x, a.1), a.2,
            twoFiber_insert_occupied_isFace base d hdimension hd hm F hF hFcard
              (twoSupportBase_mem F hsupport 0) a.2⟩
      | Sum.inr (Sum.inl a) =>
          ⟨(y, a.1), a.2,
            twoFiber_insert_occupied_isFace base d hdimension hd hm F hF hFcard
              (twoSupportBase_mem F hsupport 1) a.2⟩
      | Sum.inr (Sum.inr (z, a)) =>
          ⟨(z.1, a),
            (twoFiber_insert_third_isFace base d hdimension hd hm F hFcard
              hsupport z a).1,
            (twoFiber_insert_third_isFace base d hdimension hd hm F hFcard
              hsupport z a).2⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro hmem
    apply u.2.1
    have hp : (x, u.1.2) = u.1 := Prod.ext hx.symm rfl
    rwa [← hp]
  · intro hmem
    apply u.2.1
    have hp : (y, u.1.2) = u.1 := Prod.ext hy.symm rfl
    rwa [← hp]
  · intro huSupport
    rw [mem_projectionSupport_iff_twoSupportBase F hsupport] at huSupport
    exact huSupport.elim hx hy
  · intro u
    by_cases hx : u.1.1 = x
    · simp only [dif_pos hx]
      apply Subtype.ext
      exact Prod.ext hx.symm rfl
    · simp only [dif_neg hx]
      by_cases hy : u.1.1 = y
      · simp only [dif_pos hy]
        apply Subtype.ext
        exact Prod.ext hy.symm rfl
      · simp only [dif_neg hy]
        apply Subtype.ext
        rfl
  · intro q
    rcases q with a | q
    · simp only [dif_pos trivial]
      congr 2
    · rcases q with a | ⟨z, a⟩
      · have hyx : y ≠ x := by
          intro h
          have hfin : (1 : Fin 2) = 0 :=
            (twoSupportBase_injective F hsupport) h
          omega
        simp only [dif_neg hyx, dif_pos trivial]
        congr 2
      · have hzx : z.1 ≠ x := fun h ↦ z.2.1 (h ▸ twoSupportBase_mem F hsupport 0)
        have hzy : z.1 ≠ y := fun h ↦ z.2.1 (h ▸ twoSupportBase_mem F hsupport 1)
        simp only [dif_neg hzx, dif_neg hzy]
        congr 2

/-- The concrete link-vertex enumeration for a two-point support, with each
finite label set replaced by the `Fin` type used in the canonical model. -/
noncomputable def concreteTwoFiberLinkEquiv
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 2) :
    (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex F ≃
      TwoFiberVertex
        (CompatibleThirdVertex base.complex (projectionSupport F))
        (Fintype.card A)
        (concreteTwoOccupancy F hsupport 0)
        (concreteTwoOccupancy F hsupport 1) := by
  let ex := twoFiberRemainingLabelEquivFin F (twoSupportBase F hsupport 0)
  let ey := twoFiberRemainingLabelEquivFin F (twoSupportBase F hsupport 1)
  let ea : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
  exact (concreteTwoFiberSemanticEquiv base d hdimension hd hm F hF hFcard
    hsupport).trans
      (Equiv.sumCongr ex (Equiv.sumCongr ey (Equiv.prodCongr (Equiv.refl _) ea)))

/-- Assemble the numerical data consumed by the canonical two-fiber model. -/
noncomputable def concreteTwoFiberData
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 2) :
    TwoFiberData
      (CompatibleThirdVertex base.complex (projectionSupport F))
      d (Fintype.card A)
      (concreteTwoOccupancy F hsupport 0)
      (concreteTwoOccupancy F hsupport 1) := by
  letI : Nonempty (CompatibleThirdVertex base.complex (projectionSupport F)) := by
    apply compatibleThirdVertex_nonempty_of_isFace base.complex hdimension _ hsupport
    obtain ⟨_hcard, tau, htau, hcompatible⟩ :=
      (lifted_isFace_iff base d hdimension (by omega) hm F).mp hF
    exact ⟨tau, htau, projectionSupport_subset_of_compatible hcompatible⟩
  exact {
    hd := hd
    hm := hm
    ha := concreteTwoOccupancy_pos F hsupport 0
    hb := concreteTwoOccupancy_pos F hsupport 1
    occupancy_sum := by
      have hsum := concreteTwoOccupancy_sum F hsupport
      simp only [Fin.sum_univ_two] at hsum
      omega
    omega := concreteTwoOmega base.complex (projectionSupport F)
    omega_pos := concreteTwoOmega_pos base.complex hdimension _ hsupport
    omega_sum := concreteTwoOmega_sum base.complex hdimension _ hsupport
  }

/-- The common positive factor left after cancelling the two inserted-fiber
weights in every two-support edge. -/
noncomputable def concreteTwoFiberCommonScale
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (F : Finset (Gamma × A)) : ℝ :=
  compatibleThirdMass base.complex (projectionSupport F) *
      (∏ x ∈ projectionSupport F,
        g (Fintype.card A) (occupancy F x)) /
    normalizer (A := A) base.complex d

theorem concreteTwoFiberCommonScale_pos
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hsupport : (projectionSupport F).card = 2) :
    0 < concreteTwoFiberCommonScale base d F := by
  letI : Nonempty (CompatibleThirdVertex base.complex (projectionSupport F)) := by
    apply compatibleThirdVertex_nonempty_of_isFace base.complex hdimension _ hsupport
    exact projectionSupport_isFace base d hdimension (by omega) hm F hF
  unfold concreteTwoFiberCommonScale
  apply div_pos
  · apply mul_pos
    · exact compatibleThirdMass_pos base.complex hdimension _ hsupport
    · apply Finset.prod_pos
      intro x hx
      apply g_pos
      · exact (occupancy_pos_iff F x).mpr (mem_projectionSupport.mp hx)
      · exact occupancy_le_card F x
  · exact normalizer_pos base.complex d hdimension (by omega) hm

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- No base triangle can contain a support with more than three points. -/
theorem compatibleParentMass_eq_zero_of_three_lt_card
    (X : MeasuredComplex Gamma) (hdimension : X.dim = 2)
    (S : Finset Gamma) (hS : 3 < S.card) :
    compatibleParentMass X S = 0 := by
  classical
  unfold compatibleParentMass
  apply Finset.sum_eq_zero
  intro tau htau
  rw [if_neg]
  intro hsubset
  have hcard := Finset.card_le_card hsubset
  have htauCard : tau.card = 3 := by
    simpa [hdimension] using X.top_card tau htau
  omega

/-- Exact scaled weight when both endpoints lie over the occupied support. -/
theorem concreteTwoLink_weight_occupied_occupied
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 2)
    (u v : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).LinkVertex F)
    (huSupport : u.1.1 ∈ projectionSupport F)
    (hvSupport : v.1.1 ∈ projectionSupport F) (huv : u ≠ v) :
    ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).weight u v =
      concreteTwoFiberCommonScale base d F *
        (if u.1.1 = v.1.1 then
          ((occupancy F u.1.1 : ℝ) * (occupancy F u.1.1 + 1 : ℕ)) /
            (((Fintype.card A : ℝ) - occupancy F u.1.1) *
              ((Fintype.card A : ℝ) - occupancy F u.1.1 - 1))
        else
          ((occupancy F u.1.1 : ℝ) * (occupancy F v.1.1 : ℝ)) /
            (((Fintype.card A : ℝ) - occupancy F u.1.1) *
              ((Fintype.card A : ℝ) - occupancy F v.1.1))) := by
  classical
  have huvValue : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
  have hproj : projectionSupport (insert v.1 (insert u.1 F)) =
      projectionSupport F :=
    projectionSupport_insert_insert_eq F u.1 v.1 huSupport hvSupport
  have hproduct := g_product_insert_insert_existing F u.1 v.1
    u.2.1 v.2.1 huvValue huSupport hvSupport
  have hratio := sequential_occupancy_ratio_eq F u.1 v.1 u.2.1
  rw [concreteOneFiberLink_weight_factorized base d hdimension (by omega) hm
    F hFcard u v huv]
  rw [hproj, hsupport,
    compatibleParentMass_eq_compatibleThirdMass base.complex hdimension _ hsupport]
  simp only [show gamma d 2 = 1 by simp [gamma], one_mul]
  rw [hproduct, hratio]
  unfold concreteTwoFiberCommonScale
  ring

/-- Exact scaled weight between an occupied fiber and a compatible third
fiber. -/
theorem concreteTwoLink_weight_occupied_third
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 2)
    (u v : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).LinkVertex F)
    (huSupport : u.1.1 ∈ projectionSupport F)
    (z : CompatibleThirdVertex base.complex (projectionSupport F))
    (hv : v.1.1 = z.1) :
    ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).weight u v =
      concreteTwoFiberCommonScale base d F *
        ((occupancy F u.1.1 : ℝ) * concreteTwoOmega base.complex
            (projectionSupport F) z /
          (((Fintype.card A : ℝ) - occupancy F u.1.1) *
            (Fintype.card A : ℝ))) := by
  classical
  have huv : u ≠ v := by
    intro h
    have : u.1.1 = z.1 := h ▸ hv
    exact z.2.1 (this ▸ huSupport)
  have huvValue : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
  have hsupportU : projectionSupport (insert u.1 F) = projectionSupport F :=
    projectionSupport_insert_eq F u.1 huSupport
  have hvFresh : v.1 ∉ insert u.1 F := by
    simp [v.2.1, Ne.symm huvValue]
  have hvNotU : v.1.1 ∉ projectionSupport (insert u.1 F) := by
    rw [hsupportU]
    intro hmem
    exact z.2.1 (by rwa [← hv])
  have hnew := g_product_insert_new (insert u.1 F) v.1.1 v.1.2
    hvFresh hvNotU
  change (∏ y ∈ projectionSupport (insert v.1 (insert u.1 F)),
      g (Fintype.card A) (occupancy (insert v.1 (insert u.1 F)) y)) = _ at hnew
  rw [hsupportU] at hnew
  have hexisting := g_product_insert_existing F u.1.1 u.1.2 u.2.1 huSupport
  have hproj : projectionSupport (insert v.1 (insert u.1 F)) =
      insert z.1 (projectionSupport F) := by
    rw [projectionSupport_insert, hv, hsupportU]
  have hcard : (projectionSupport (insert v.1 (insert u.1 F))).card = 3 := by
    rw [hproj, Finset.card_insert_of_notMem z.2.1, hsupport]
  rw [concreteOneFiberLink_weight_factorized base d hdimension (by omega) hm
    F hFcard u v huv]
  rw [hcard]
  simp only [show gamma d 3 = 1 by simp [gamma], one_mul]
  rw [hnew, hexisting, hproj,
    compatibleParentMass_eq_topWeight_of_mem base.complex hdimension _
      (compatibleThirdVertex_parent_mem base.complex hdimension _ hsupport z)]
  unfold concreteTwoFiberCommonScale concreteTwoOmega
  have hmass : compatibleThirdMass base.complex (projectionSupport F) ≠ 0 := by
    apply ne_of_gt
    letI : Nonempty (CompatibleThirdVertex base.complex (projectionSupport F)) := by
      apply compatibleThirdVertex_nonempty_of_isFace base.complex hdimension _ hsupport
      exact projectionSupport_isFace base d hdimension (by omega) hm F hF
    exact compatibleThirdMass_pos base.complex hdimension _ hsupport
  field_simp [hmass]

/-- The reverse occupied/third orientation has the same formula. -/
theorem concreteTwoLink_weight_third_occupied
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 2)
    (u v : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).LinkVertex F)
    (z : CompatibleThirdVertex base.complex (projectionSupport F))
    (hu : u.1.1 = z.1) (hvSupport : v.1.1 ∈ projectionSupport F) :
    ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).weight u v =
      concreteTwoFiberCommonScale base d F *
        ((occupancy F v.1.1 : ℝ) * concreteTwoOmega base.complex
            (projectionSupport F) z /
          (((Fintype.card A : ℝ) - occupancy F v.1.1) *
            (Fintype.card A : ℝ))) := by
  rw [WeightedGraph.weight_symm]
  exact concreteTwoLink_weight_occupied_third base d hdimension hd hm F hF hFcard
    hsupport v u hvSupport z hu

/-- Exact scaled weight between two different labels over the same compatible
third base vertex. -/
theorem concreteTwoLink_weight_third_same
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 2)
    (u v : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).LinkVertex F)
    (z : CompatibleThirdVertex base.complex (projectionSupport F))
    (hu : u.1.1 = z.1) (hv : v.1.1 = z.1) (huv : u ≠ v) :
    ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).weight u v =
      concreteTwoFiberCommonScale base d F *
        (concreteTwoOmega base.complex (projectionSupport F) z /
          ((Fintype.card A : ℝ) * (Fintype.card A - 1 : ℕ))) := by
  classical
  have huvValue : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
  have huNot : u.1.1 ∉ projectionSupport F := by
    intro hmem
    exact z.2.1 (by rwa [← hu])
  have hfirst := g_product_insert_new F u.1.1 u.1.2 u.2.1 huNot
  have hsupportU : projectionSupport (insert u.1 F) =
      insert z.1 (projectionSupport F) := by rw [projectionSupport_insert, hu]
  rw [hsupportU] at hfirst
  have hvFresh : v.1 ∉ insert u.1 F := by
    simp [v.2.1, Ne.symm huvValue]
  have hvSupportU : v.1.1 ∈ projectionSupport (insert u.1 F) := by
    rw [hsupportU, hv]
    exact Finset.mem_insert_self _ _
  have hsecond := g_product_insert_existing (insert u.1 F) v.1.1 v.1.2
    hvFresh hvSupportU
  have hoccZero : occupancy F z.1 = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact z.2.1 (mem_projectionSupport.mpr ((occupancy_pos_iff F z.1).mp hpos))
  have hoccOne : occupancy (insert u.1 F) v.1.1 = 1 := by
    rw [occupancy_insert_of_notMem F u.1 u.2.1 v.1.1, hu, hv, hoccZero]
    simp
  have hproj : projectionSupport (insert v.1 (insert u.1 F)) =
      insert z.1 (projectionSupport F) := by
    rw [projectionSupport_insert_eq (insert u.1 F) v.1 hvSupportU, hsupportU]
  rw [hsupportU] at hsecond
  have hcard : (projectionSupport (insert v.1 (insert u.1 F))).card = 3 := by
    rw [hproj, Finset.card_insert_of_notMem z.2.1, hsupport]
  rw [concreteOneFiberLink_weight_factorized base d hdimension (by omega) hm
    F hFcard u v huv, hcard]
  simp only [show gamma d 3 = 1 by simp [gamma], one_mul]
  rw [hproj, hsecond, hoccOne, hfirst,
    compatibleParentMass_eq_topWeight_of_mem base.complex hdimension _
      (compatibleThirdVertex_parent_mem base.complex hdimension _ hsupport z)]
  unfold concreteTwoFiberCommonScale concreteTwoOmega
  have hmass : compatibleThirdMass base.complex (projectionSupport F) ≠ 0 := by
    apply ne_of_gt
    letI : Nonempty (CompatibleThirdVertex base.complex (projectionSupport F)) := by
      apply compatibleThirdVertex_nonempty_of_isFace base.complex hdimension _ hsupport
      exact projectionSupport_isFace base d hdimension (by omega) hm F hF
    exact compatibleThirdMass_pos base.complex hdimension _ hsupport
  have hmpos : 0 < Fintype.card A := by omega
  norm_num only [Nat.cast_one]
  rw [Nat.cast_sub (show 1 ≤ Fintype.card A by omega)]
  field_simp [hmass]
  <;> ring

/-- Distinct compatible third vertices cannot occur together in a base
triangle, so their lifted edge weight is zero. -/
theorem concreteTwoLink_weight_third_distinct
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 2)
    (u v : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).LinkVertex F)
    (z w : CompatibleThirdVertex base.complex (projectionSupport F))
    (hu : u.1.1 = z.1) (hv : v.1.1 = w.1) (hzw : z ≠ w) :
    ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).weight u v = 0 := by
  classical
  have hzwVal : z.1 ≠ w.1 := fun h ↦ hzw (Subtype.ext h)
  have huv : u ≠ v := by
    intro h
    have hbase : u.1.1 = v.1.1 := congrArg (fun q ↦ q.1.1) h
    exact hzwVal (hu.symm.trans (hbase.trans hv))
  have hproj : projectionSupport (insert v.1 (insert u.1 F)) =
      insert w.1 (insert z.1 (projectionSupport F)) := by
    simp [hu, hv]
  have hwNot : w.1 ∉ insert z.1 (projectionSupport F) := by
    simp [w.2.1, Ne.symm hzwVal]
  have hcard : (projectionSupport (insert v.1 (insert u.1 F))).card = 4 := by
    rw [hproj, Finset.card_insert_of_notMem hwNot,
      Finset.card_insert_of_notMem z.2.1, hsupport]
  rw [concreteOneFiberLink_weight_factorized base d hdimension (by omega) hm
    F hFcard u v huv]
  rw [compatibleParentMass_eq_zero_of_three_lt_card base.complex hdimension _
    (by omega : 3 < (projectionSupport (insert v.1 (insert u.1 F))).card)]
  ring

theorem concreteTwoFiberLinkEquiv_symm_left_fst
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 2)
    (i : Fin (Fintype.card A - concreteTwoOccupancy F hsupport 0)) :
    ((concreteTwoFiberLinkEquiv base d hdimension hd hm F hF hFcard hsupport).symm
      (Sum.inl i)).1.1 = twoSupportBase F hsupport 0 := by
  rfl

theorem concreteTwoFiberLinkEquiv_symm_right_fst
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 2)
    (i : Fin (Fintype.card A - concreteTwoOccupancy F hsupport 1)) :
    ((concreteTwoFiberLinkEquiv base d hdimension hd hm F hF hFcard hsupport).symm
      (Sum.inr (Sum.inl i))).1.1 = twoSupportBase F hsupport 1 := by
  rfl

theorem concreteTwoFiberLinkEquiv_symm_third_fst
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 2)
    (z : CompatibleThirdVertex base.complex (projectionSupport F))
    (i : Fin (Fintype.card A)) :
    ((concreteTwoFiberLinkEquiv base d hdimension hd hm F hF hFcard hsupport).symm
      (Sum.inr (Sum.inr (z, i)))).1.1 = z.1 := by
  rfl

theorem concreteTwo_cast_remaining
    (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 2) (k : Fin 2) :
    (Fintype.card A : ℝ) - occupancy F (twoSupportBase F hsupport k) =
      (Fintype.card A - concreteTwoOccupancy F hsupport k : ℕ) := by
  apply cast_card_sub_occupancy_eq
  exact Nat.add_sub_of_le (occupancy_le_card F _)

theorem concreteTwo_cast_remaining_sub_one
    (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 2) (k : Fin 2)
    (hn : 1 ≤ Fintype.card A - concreteTwoOccupancy F hsupport k) :
    (Fintype.card A : ℝ) - occupancy F (twoSupportBase F hsupport k) - 1 =
      (Fintype.card A - concreteTwoOccupancy F hsupport k - 1 : ℕ) := by
  apply cast_card_sub_occupancy_sub_one_eq
  · exact Nat.add_sub_of_le (occupancy_le_card F _)
  · exact hn

/-- Every concrete two-support link weight is the corresponding canonical
two-fiber weight times one common positive scalar. -/
theorem concreteTwoFiberLink_weight_eq
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 2)
    (u v : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).LinkVertex F) :
    ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).weight u v =
      concreteTwoFiberCommonScale base d F *
        twoFiberEdgeWeight
          (concreteTwoFiberData base d hdimension hd hm F hF hFcard hsupport)
          (concreteTwoFiberLinkEquiv base d hdimension (by omega) hm F hF hFcard hsupport u)
          (concreteTwoFiberLinkEquiv base d hdimension (by omega) hm F hF hFcard hsupport v) := by
  classical
  let e := concreteTwoFiberLinkEquiv base d hdimension (by omega) hm F hF hFcard hsupport
  let D := concreteTwoFiberData base d hdimension hd hm F hF hFcard hsupport
  suffices H : ∀ p q,
      ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).weight
          (e.symm p) (e.symm q) =
        concreteTwoFiberCommonScale base d F * twoFiberEdgeWeight D p q by
    simpa [e, D] using H (e u) (e v)
  intro p q
  by_cases hpq : p = q
  · subst q
    rw [WeightedGraph.weight_self]
    rw [twoFiberEdgeWeight_self, mul_zero]
  have huv : e.symm p ≠ e.symm q := fun h ↦ hpq (e.symm.injective h)
  rcases p with i | p
  · rcases q with j | q
    · have hbaseI := concreteTwoFiberLinkEquiv_symm_left_fst base d hdimension
        (by omega) hm F hF hFcard hsupport i
      have hbaseJ := concreteTwoFiberLinkEquiv_symm_left_fst base d hdimension
        (by omega) hm F hF hFcard hsupport j
      have hij : i ≠ j := fun h ↦ hpq (by rw [h])
      rw [concreteTwoLink_weight_occupied_occupied base d hdimension hd hm F hFcard
        hsupport (e.symm (Sum.inl i)) (e.symm (Sum.inl j))
        (hbaseI ▸ twoSupportBase_mem F hsupport 0)
        (hbaseJ ▸ twoSupportBase_mem F hsupport 0) huv]
      have hn : 1 ≤ Fintype.card A - concreteTwoOccupancy F hsupport 0 := by
        have := i.isLt
        omega
      rw [hbaseI, hbaseJ, concreteTwo_cast_remaining_sub_one F hsupport 0 hn,
        concreteTwo_cast_remaining F hsupport 0]
      simp [twoFiberEdgeWeight, D, concreteTwoFiberData, concreteTwoOccupancy, hij]
      exact fun h ↦ (hij h).elim
    · rcases q with j | ⟨z, j⟩
      · have hbaseI := concreteTwoFiberLinkEquiv_symm_left_fst base d hdimension
          (by omega) hm F hF hFcard hsupport i
        have hbaseJ := concreteTwoFiberLinkEquiv_symm_right_fst base d hdimension
          (by omega) hm F hF hFcard hsupport j
        have hxy : twoSupportBase F hsupport 0 ≠ twoSupportBase F hsupport 1 := by
          intro h
          have : (0 : Fin 2) = 1 := twoSupportBase_injective F hsupport h
          omega
        have hactual :
            (e.symm (Sum.inl i)).1.1 ≠ (e.symm (Sum.inr (Sum.inl j))).1.1 := by
          rw [hbaseI, hbaseJ]
          exact hxy
        rw [concreteTwoLink_weight_occupied_occupied base d hdimension hd hm F hFcard
          hsupport (e.symm (Sum.inl i)) (e.symm (Sum.inr (Sum.inl j)))
          (hbaseI ▸ twoSupportBase_mem F hsupport 0)
          (hbaseJ ▸ twoSupportBase_mem F hsupport 1) huv,
          if_neg hactual, hbaseI, hbaseJ,
          concreteTwo_cast_remaining F hsupport 0,
          concreteTwo_cast_remaining F hsupport 1]
        simp [twoFiberEdgeWeight, D, concreteTwoFiberData, concreteTwoOccupancy]
      · have hbaseI := concreteTwoFiberLinkEquiv_symm_left_fst base d hdimension
          (by omega) hm F hF hFcard hsupport i
        have hbaseJ := concreteTwoFiberLinkEquiv_symm_third_fst base d hdimension
          (by omega) hm F hF hFcard hsupport z j
        rw [concreteTwoLink_weight_occupied_third base d hdimension hd hm F hF hFcard
          hsupport (e.symm (Sum.inl i)) (e.symm (Sum.inr (Sum.inr (z, j))))
          (hbaseI ▸ twoSupportBase_mem F hsupport 0) z hbaseJ,
          hbaseI, concreteTwo_cast_remaining F hsupport 0]
        simp [twoFiberEdgeWeight, D, concreteTwoFiberData, concreteTwoOccupancy]
  · rcases p with i | ⟨z, i⟩
    · rcases q with j | q
      · have hbaseI := concreteTwoFiberLinkEquiv_symm_right_fst base d hdimension
          (by omega) hm F hF hFcard hsupport i
        have hbaseJ := concreteTwoFiberLinkEquiv_symm_left_fst base d hdimension
          (by omega) hm F hF hFcard hsupport j
        have hxy : twoSupportBase F hsupport 1 ≠ twoSupportBase F hsupport 0 := by
          intro h
          have : (1 : Fin 2) = 0 := twoSupportBase_injective F hsupport h
          omega
        have hactual :
            (e.symm (Sum.inr (Sum.inl i))).1.1 ≠ (e.symm (Sum.inl j)).1.1 := by
          rw [hbaseI, hbaseJ]
          exact hxy
        rw [concreteTwoLink_weight_occupied_occupied base d hdimension hd hm F hFcard
          hsupport (e.symm (Sum.inr (Sum.inl i))) (e.symm (Sum.inl j))
          (hbaseI ▸ twoSupportBase_mem F hsupport 1)
          (hbaseJ ▸ twoSupportBase_mem F hsupport 0) huv,
          if_neg hactual, hbaseI, hbaseJ,
          concreteTwo_cast_remaining F hsupport 1,
          concreteTwo_cast_remaining F hsupport 0]
        simp [twoFiberEdgeWeight, D, concreteTwoFiberData, concreteTwoOccupancy]
        exact Or.inl (by ring)
      · rcases q with j | ⟨w, j⟩
        · have hbaseI := concreteTwoFiberLinkEquiv_symm_right_fst base d hdimension
            (by omega) hm F hF hFcard hsupport i
          have hbaseJ := concreteTwoFiberLinkEquiv_symm_right_fst base d hdimension
            (by omega) hm F hF hFcard hsupport j
          have hij : i ≠ j := fun h ↦ hpq (by rw [h])
          have hn : 1 ≤ Fintype.card A - concreteTwoOccupancy F hsupport 1 := by
            have := i.isLt
            omega
          rw [concreteTwoLink_weight_occupied_occupied base d hdimension hd hm F hFcard
            hsupport (e.symm (Sum.inr (Sum.inl i)))
            (e.symm (Sum.inr (Sum.inl j)))
            (hbaseI ▸ twoSupportBase_mem F hsupport 1)
            (hbaseJ ▸ twoSupportBase_mem F hsupport 1) huv,
            hbaseI, hbaseJ, concreteTwo_cast_remaining_sub_one F hsupport 1 hn,
            concreteTwo_cast_remaining F hsupport 1]
          simp [twoFiberEdgeWeight, D, concreteTwoFiberData, concreteTwoOccupancy, hij]
          exact fun h ↦ (hij h).elim
        · have hbaseI := concreteTwoFiberLinkEquiv_symm_right_fst base d hdimension
            (by omega) hm F hF hFcard hsupport i
          have hbaseJ := concreteTwoFiberLinkEquiv_symm_third_fst base d hdimension
            (by omega) hm F hF hFcard hsupport w j
          rw [concreteTwoLink_weight_occupied_third base d hdimension hd hm F hF hFcard
            hsupport (e.symm (Sum.inr (Sum.inl i)))
            (e.symm (Sum.inr (Sum.inr (w, j))))
            (hbaseI ▸ twoSupportBase_mem F hsupport 1) w hbaseJ,
            hbaseI, concreteTwo_cast_remaining F hsupport 1]
          simp [twoFiberEdgeWeight, D, concreteTwoFiberData, concreteTwoOccupancy]
    · rcases q with j | q
      · have hbaseI := concreteTwoFiberLinkEquiv_symm_third_fst base d hdimension
          (by omega) hm F hF hFcard hsupport z i
        have hbaseJ := concreteTwoFiberLinkEquiv_symm_left_fst base d hdimension
          (by omega) hm F hF hFcard hsupport j
        rw [concreteTwoLink_weight_third_occupied base d hdimension hd hm F hF hFcard
          hsupport (e.symm (Sum.inr (Sum.inr (z, i)))) (e.symm (Sum.inl j)) z
          hbaseI (hbaseJ ▸ twoSupportBase_mem F hsupport 0)]
        rw [hbaseJ, concreteTwo_cast_remaining F hsupport 0]
        simp [twoFiberEdgeWeight, D, concreteTwoFiberData, concreteTwoOccupancy]
      · rcases q with j | ⟨w, j⟩
        · have hbaseI := concreteTwoFiberLinkEquiv_symm_third_fst base d hdimension
            (by omega) hm F hF hFcard hsupport z i
          have hbaseJ := concreteTwoFiberLinkEquiv_symm_right_fst base d hdimension
            (by omega) hm F hF hFcard hsupport j
          rw [concreteTwoLink_weight_third_occupied base d hdimension hd hm F hF hFcard
            hsupport (e.symm (Sum.inr (Sum.inr (z, i))))
            (e.symm (Sum.inr (Sum.inl j))) z hbaseI
            (hbaseJ ▸ twoSupportBase_mem F hsupport 1),
            hbaseJ, concreteTwo_cast_remaining F hsupport 1]
          simp [twoFiberEdgeWeight, D, concreteTwoFiberData, concreteTwoOccupancy]
        · by_cases hzw : z = w
          · subst w
            have hbaseI := concreteTwoFiberLinkEquiv_symm_third_fst base d hdimension
              (by omega) hm F hF hFcard hsupport z i
            have hbaseJ := concreteTwoFiberLinkEquiv_symm_third_fst base d hdimension
              (by omega) hm F hF hFcard hsupport z j
            rw [concreteTwoLink_weight_third_same base d hdimension hd hm F hF hFcard
              hsupport (e.symm (Sum.inr (Sum.inr (z, i))))
              (e.symm (Sum.inr (Sum.inr (z, j)))) z hbaseI hbaseJ huv]
            have hij : i ≠ j := fun h ↦ hpq (by rw [h])
            simp [twoFiberEdgeWeight, D, concreteTwoFiberData, hij]
          · rw [concreteTwoLink_weight_third_distinct base d hdimension hd hm F hFcard
              hsupport (e.symm (Sum.inr (Sum.inr (z, i))))
              (e.symm (Sum.inr (Sum.inr (w, j)))) z w
              (concreteTwoFiberLinkEquiv_symm_third_fst base d hdimension
                (by omega) hm F hF hFcard hsupport z i)
              (concreteTwoFiberLinkEquiv_symm_third_fst base d hdimension
                (by omega) hm F hF hFcard hsupport w j) hzw]
            simp [twoFiberEdgeWeight, hzw]

/-- The actual link over a two-point projection support, together with its
explicit enumeration and positive common edge-weight scale. -/
noncomputable def concreteTwoFiberLinkCertificate
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 2) :
    TwoFiberLinkCertificate
      ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F)
      (CompatibleThirdVertex base.complex (projectionSupport F)) d (Fintype.card A)
      (concreteTwoOccupancy F hsupport 0) (concreteTwoOccupancy F hsupport 1) where
  data := concreteTwoFiberData base d hdimension hd hm F hF hFcard hsupport
  enumerate := concreteTwoFiberLinkEquiv base d hdimension (by omega) hm F hF hFcard hsupport
  commonScale := concreteTwoFiberCommonScale base d F
  commonScale_pos := concreteTwoFiberCommonScale_pos
    base d hdimension hd hm F hF hsupport
  relabel_eq := by
    apply WeightedGraph.ext_weight
    intro u v
    rw [WeightedGraph.relabel_weight]
    change _ = concreteTwoFiberCommonScale base d F *
      twoFiberEdgeWeight
        (concreteTwoFiberData base d hdimension hd hm F hF hFcard hsupport)
        (concreteTwoFiberLinkEquiv base d hdimension (by omega) hm F hF hFcard hsupport u)
        (concreteTwoFiberLinkEquiv base d hdimension (by omega) hm F hF hFcard hsupport v)
    exact concreteTwoFiberLink_weight_eq
      base d hdimension hd hm F hF hFcard hsupport u v

/-- Every actual two-support codimension-two link satisfies the sharp
canonical two-fiber `1 / d` bound. -/
theorem concreteTwoFiberLink_twoSidedSpectralBound
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 2) :
    WeightedGraph.TwoSidedSpectralBound
      ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F)
      (1 / (d : ℝ)) := by
  exact TwoFiberLinkCertificate.twoSidedSpectralBound
    (concreteTwoFiberLinkCertificate base d hdimension hd hm F hF hFcard hsupport)
      (twoFiberGraph_twoSidedSpectralBound
        (concreteTwoFiberData base d hdimension hd hm F hF hFcard hsupport))

/-- The complete `r(F)=2` row of the conditioned-link table. -/
theorem occupancyCaseBound_two
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) :
    OccupancyCaseBound (A := A) base d hdimension hd hm 2 := by
  intro F hF hFcard hsupport
  exact concreteTwoFiberLink_twoSidedSpectralBound
    base d hdimension hd hm F hF hFcard hsupport

end WeightedLift

end HDXLean
