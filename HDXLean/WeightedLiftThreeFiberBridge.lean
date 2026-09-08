import HDXLean.WeightedLiftThreeFiber
import HDXLean.WeightedLiftOccupancy
import HDXLean.ConditionedLinkWeights
import HDXLean.WeightedLiftParentSums
import HDXLean.WeightedLiftInsertion

/-!
# Concrete bridge for the three-fiber conditioned link

This file identifies an actual codimension-two link of the weighted lift with
the canonical three-fiber graph whenever the conditioned face meets all three
base fibers.  In particular, it proves that the concrete link weights differ
from the canonical weights by one common positive scalar and transfers the
complete `1 / d` bound.
-/

namespace HDXLean

open scoped BigOperators

namespace WeightedLift

variable {Gamma A : Type*}
  [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma] [DecidableEq Gamma]
  [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A]

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- In the three-fiber case the projection support itself is the unique base
triangle containing the conditioned face. -/
theorem projectionSupport_mem_topFaces_of_card_three
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hsupport : (projectionSupport F).card = 3) :
    projectionSupport F ∈ base.complex.topFaces := by
  obtain ⟨_hcard, tau, htau, hcompatible⟩ :=
    (lifted_isFace_iff base d hdimension hd hm F).mp hF
  have hsubset : projectionSupport F ⊆ tau := by
    intro x hx
    obtain ⟨a, ha⟩ := mem_projectionSupport.mp hx
    exact mem_fibersAbove.mp (hcompatible ha)
  have htauCard : tau.card = 3 := by
    simpa [hdimension] using base.complex.top_card tau htau
  have heq : projectionSupport F = tau :=
    Finset.eq_of_subset_of_card_le hsubset (by omega)
  rwa [heq]

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- The conditioned face is compatible with its canonical parent. -/
theorem compatible_projectionSupport (F : Finset (Gamma × A)) :
    CompatibleParent (A := A) (projectionSupport F) F := by
  intro z hz
  exact mem_fibersAbove.mpr
    (mem_projectionSupport.mpr ⟨z.2, hz⟩)

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Every vertex in the concrete link lies over the canonical parent
triangle. -/
theorem linkVertex_fst_mem_projectionSupport
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 3)
    (u : (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex F) :
    u.1.1 ∈ projectionSupport F := by
  obtain ⟨_hcard, tau, htau, hcompatible⟩ :=
    (lifted_isFace_iff base d hdimension hd hm (insert u.1 F)).mp u.2.2
  have htauCard : tau.card = 3 := by
    simpa [hdimension] using base.complex.top_card tau htau
  have hcompatibleF : CompatibleParent (A := A) tau F := by
    intro z hz
    exact hcompatible (Finset.mem_insert_of_mem hz)
  have heq := compatibleParent_eq_projectionSupport_of_card_three
    (A := A) htauCard hsupport hcompatibleF
  rw [← heq]
  exact mem_fibersAbove.mp (hcompatible (Finset.mem_insert_self _ _))

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Conversely, every unused label over the support is a concrete link
vertex. -/
theorem isLinkVertex_of_mem_projectionSupport
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 3)
    {x : Gamma} (hx : x ∈ projectionSupport F)
    {a : A} (ha : (x, a) ∉ F) :
    (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace
      (insert (x, a) F) := by
  rw [lifted_isFace_iff base d hdimension hd hm]
  refine ⟨?_, projectionSupport F, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem ha]
    omega
  · exact projectionSupport_mem_topFaces_of_card_three base d hdimension hd hm
      F hF hsupport
  · intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact mem_fibersAbove.mpr hx
    · exact compatible_projectionSupport F hz

/-- A fixed enumeration of a three-element projection support. -/
noncomputable def supportIndexEquiv (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 3) :
    Fin 3 ≃ {x : Gamma // x ∈ projectionSupport F} :=
  (Equiv.cast (congrArg Fin hsupport.symm)).trans
    (Finset.equivFin (projectionSupport F)).symm

/-- Base vertex carrying the `i`-th occupied fiber. -/
noncomputable def supportBase (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 3) (i : Fin 3) : Gamma :=
  (supportIndexEquiv F hsupport i).1

omit [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma]
    [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A] in
theorem supportBase_mem (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 3) (i : Fin 3) :
    supportBase F hsupport i ∈ projectionSupport F :=
  (supportIndexEquiv F hsupport i).2

omit [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma]
    [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A] in
theorem supportBase_injective (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 3) :
    Function.Injective (supportBase F hsupport) := by
  intro i j hij
  apply (supportIndexEquiv F hsupport).injective
  apply Subtype.ext
  exact hij

/-- The actual occupancy of the enumerated fiber. -/
noncomputable def concreteThreeOccupancy (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 3) (i : Fin 3) : ℕ :=
  occupancy F (supportBase F hsupport i)

/-- Labels not already used by the conditioned face in a fixed fiber. -/
def RemainingLabel (F : Finset (Gamma × A)) (x : Gamma) :=
  {a : A // (x, a) ∉ F}

noncomputable instance (F : Finset (Gamma × A)) (x : Gamma) :
    Fintype (RemainingLabel F x) := by
  letI : Finite (RemainingLabel F x) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance (F : Finset (Gamma × A)) (x : Gamma) :
    DecidableEq (RemainingLabel F x) := Classical.decEq _

/-- Number of unused labels in the enumerated fiber. -/
noncomputable def concreteThreeUnused (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 3) (i : Fin 3) : ℕ :=
  (Finset.univ.filter fun a : A ↦
    (supportBase F hsupport i, a) ∉ F).card

omit [AddCommGroup Gamma] [Module F₂ Gamma]
    [AddCommGroup A] [Module F₂ A] in
/-- Fiber occupancies sum to the cardinality of the lifted face. -/
theorem sum_occupancy_projectionSupport (F : Finset (Gamma × A)) :
    ∑ x ∈ projectionSupport F, occupancy F x = F.card := by
  classical
  have hall : ∑ x : Gamma, occupancy F x = F.card := by
    calc
      (∑ x : Gamma, occupancy F x) =
          ∑ x : Gamma, ∑ a : A, if (x, a) ∈ F then 1 else 0 := by
        unfold occupancy
        apply Finset.sum_congr rfl
        intro x _hx
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = ∑ z : Gamma × A, if z ∈ F then 1 else 0 := by
        rw [Fintype.sum_prod_type]
      _ = F.card := by
        rw [← Finset.sum_filter]
        simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
        rw [← Finset.card_eq_sum_ones]
  calc
    (∑ x ∈ projectionSupport F, occupancy F x) =
        ∑ x : Gamma, occupancy F x := by
      exact Finset.sum_subset (Finset.subset_univ _) (by
      intro x _hx hxnot
      have hzero : ¬∃ a : A, (x, a) ∈ F := by
        simpa [mem_projectionSupport] using hxnot
      exact Nat.eq_zero_of_not_pos
        (fun hpos ↦ hzero ((occupancy_pos_iff F x).mp hpos)))
    _ = F.card := hall

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
theorem concreteThreeOccupancy_sum (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 3) :
    ∑ i : Fin 3, concreteThreeOccupancy F hsupport i = F.card := by
  let e := supportIndexEquiv F hsupport
  calc
    (∑ i : Fin 3, concreteThreeOccupancy F hsupport i) =
        ∑ x : {x : Gamma // x ∈ projectionSupport F}, occupancy F x.1 := by
      exact e.sum_comp (fun x ↦ occupancy F x.1)
    _ = ∑ x ∈ projectionSupport F, occupancy F x := by
      symm
      apply Finset.sum_subtype (projectionSupport F)
      intro x
      rfl
    _ = F.card := sum_occupancy_projectionSupport F

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
theorem concreteThreeOccupancy_pos (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 3) (i : Fin 3) :
    1 ≤ concreteThreeOccupancy F hsupport i := by
  rw [Nat.one_le_iff_ne_zero]
  intro hzero
  have hnot : ¬∃ a : A, (supportBase F hsupport i, a) ∈ F := by
    intro hexists
    have hpos := (occupancy_pos_iff F (supportBase F hsupport i)).mpr hexists
    apply (Nat.ne_of_gt ?_) hzero
    exact hpos
  exact hnot (mem_projectionSupport.mp (supportBase_mem F hsupport i))

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Used and unused labels partition a fiber. -/
theorem concreteThree_fiber_capacity (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 3) (i : Fin 3) :
    concreteThreeOccupancy F hsupport i +
      concreteThreeUnused F hsupport i = Fintype.card A := by
  classical
  let x := supportBase F hsupport i
  let p : A → Prop := fun a ↦ (x, a) ∈ F
  let used : Finset A := Finset.univ.filter p
  let unused : Finset A := Finset.univ.filter fun a ↦ ¬p a
  have hdisjoint : Disjoint used unused := by
    rw [Finset.disjoint_left]
    intro a haUsed haUnused
    exact (Finset.mem_filter.mp haUnused).2 (Finset.mem_filter.mp haUsed).2
  have hunion : used ∪ unused = Finset.univ := by
    ext a
    simp [used, unused, p]
    exact Classical.em ((x, a) ∈ F)
  have hcard := Finset.card_union_of_disjoint hdisjoint
  rw [hunion] at hcard
  change used.card + unused.card = Fintype.card A
  rw [← hcard]
  simp

/-- The unused labels in one fiber are explicitly enumerated by the `Fin`
type used in the canonical model. -/
noncomputable def remainingLabelEquivFin (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 3) (i : Fin 3) :
    RemainingLabel F (supportBase F hsupport i) ≃
      Fin (concreteThreeUnused F hsupport i) := by
  classical
  let x := supportBase F hsupport i
  let U : Finset A := Finset.univ.filter fun a ↦ (x, a) ∉ F
  let eU : RemainingLabel F x ≃ {a : A // a ∈ U} := {
    toFun a := ⟨a.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.2⟩⟩
    invFun a := ⟨a.1, (Finset.mem_filter.mp a.2).2⟩
    left_inv a := by apply Subtype.ext; rfl
    right_inv a := by apply Subtype.ext; rfl
  }
  have hcardU : Fintype.card (RemainingLabel F x) = U.card := by
    calc
      Fintype.card (RemainingLabel F x) = Fintype.card {a : A // a ∈ U} :=
        Fintype.card_congr eU
      _ = U.card := by simp
  have htarget : U.card = concreteThreeUnused F hsupport i := by rfl
  exact (Fintype.equivFin (RemainingLabel F x)).trans
    (Equiv.cast (congrArg Fin (hcardU.trans htarget)))

/-- First identify a concrete link vertex with its base support point and its
unused label. -/
noncomputable def linkVertexSupportEquiv
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 3) :
    (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex F ≃
      Σ x : {x : Gamma // x ∈ projectionSupport F}, RemainingLabel F x.1 where
  toFun u :=
    ⟨⟨u.1.1, linkVertex_fst_mem_projectionSupport
      base d hdimension hd hm F hsupport u⟩, ⟨u.1.2, u.2.1⟩⟩
  invFun z := by
    refine ⟨(z.1.1, z.2.1), z.2.2, ?_⟩
    exact isLinkVertex_of_mem_projectionSupport base d hdimension hd hm F
      hF hFcard hsupport z.1.2 z.2.2
  left_inv u := by
    apply Subtype.ext
    rfl
  right_inv z := by
    rcases z with ⟨x, a⟩
    apply Sigma.ext <;> rfl

/-- Reindex the support-point sigma type by `Fin 3`. -/
noncomputable def indexedSupportEquiv (F : Finset (Gamma × A))
    (hsupport : (projectionSupport F).card = 3) :
    (Σ i : Fin 3, RemainingLabel F (supportBase F hsupport i)) ≃
      Σ x : {x : Gamma // x ∈ projectionSupport F}, RemainingLabel F x.1 :=
  Equiv.sigmaCongr (supportIndexEquiv F hsupport)
    (fun _i ↦ Equiv.refl _)

/-- The concrete link-vertex enumeration used in the scaling certificate. -/
noncomputable def concreteThreeLinkEquiv
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 3) :
    (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex F ≃
      ThreeFiberVertex (concreteThreeUnused F hsupport) :=
  (linkVertexSupportEquiv base d hdimension hd hm F hF hFcard hsupport).trans
    ((indexedSupportEquiv F hsupport).symm.trans
      (Equiv.sigmaCongrRight fun i ↦ remainingLabelEquivFin F hsupport i))

/-- The first coordinate of the canonical enumeration records the original
base fiber of a concrete link vertex. -/
theorem supportBase_concreteThreeLinkEquiv_fst
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 3)
    (u : (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex F) :
    supportBase F hsupport
      (concreteThreeLinkEquiv base d hdimension hd hm F hF hFcard hsupport u).1 = u.1.1 := by
  let L := linkVertexSupportEquiv base d hdimension hd hm F hF hFcard hsupport
  let I := indexedSupportEquiv F hsupport
  let R := Equiv.sigmaCongrRight fun i ↦ remainingLabelEquivFin F hsupport i
  change supportBase F hsupport (R (I.symm (L u))).1 = u.1.1
  have hfirst : (I.symm (L u)).1 = (supportIndexEquiv F hsupport).symm (L u).1 := by
    rfl
  change (supportIndexEquiv F hsupport (R (I.symm (L u))).1).1 = u.1.1
  change (supportIndexEquiv F hsupport (I.symm (L u)).1).1 = u.1.1
  rw [hfirst, Equiv.apply_symm_apply]
  rfl

/-- The two sequential cancellation ratios are exactly the canonical
three-fiber edge weight after enumerating the concrete link vertices. -/
theorem concreteThree_sequentialRatio_eq_weight
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 3)
    (u v : (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex F)
    (huv : u ≠ v) :
    ((occupancy (insert u.1 F) v.1.1 : ℝ) /
          ((Fintype.card A : ℝ) - occupancy (insert u.1 F) v.1.1)) *
        ((occupancy F u.1.1 : ℝ) /
          ((Fintype.card A : ℝ) - occupancy F u.1.1)) =
      threeFiberWeight
        (concreteThreeOccupancy F hsupport)
        (concreteThreeUnused F hsupport)
        (concreteThreeLinkEquiv base d hdimension hd hm F hF hFcard hsupport u)
        (concreteThreeLinkEquiv base d hdimension hd hm F hF hFcard hsupport v) := by
  let eu := concreteThreeLinkEquiv base d hdimension hd hm F hF hFcard hsupport u
  let ev := concreteThreeLinkEquiv base d hdimension hd hm F hF hFcard hsupport v
  have heuv : eu ≠ ev := by
    intro h
    exact huv ((concreteThreeLinkEquiv base d hdimension hd hm F hF hFcard hsupport).injective h)
  have hbaseU : supportBase F hsupport eu.1 = u.1.1 :=
    supportBase_concreteThreeLinkEquiv_fst base d hdimension hd hm F hF hFcard
      hsupport u
  have hbaseV : supportBase F hsupport ev.1 = v.1.1 :=
    supportBase_concreteThreeLinkEquiv_fst base d hdimension hd hm F hF hFcard
      hsupport v
  have hoccU : concreteThreeOccupancy F hsupport eu.1 = occupancy F u.1.1 := by
    unfold concreteThreeOccupancy
    rw [hbaseU]
  have hoccV : concreteThreeOccupancy F hsupport ev.1 = occupancy F v.1.1 := by
    unfold concreteThreeOccupancy
    rw [hbaseV]
  have hcapU := concreteThree_fiber_capacity F hsupport eu.1
  have hcapV := concreteThree_fiber_capacity F hsupport ev.1
  have hnU : 1 ≤ concreteThreeUnused F hsupport eu.1 := by
    have := eu.2.isLt
    omega
  have hnV : 1 ≤ concreteThreeUnused F hsupport ev.1 := by
    have := ev.2.isLt
    omega
  rw [sequential_occupancy_ratio_eq F u.1 v.1 u.2.1]
  change _ = threeFiberWeight _ _ eu ev
  unfold threeFiberWeight
  rw [if_neg heuv]
  by_cases hij : eu.1 = ev.1
  · have hbase : u.1.1 = v.1.1 := by
      rw [← hbaseU, ← hbaseV, hij]
    rw [if_pos hbase, dif_pos hij]
    rw [← hoccU]
    rw [cast_card_sub_occupancy_sub_one_eq hcapU hnU,
      cast_card_sub_occupancy_eq hcapU]
  · have hbase : u.1.1 ≠ v.1.1 := by
      intro huvBase
      apply hij
      apply supportBase_injective F hsupport
      rw [hbaseU, hbaseV, huvBase]
    rw [if_neg hbase, dif_neg hij]
    rw [← hoccU, ← hoccV,
      cast_card_sub_occupancy_eq hcapU,
      cast_card_sub_occupancy_eq hcapV]

/-- In the three-fiber case every distinct concrete link edge is the unique
parent contribution of the enlarged lifted top face. -/
theorem concreteThreeLink_edgeWeight_eq_parentWeight
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 3)
    (u v : (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex F)
    (huv : u ≠ v) :
    ((measuredComplex (A := A) base.complex d hdimension hd hm).linkGraph F).weight u v =
      parentWeight (A := A) base.complex d (projectionSupport F)
        (insert v.1 (insert u.1 F)) /
          normalizer (A := A) base.complex d := by
  let E : Finset (Gamma × A) := insert v.1 (insert u.1 F)
  have huvValue : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
  have hvnot : v.1 ∉ insert u.1 F := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h ↦ huvValue h.symm, v.2.1⟩
  have hEcard : E.card = d + 1 := by
    dsimp [E]
    rw [Finset.card_insert_of_notMem hvnot,
      Finset.card_insert_of_notMem u.2.1, hFcard]
  have htau : projectionSupport F ∈ base.complex.topFaces :=
    projectionSupport_mem_topFaces_of_card_three base d hdimension hd hm F hF hsupport
  have hcompatible : CompatibleParent (A := A) (projectionSupport F) E := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact mem_fibersAbove.mpr
        (linkVertex_fst_mem_projectionSupport base d hdimension hd hm F hsupport v)
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact mem_fibersAbove.mpr
        (linkVertex_fst_mem_projectionSupport base d hdimension hd hm F hsupport u)
    exact compatible_projectionSupport F hz
  have hEtop : E ∈ topFaces (A := A) base.complex d :=
    mem_topFaces.mpr ⟨hEcard, projectionSupport F, htau, hcompatible⟩
  have huSupport : u.1.1 ∈ projectionSupport F :=
    linkVertex_fst_mem_projectionSupport base d hdimension hd hm F hsupport u
  have hvSupport : v.1.1 ∈ projectionSupport F :=
    linkVertex_fst_mem_projectionSupport base d hdimension hd hm F hsupport v
  have hproj : projectionSupport E = projectionSupport F := by
    exact projectionSupport_insert_insert_eq F u.1 v.1 huSupport hvSupport
  change (measuredComplex (A := A) base.complex d hdimension hd hm).linkEdgeWeight F u v = _
  rw [MeasuredComplex.codimensionTwo_linkEdgeWeight_eq_topWeight _ F hFcard u v huv]
  change liftedTopWeight (A := A) base.complex d E = _
  rw [liftedTopWeight_eq base.complex d hEtop]
  have hEsupport : (projectionSupport E).card = 3 := by simpa [hproj] using hsupport
  rw [rawTopWeight_eq_parentWeight_projectionSupport base.complex d hdimension hEtop hEsupport]
  rw [hproj]

/-- The common positive factor left after the two local `g` cancellations. -/
noncomputable def concreteThreeCommonScale
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (F : Finset (Gamma × A)) : ℝ :=
  base.complex.topWeight (projectionSupport F) *
    (∏ x ∈ projectionSupport F, g (Fintype.card A) (occupancy F x)) /
      normalizer (A := A) base.complex d

theorem concreteThreeCommonScale_pos
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hsupport : (projectionSupport F).card = 3) :
    0 < concreteThreeCommonScale base d F := by
  unfold concreteThreeCommonScale
  apply div_pos
  · apply mul_pos
    · exact base.complex.topWeight_pos _
        (projectionSupport_mem_topFaces_of_card_three base d hdimension hd hm F hF hsupport)
    · apply Finset.prod_pos
      intro x hx
      apply g_pos
      · exact (occupancy_pos_iff F x).mpr (mem_projectionSupport.mp hx)
      · exact occupancy_le_card F x
  · exact normalizer_pos base.complex d hdimension hd hm

/-- Equation (5.1), after the two `g_m` cancellations, is exactly one common
positive scalar times the canonical three-fiber edge weight. -/
theorem concreteThreeLink_weight_eq
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 3)
    (u v : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).LinkVertex F) :
    ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).weight u v =
      concreteThreeCommonScale base d F *
        threeFiberWeight
          (concreteThreeOccupancy F hsupport)
          (concreteThreeUnused F hsupport)
          (concreteThreeLinkEquiv base d hdimension (by omega) hm F hF hFcard hsupport u)
          (concreteThreeLinkEquiv base d hdimension (by omega) hm F hF hFcard hsupport v) := by
  classical
  by_cases huv : u = v
  · subst v
    rw [WeightedGraph.weight_self]
    simp [threeFiberWeight]
  · have huvValue : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
    have huSupport : u.1.1 ∈ projectionSupport F :=
      linkVertex_fst_mem_projectionSupport base d hdimension (by omega) hm F hsupport u
    have hvSupport : v.1.1 ∈ projectionSupport F :=
      linkVertex_fst_mem_projectionSupport base d hdimension (by omega) hm F hsupport v
    let E : Finset (Gamma × A) := insert v.1 (insert u.1 F)
    have hproj : projectionSupport E = projectionSupport F := by
      exact projectionSupport_insert_insert_eq F u.1 v.1 huSupport hvSupport
    have hcompatible : CompatibleParent (A := A) (projectionSupport F) E := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact mem_fibersAbove.mpr hvSupport
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact mem_fibersAbove.mpr huSupport
      · exact compatible_projectionSupport F hz
    have hoccupied :
        occupiedSupport (A := A) (projectionSupport F) E = projectionSupport F :=
      (occupiedSupport_eq_projectionSupport hcompatible).trans hproj
    have hproduct := g_product_insert_insert_existing F u.1 v.1
      u.2.1 v.2.1 huvValue huSupport hvSupport
    have hratio := concreteThree_sequentialRatio_eq_weight
      base d hdimension (by omega) hm F hF hFcard hsupport u v huv
    rw [concreteThreeLink_edgeWeight_eq_parentWeight base d hdimension
      (by omega) hm F hF hFcard hsupport u v huv]
    unfold parentWeight concreteThreeCommonScale
    change
      (base.complex.topWeight (projectionSupport F) *
          gamma d (occupiedSupport (A := A) (projectionSupport F) E).card *
          (∏ x ∈ occupiedSupport (A := A) (projectionSupport F) E,
            g (Fintype.card A) (occupancy E x))) /
        normalizer (A := A) base.complex d = _
    rw [hoccupied, hsupport]
    rw [show gamma d 3 = 1 by simp [gamma]]
    simp only [mul_one]
    rw [hproduct, hratio]
    ring

/-- An exact common-factor formula for the concrete link weights supplies the
certificate required by the canonical three-fiber calculation.  This is the
transport step: the equivalence above turns an equality on concrete vertices
into equality of weighted graphs after positive scaling and relabeling. -/
noncomputable def concreteThreeLinkCertificate_of_weight_formula
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 3)
    (commonScale : ℝ) (hcommonScale : 0 < commonScale)
    (hweight : ∀ u v :
      (measuredComplex (A := A) base.complex d hdimension (by omega) hm).LinkVertex F,
      ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).weight u v =
        commonScale * threeFiberWeight
          (concreteThreeOccupancy F hsupport)
          (concreteThreeUnused F hsupport)
          (concreteThreeLinkEquiv base d hdimension (by omega) hm F hF hFcard hsupport u)
          (concreteThreeLinkEquiv base d hdimension (by omega) hm F hF hFcard hsupport v)) :
    ThreeFiberLinkCertificate
      ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F)
      d (Fintype.card A) where
  occupancy := concreteThreeOccupancy F hsupport
  unused := concreteThreeUnused F hsupport
  occupancy_sum := by
    have hsum := concreteThreeOccupancy_sum F hsupport
    omega
  dimension_ge_three := hd
  occupancy_pos := concreteThreeOccupancy_pos F hsupport
  fiber_capacity := concreteThree_fiber_capacity F hsupport
  fiber_size := hm
  enumerate := concreteThreeLinkEquiv base d hdimension (by omega) hm F hF hFcard hsupport
  commonScale := commonScale
  commonScale_pos := hcommonScale
  relabel_eq := by
    apply WeightedGraph.ext_weight
    intro u v
    rw [WeightedGraph.relabel_weight]
    change _ = commonScale * threeFiberWeight _ _
      (concreteThreeLinkEquiv base d hdimension (by omega) hm F hF hFcard hsupport u)
      (concreteThreeLinkEquiv base d hdimension (by omega) hm F hF hFcard hsupport v)
    exact hweight u v

/-- The actual codimension-two three-fiber link has the full two-sided
`1 / d` bound as soon as its (5.1) edge calculation is stated with its common
positive factor. -/
theorem concreteThreeLink_twoSidedSpectralBound_of_weight_formula
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 3)
    (commonScale : ℝ) (hcommonScale : 0 < commonScale)
    (hweight : ∀ u v :
      (measuredComplex (A := A) base.complex d hdimension (by omega) hm).LinkVertex F,
      ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).weight u v =
        commonScale * threeFiberWeight
          (concreteThreeOccupancy F hsupport)
          (concreteThreeUnused F hsupport)
          (concreteThreeLinkEquiv base d hdimension (by omega) hm F hF hFcard hsupport u)
          (concreteThreeLinkEquiv base d hdimension (by omega) hm F hF hFcard hsupport v)) :
    ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F).TwoSidedSpectralBound
      (1 / (d : ℝ)) := by
  exact (concreteThreeLinkCertificate_of_weight_formula base d hdimension hd hm F
    hF hFcard hsupport commonScale hcommonScale hweight).twoSidedSpectralBound

/-- Unconditional concrete `r(F)=3` row of Theorem 5.1. -/
theorem concreteThreeLink_twoSidedSpectralBound
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hFcard : F.card + 1 = d)
    (hsupport : (projectionSupport F).card = 3) :
    WeightedGraph.TwoSidedSpectralBound
      ((measuredComplex (A := A) base.complex d hdimension (by omega) hm).linkGraph F)
      (1 / (d : ℝ)) := by
  apply concreteThreeLink_twoSidedSpectralBound_of_weight_formula
    base d hdimension hd hm F hF hFcard hsupport
    (concreteThreeCommonScale base d F)
    (concreteThreeCommonScale_pos base d hdimension (by omega) hm F hF hsupport)
  exact concreteThreeLink_weight_eq base d hdimension hd hm F hF hFcard hsupport

end WeightedLift

end HDXLean
