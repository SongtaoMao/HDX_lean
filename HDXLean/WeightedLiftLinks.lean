import HDXLean.WeightedLiftCayley

/-!
# Link structure in the weighted dimension lift

This file isolates the combinatorial part of the link-connectivity argument in
Section 5.  Positivity of the lifted measure turns positive link edges into
the simple condition that the corresponding enlarged face has a compatible
base triangle.  Every nonempty positive-dimensional link then has a star
center: choose a fresh label in any already occupied fiber.
-/

namespace HDXLean

namespace MeasuredComplex

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Because every top-face weight is positive, the support of a link graph is
exactly the set of pairs which extend the conditioned face. -/
theorem linkEdgeWeight_pos_iff (X : MeasuredComplex V) (F : Finset V)
    (u v : X.LinkVertex F) :
    0 < X.linkEdgeWeight F u v ↔
      u ≠ v ∧ X.IsFace (insert v.1 (insert u.1 F)) := by
  classical
  constructor
  · intro hpos
    have huv : u ≠ v := by
      intro huv
      subst v
      simp [linkEdgeWeight] at hpos
    rw [linkEdgeWeight, if_neg huv] at hpos
    have hexists :
        ∃ T ∈ X.topFaces.filter
            (fun T ↦ insert v.1 (insert u.1 F) ⊆ T),
          0 < X.topWeight T := by
      rw [Finset.sum_pos_iff_of_nonneg] at hpos
      · exact hpos
      · intro T hT
        exact le_of_lt (X.topWeight_pos T (Finset.mem_filter.mp hT).1)
    obtain ⟨T, hT, -⟩ := hexists
    exact ⟨huv, T, (Finset.mem_filter.mp hT).1,
      (Finset.mem_filter.mp hT).2⟩
  · rintro ⟨huv, T, hT, hsub⟩
    rw [linkEdgeWeight, if_neg huv]
    apply Finset.sum_pos'
    · intro S hS
      exact le_of_lt (X.topWeight_pos S (Finset.mem_filter.mp hS).1)
    · exact ⟨T, Finset.mem_filter.mpr ⟨hT, hsub⟩,
        X.topWeight_pos T hT⟩

/-- Adjacency in a link is the corresponding enlarged-face condition. -/
theorem linkGraph_adj_iff (X : MeasuredComplex V) (F : Finset V)
    (u v : X.LinkVertex F) :
    (X.linkGraph F).Adj u v ↔
      u ≠ v ∧ X.IsFace (insert v.1 (insert u.1 F)) := by
  exact X.linkEdgeWeight_pos_iff F u v

end MeasuredComplex

namespace WeightedLift

variable {Gamma A : Type*}
  [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma] [DecidableEq Gamma]
  [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A]

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Exact face criterion for the lifted complex.  The cardinality condition is
the only obstruction in addition to containment in the fibers of one base
triangle. -/
theorem lifted_isFace_iff
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A)) :
    (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F ↔
      F.card ≤ d + 1 ∧
        ∃ tau ∈ base.complex.topFaces,
          CompatibleParent (A := A) tau F := by
  constructor
  · rintro ⟨T, hT, hFT⟩
    obtain ⟨hTcard, tau, htau, hcompatible⟩ := mem_topFaces.mp hT
    refine ⟨?_, tau, htau, fun z hz ↦ hcompatible (hFT hz)⟩
    rw [← hTcard]
    exact Finset.card_le_card hFT
  · rintro ⟨hcard, tau, htau, hcompatible⟩
    obtain ⟨T, hT, hFT⟩ :=
      extend_to_topFace (A := A) htau hdimension hd hm hcompatible hcard
    exact ⟨T, hT, hFT⟩

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Fully explicit adjacency criterion for a conditioned lifted link. -/
theorem lifted_link_adj_iff
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (u v : (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex F) :
    ((measuredComplex (A := A) base.complex d hdimension hd hm).linkGraph F).Adj u v ↔
      u ≠ v ∧
        (insert v.1 (insert u.1 F)).card ≤ d + 1 ∧
        ∃ tau ∈ base.complex.topFaces,
          CompatibleParent (A := A) tau
            (insert v.1 (insert u.1 F)) := by
  rw [MeasuredComplex.linkGraph_adj_iff,
    lifted_isFace_iff base d hdimension hd hm]

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Projection of a vertex in the empty lifted link to the empty base link. -/
noncomputable def projectEmptyLinkVertex
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A)
    (u : (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex ∅) :
    base.complex.LinkVertex ∅ := by
  refine ⟨u.1.1, by simp, ?_⟩
  have hliftedPair :
      (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace
        {u.1, u.1} := by
    simpa using u.2.2
  have hbasePair :=
    (lifted_pair_isFace_iff (A := A) base d hdimension hd hm u.1 u.1).mp
      hliftedPair
  simpa using hbasePair

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Lift an empty-base-link vertex using an arbitrary fiber label. -/
noncomputable def emptyLiftVertex
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A)
    (a : A) (u : base.complex.LinkVertex ∅) :
    (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex ∅ := by
  refine ⟨(u.1, a), by simp, ?_⟩
  have hbasePair : base.complex.IsFace {u.1, u.1} := by
    simpa using u.2.2
  have hliftedPair :=
    (lifted_pair_isFace_iff (A := A) base d hdimension hd hm
      (u.1, a) (u.1, a)).mpr hbasePair
  simpa using hliftedPair

/-- An edge of the empty base link lifts to an edge with any choices of fiber
labels. -/
theorem emptyLiftVertex_adj
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A)
    (a b : A) (u v : base.complex.LinkVertex ∅)
    (huv : (base.complex.linkGraph ∅).Adj u v) :
    ((measuredComplex (A := A) base.complex d hdimension hd hm).linkGraph ∅).Adj
      (emptyLiftVertex (A := A) base d hdimension hd hm a u)
      (emptyLiftVertex (A := A) base d hdimension hd hm b v) := by
  rw [MeasuredComplex.linkGraph_adj_iff] at huv ⊢
  refine ⟨?_, ?_⟩
  · intro heq
    apply huv.1
    apply Subtype.ext
    have hfst := congrArg (fun z : Gamma × A ↦ z.1)
      (congrArg Subtype.val heq)
    exact hfst
  · have hlifted :=
      (lifted_pair_isFace_iff (A := A) base d hdimension hd hm
        (v.1, b) (u.1, a)).mpr huv.2
    simpa [emptyLiftVertex] using hlifted

/-- Distinct vertices in the empty lifted link lying over the same base vertex
are adjacent through the complete graph in that fiber. -/
theorem empty_link_adj_of_same_base
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A)
    (u v : (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex ∅)
    (huv : u ≠ v) (hbase : u.1.1 = v.1.1) :
    ((measuredComplex (A := A) base.complex d hdimension hd hm).linkGraph ∅).Adj
      u v := by
  rw [MeasuredComplex.linkGraph_adj_iff]
  refine ⟨huv, ?_⟩
  have huBase : base.complex.IsFace {u.1.1, u.1.1} := by
    have huLifted :
        (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace
          {u.1, u.1} := by
      simpa using u.2.2
    exact (lifted_pair_isFace_iff (A := A) base d hdimension hd hm u.1 u.1).mp
      huLifted
  have hpairBase : base.complex.IsFace {v.1.1, u.1.1} := by
    simpa [hbase] using huBase
  exact (lifted_pair_isFace_iff (A := A) base d hdimension hd hm v.1 u.1).mpr
    hpairBase

/-- Connectivity of the empty lifted link follows from connectivity of the
empty base link: lift a base path at label zero and use one within-fiber edge
at each endpoint. -/
theorem empty_lifted_link_connected
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A)
    (hbase : base.complex.PositiveLinksConnected) :
    ((measuredComplex (A := A) base.complex d hdimension hd hm).linkGraph ∅).Connected := by
  let Y := measuredComplex (A := A) base.complex d hdimension hd hm
  have hemptyFace : base.complex.IsFace ∅ := by
    obtain ⟨T, hT⟩ := base_topFaces_nonempty base.complex
    exact ⟨T, hT, Finset.empty_subset T⟩
  have hbaseConnected : (base.complex.linkGraph ∅).Connected := by
    apply hbase ∅ hemptyFace
    simp [hdimension]
  intro u v
  let pu := projectEmptyLinkVertex (A := A) base d hdimension hd hm u
  let pv := projectEmptyLinkVertex (A := A) base d hdimension hd hm v
  let lu := emptyLiftVertex (A := A) base d hdimension hd hm (0 : A) pu
  let lv := emptyLiftVertex (A := A) base d hdimension hd hm (0 : A) pv
  have hmiddleBase : Relation.ReflTransGen
      (base.complex.linkGraph ∅).Adj pu pv := hbaseConnected pu pv
  have liftPath : ∀ {p q : base.complex.LinkVertex ∅},
      Relation.ReflTransGen (base.complex.linkGraph ∅).Adj p q →
        Relation.ReflTransGen (Y.linkGraph ∅).Adj
          (emptyLiftVertex (A := A) base d hdimension hd hm (0 : A) p)
          (emptyLiftVertex (A := A) base d hdimension hd hm (0 : A) q) := by
    intro p q hpq
    induction hpq with
    | refl => exact Relation.ReflTransGen.refl
    | tail hxy hyz ih =>
        exact ih.tail (emptyLiftVertex_adj (A := A) base d hdimension hd hm
          0 0 _ _ hyz)
  have hmiddle : Relation.ReflTransGen (Y.linkGraph ∅).Adj lu lv := by
    exact liftPath hmiddleBase
  have hleft : Relation.ReflTransGen (Y.linkGraph ∅).Adj u lu := by
    by_cases h : u = lu
    · rw [h]
    · apply Relation.ReflTransGen.single
      apply empty_link_adj_of_same_base (A := A) base d hdimension hd hm u lu h
      simp [lu, pu, emptyLiftVertex, projectEmptyLinkVertex]
  have hright : Relation.ReflTransGen (Y.linkGraph ∅).Adj lv v := by
    by_cases h : lv = v
    · rw [h]
    · apply Relation.ReflTransGen.single
      apply empty_link_adj_of_same_base (A := A) base d hdimension hd hm lv v h
      simp [lv, pv, emptyLiftVertex, projectEmptyLinkVertex]
  exact hleft.trans (hmiddle.trans hright)

omit [Fintype Gamma] [AddCommGroup Gamma] [Module F₂ Gamma]
  [AddCommGroup A] [Module F₂ A] in
/-- A fiber uses at most as many labels as the whole lifted face has vertices. -/
theorem occupancy_le_face_card (F : Finset (Gamma × A)) (x : Gamma) :
    occupancy F x ≤ F.card := by
  classical
  let used : Finset A := Finset.univ.filter fun a ↦ (x, a) ∈ F
  have himage : used.image (fun a ↦ (x, a)) ⊆ F := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp ha).2
  calc
    occupancy F x = used.card := rfl
    _ = (used.image fun a ↦ (x, a)).card := by
      symm
      apply Finset.card_image_of_injective
      intro a b hab
      exact congrArg Prod.snd hab
    _ ≤ F.card := Finset.card_le_card himage

omit [Fintype Gamma] [AddCommGroup Gamma] [Module F₂ Gamma]
  [AddCommGroup A] [Module F₂ A] in
/-- If a face is smaller than a fiber, that fiber contains a fresh label. -/
theorem exists_fresh_fiber_vertex (F : Finset (Gamma × A)) (x : Gamma)
    (hsmall : F.card < Fintype.card A) :
    ∃ a : A, (x, a) ∉ F := by
  classical
  let used : Finset A := Finset.univ.filter fun a ↦ (x, a) ∈ F
  have hused : used.card < (Finset.univ : Finset A).card :=
    (occupancy_le_face_card (A := A) F x).trans_lt hsmall
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hused
  exact ⟨a, fun hmem ↦ ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩)⟩

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Every nonempty link which is required to be positive-dimensional has a
universal center.  This is the precise star decomposition used for link
connectivity: the center is a fresh label in an already occupied fiber. -/
theorem exists_link_star_center
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A)
    (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFnonempty : F.Nonempty) (hcodim : F.card + 1 ≤ d) :
    ∃ c : (measuredComplex (A := A) base.complex d hdimension hd hm).LinkVertex F,
      ∀ u, u ≠ c →
        ((measuredComplex (A := A) base.complex d hdimension hd hm).linkGraph F).Adj u c := by
  let Y := measuredComplex (A := A) base.complex d hdimension hd hm
  obtain ⟨z, hzF⟩ := hFnonempty
  have hFsmall : F.card < Fintype.card A := by
    have hFd : F.card < d := by omega
    have hdcard : d ≤ Fintype.card A := by omega
    exact hFd.trans_le hdcard
  obtain ⟨a, haFresh⟩ := exists_fresh_fiber_vertex (A := A) F z.1 hFsmall
  have hcenterFace : Y.IsFace (insert (z.1, a) F) := by
    rw [lifted_isFace_iff base d hdimension hd hm]
    obtain ⟨-, tau, htau, hcompatible⟩ :=
      (lifted_isFace_iff base d hdimension hd hm F).mp hF
    refine ⟨?_, tau, htau, ?_⟩
    · calc
        (insert (z.1, a) F).card ≤ F.card + 1 := Finset.card_insert_le _ _
        _ ≤ d := hcodim
        _ ≤ d + 1 := by omega
    · intro w hw
      rw [Finset.mem_insert] at hw
      rcases hw with hw | hw
      · subst w
        have hzParent : z ∈ fibersAbove (A := A) tau := hcompatible hzF
        have hzBase : z.1 ∈ tau := mem_fibersAbove.mp hzParent
        apply mem_fibersAbove.mpr
        exact hzBase
      · exact hcompatible hw
  let c : Y.LinkVertex F := ⟨(z.1, a), haFresh, hcenterFace⟩
  refine ⟨c, ?_⟩
  intro u huc
  rw [MeasuredComplex.linkGraph_adj_iff]
  refine ⟨huc, ?_⟩
  rw [lifted_isFace_iff base d hdimension hd hm]
  obtain ⟨-, tau, htau, hcompatible⟩ :=
    (lifted_isFace_iff base d hdimension hd hm (insert u.1 F)).mp u.2.2
  refine ⟨?_, tau, htau, ?_⟩
  · calc
      (insert c.1 (insert u.1 F)).card ≤ (insert u.1 F).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ (F.card + 1) + 1 :=
        Nat.add_le_add_right (Finset.card_insert_le u.1 F) 1
      _ = F.card + 2 := by omega
      _ ≤ d + 1 := by omega
  · intro w hw
    rw [Finset.mem_insert] at hw
    rcases hw with hw | hw
    · subst w
      apply mem_fibersAbove.mpr
      change z.1 ∈ tau
      apply mem_fibersAbove.mp
      exact hcompatible (Finset.mem_insert_of_mem hzF)
    · exact hcompatible hw

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Consequently every nonempty positive-dimensional lifted link is
connected, independently of any spectral calculation. -/
theorem nonempty_lifted_link_connected
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A)
    (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F)
    (hFnonempty : F.Nonempty) (hcodim : F.card + 1 ≤ d) :
    ((measuredComplex (A := A) base.complex d hdimension hd hm).linkGraph F).Connected := by
  obtain ⟨c, hc⟩ :=
    exists_link_star_center (A := A) base d hdimension hd hm F hF hFnonempty hcodim
  intro u v
  have huc : Relation.ReflTransGen
      ((measuredComplex (A := A) base.complex d hdimension hd hm).linkGraph F).Adj u c := by
    by_cases h : u = c
    · subst u
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (hc u h)
  have hcv : Relation.ReflTransGen
      ((measuredComplex (A := A) base.complex d hdimension hd hm).linkGraph F).Adj c v := by
    by_cases h : v = c
    · subst v
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single
        (((measuredComplex (A := A) base.complex d hdimension hd hm).linkGraph F).adj_symm.mp
          (hc v h))
  exact huc.trans hcv

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Reduction of all positive-link connectivity to the empty-face link (the
lifted one-skeleton). -/
theorem positiveLinksConnected_of_empty_link
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A)
    (hempty :
      ((measuredComplex (A := A) base.complex d hdimension hd hm).linkGraph ∅).Connected) :
    (measuredComplex (A := A) base.complex d hdimension hd hm).PositiveLinksConnected := by
  intro F hF hcodim
  by_cases hnonempty : F.Nonempty
  · exact nonempty_lifted_link_connected (A := A) base d hdimension hd hm
      F hF hnonempty hcodim
  · rw [Finset.not_nonempty_iff_eq_empty] at hnonempty
    subst F
    exact hempty

/-- The complete connectivity statement required in Theorem 5.1.  The empty
link is lifted from the connected base one-skeleton; every nonempty link is
the star described by `exists_link_star_center`. -/
theorem lifted_positiveLinksConnected
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A)
    (hbase : base.complex.PositiveLinksConnected) :
    (measuredComplex (A := A) base.complex d hdimension hd hm).PositiveLinksConnected := by
  apply positiveLinksConnected_of_empty_link (A := A) base d hdimension hd hm
  exact empty_lifted_link_connected (A := A) base d hdimension hd hm hbase

end WeightedLift

end HDXLean
