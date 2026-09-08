import HDXLean.Basic

/-!
# Affine functions along projective directions

This module gives a representative-based interface for the finite projective
direction sets used in Section 3 of the paper.  The two predicates that depend
on representatives are proved invariant under multiplication by a nonzero
scalar.
-/

namespace HDXLean

universe u v

section Directions

variable (F : Type u) [Field F]

/-- The coordinate model for the ambient vector space. -/
abbrev CoordinateSpace (t : ℕ) := Fin t → F

/--
A finite family of representatives for distinct projective directions.

The index type is kept as a parameter, rather than bundled into the structure,
so later constructions can retain their natural finite indexing types.
-/
structure DirectionSet (t : ℕ) (ι : Type v) [Fintype ι] where
  representative : ι → CoordinateSpace F t
  representative_ne_zero : ∀ i, representative i ≠ 0
  projectivelyDistinct : ∀ {i j} {c : F}, c ≠ 0 →
    representative i = c • representative j → i = j
  spans : Submodule.span F (Set.range representative) = ⊤

/-- A function restricts to an affine function on every line parallel to `a`. -/
def AffineOnDirection {t : ℕ} (f : CoordinateSpace F t → F)
    (a : CoordinateSpace F t) : Prop :=
  ∀ x, ∃ A B : F, ∀ scalar : F,
    f (x + scalar • a) = A + B * scalar

theorem AffineOnDirection.smul {t : ℕ} {f : CoordinateSpace F t → F}
    {a : CoordinateSpace F t} (h : AffineOnDirection F f a) (c : F) :
    AffineOnDirection F f (c • a) := by
  intro x
  obtain ⟨A, B, hline⟩ := h x
  refine ⟨A, B * c, fun scalar ↦ ?_⟩
  rw [smul_smul, hline (scalar * c)]
  ring

/-- Affineness along a direction is independent of its nonzero representative. -/
theorem affineOnDirection_smul_iff {t : ℕ}
    (f : CoordinateSpace F t → F) (a : CoordinateSpace F t)
    {c : F} (hc : c ≠ 0) :
    AffineOnDirection F f (c • a) ↔ AffineOnDirection F f a := by
  constructor
  · intro h
    simpa [smul_smul, hc] using AffineOnDirection.smul F h (c⁻¹)
  · intro h
    exact AffineOnDirection.smul F h c

/-- Functions that are affine on every direction represented by `D`. -/
def affineFunctions {t : ℕ} {ι : Type v} [Fintype ι]
    (D : DirectionSet F t ι) : Submodule F (CoordinateSpace F t → F) where
  carrier := {f | ∀ i, AffineOnDirection F f (D.representative i)}
  zero_mem' := by
    intro i x
    exact ⟨0, 0, fun scalar ↦ by simp⟩
  add_mem' := by
    intro f g hf hg i x
    obtain ⟨A₁, B₁, hfline⟩ := hf i x
    obtain ⟨A₂, B₂, hgline⟩ := hg i x
    refine ⟨A₁ + A₂, B₁ + B₂, fun scalar ↦ ?_⟩
    change f (x + scalar • D.representative i) +
        g (x + scalar • D.representative i) = _
    rw [hfline scalar, hgline scalar]
    ring
  smul_mem' := by
    intro c f hf i x
    obtain ⟨A, B, hline⟩ := hf i x
    refine ⟨c * A, c * B, fun scalar ↦ ?_⟩
    change c * f (x + scalar • D.representative i) = _
    rw [hline scalar]
    ring

@[simp]
theorem mem_affineFunctions_iff {t : ℕ} {ι : Type v} [Fintype ι]
    (D : DirectionSet F t ι) (f : CoordinateSpace F t → F) :
    f ∈ affineFunctions F D ↔
      ∀ i, AffineOnDirection F f (D.representative i) :=
  Iff.rfl

/-- The number of represented directions on which a functional is nonzero. -/
noncomputable def directionWeight {t : ℕ} {ι : Type v} [Fintype ι]
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F) : ℕ := by
  classical
  exact (Finset.univ.filter fun i ↦
    functional (D.representative i) ≠ 0).card

/-- Every nonzero linear functional has at least the prescribed direction weight. -/
def HasLowerDistance {t : ℕ} {ι : Type v} [Fintype ι]
    (D : DirectionSet F t ι) (minimumWeight : ℕ) : Prop :=
  ∀ functional : CoordinateSpace F t →ₗ[F] F,
    functional ≠ 0 → minimumWeight ≤ directionWeight F D functional

/-- A direction weight can never exceed the total number of represented points. -/
theorem directionWeight_le_card {t : ℕ} {ι : Type v} [Fintype ι]
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F) :
    directionWeight F D functional ≤ Fintype.card ι := by
  classical
  simpa [directionWeight] using
    (Finset.card_filter_le (Finset.univ : Finset ι)
      (fun i ↦ functional (D.representative i) ≠ 0))

/-- Spanning projective directions meet the complement of every hyperplane.
This is the elementary fact used in the paper to infer `Δ(D) ≥ 1`. -/
theorem directionWeight_pos {t : ℕ} {ι : Type v} [Fintype ι]
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F)
    (hfunctional : functional ≠ 0) :
    0 < directionWeight F D functional := by
  classical
  rw [directionWeight, Finset.card_pos]
  rw [Finset.filter_nonempty_iff]
  simp only [Finset.mem_univ, true_and]
  by_contra hnonempty
  push Not at hnonempty
  have hrange : Set.range D.representative ⊆ LinearMap.ker functional := by
    rintro _ ⟨i, rfl⟩
    exact hnonempty i
  have hspan : Submodule.span F (Set.range D.representative) ≤
      LinearMap.ker functional :=
    Submodule.span_le.mpr hrange
  have htop : (⊤ : Submodule F (CoordinateSpace F t)) ≤
      LinearMap.ker functional := by
    simpa only [D.spans] using hspan
  have hker : LinearMap.ker functional = ⊤ := top_unique htop
  exact hfunctional (LinearMap.ker_eq_top.mp hker)

/-- Every spanning direction set has lower distance at least one. -/
theorem hasLowerDistance_one {t : ℕ} {ι : Type v} [Fintype ι]
    (D : DirectionSet F t ι) : HasLowerDistance F D 1 := by
  intro functional hfunctional
  exact directionWeight_pos F D functional hfunctional

/-- Nonvanishing of a functional is unchanged when its argument is rescaled. -/
theorem linearFunctional_smul_ne_zero_iff {t : ℕ}
    (functional : CoordinateSpace F t →ₗ[F] F)
    (a : CoordinateSpace F t) {c : F} (hc : c ≠ 0) :
    functional (c • a) ≠ 0 ↔ functional a ≠ 0 := by
  rw [map_smul]
  simp [hc]

/-- Pointwise nonzero rescaling of representatives does not change direction weight. -/
theorem directionWeight_eq_of_rescaled_representatives
    {t : ℕ} {ι : Type v} [Fintype ι]
    (D E : DirectionSet F t ι) (c : ι → F)
    (hc : ∀ i, c i ≠ 0)
    (hrepresentative : ∀ i, E.representative i = c i • D.representative i)
    (functional : CoordinateSpace F t →ₗ[F] F) :
    directionWeight F E functional = directionWeight F D functional := by
  classical
  unfold directionWeight
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hrepresentative i,
    linearFunctional_smul_ne_zero_iff F functional (D.representative i) (hc i)]

/-- Lower distance is invariant under pointwise nonzero rescaling of representatives. -/
theorem hasLowerDistance_of_rescaled_representatives
    {t : ℕ} {ι : Type v} [Fintype ι]
    (D E : DirectionSet F t ι) (c : ι → F)
    (hc : ∀ i, c i ≠ 0)
    (hrepresentative : ∀ i, E.representative i = c i • D.representative i)
    {minimumWeight : ℕ} (hD : HasLowerDistance F D minimumWeight) :
    HasLowerDistance F E minimumWeight := by
  intro functional hfunctional
  rw [directionWeight_eq_of_rescaled_representatives F D E c hc
    hrepresentative functional]
  exact hD functional hfunctional

/-- Pointwise nonzero rescaling of representatives does not change the affine subspace. -/
theorem affineFunctions_eq_of_rescaled_representatives
    {t : ℕ} {ι : Type v} [Fintype ι]
    (D E : DirectionSet F t ι) (c : ι → F)
    (hc : ∀ i, c i ≠ 0)
    (hrepresentative : ∀ i, E.representative i = c i • D.representative i) :
    affineFunctions F E = affineFunctions F D := by
  ext f
  simp only [mem_affineFunctions_iff]
  constructor
  · intro hf i
    rw [← affineOnDirection_smul_iff F f (D.representative i) (hc i)]
    simpa only [hrepresentative i] using hf i
  · intro hf i
    rw [hrepresentative i,
      affineOnDirection_smul_iff F f (D.representative i) (hc i)]
    exact hf i

/-- Every constant function belongs to the affine-on-directions submodule. -/
theorem constant_mem_affineFunctions {t : ℕ} {ι : Type v} [Fintype ι]
    (D : DirectionSet F t ι) (constant : F) :
    (fun _ : CoordinateSpace F t ↦ constant) ∈ affineFunctions F D := by
  rw [mem_affineFunctions_iff]
  intro i x
  exact ⟨constant, 0, fun scalar ↦ by simp⟩

/-- Every globally linear function belongs to the affine-on-directions submodule. -/
theorem linear_mem_affineFunctions {t : ℕ} {ι : Type v} [Fintype ι]
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F) :
    (functional : CoordinateSpace F t → F) ∈ affineFunctions F D := by
  rw [mem_affineFunctions_iff]
  intro i x
  refine ⟨functional x, functional (D.representative i), fun scalar ↦ ?_⟩
  rw [map_add, map_smul]
  change functional x + scalar * functional (D.representative i) = _
  ring

/-- A constant plus a globally linear function belongs to `affineFunctions`. -/
theorem affine_mem_affineFunctions {t : ℕ} {ι : Type v} [Fintype ι]
    (D : DirectionSet F t ι) (constant : F)
    (functional : CoordinateSpace F t →ₗ[F] F) :
    (fun x ↦ constant + functional x) ∈ affineFunctions F D := by
  have hconstant := constant_mem_affineFunctions F D constant
  have hlinear := linear_mem_affineFunctions F D functional
  change (fun _ : CoordinateSpace F t ↦ constant) +
      (functional : CoordinateSpace F t → F) ∈ affineFunctions F D
  exact (affineFunctions F D).add_mem hconstant hlinear

end Directions

end HDXLean
