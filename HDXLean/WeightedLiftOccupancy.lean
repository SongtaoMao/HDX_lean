import HDXLean.WeightedLiftLinks

/-!
# Occupied base fibers of a lifted face

Codimension-two faces in the weighted lift meet exactly one, two, or three
base fibers.  This file defines the parent-independent projection support and
proves the exhaustive trichotomy used by the three spectral calculations.
-/

namespace HDXLean

namespace WeightedLift

variable {Gamma A : Type*}
  [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma] [DecidableEq Gamma]
  [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A]

/-- The set of base vertices whose fibers meet a lifted face. -/
def projectionSupport (F : Finset (Gamma × A)) : Finset Gamma :=
  F.image Prod.fst

omit [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma]
    [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A] in
@[simp]
theorem mem_projectionSupport {F : Finset (Gamma × A)} {x : Gamma} :
    x ∈ projectionSupport F ↔ ∃ a : A, (x, a) ∈ F := by
  simp [projectionSupport]

omit [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma]
    [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A] in
theorem projectionSupport_card_le (F : Finset (Gamma × A)) :
    (projectionSupport F).card ≤ F.card :=
  Finset.card_image_le

omit [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma]
    [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A] in
theorem projectionSupport_nonempty_iff (F : Finset (Gamma × A)) :
    (projectionSupport F).Nonempty ↔ F.Nonempty := by
  simp [projectionSupport]

omit [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma]
    [AddCommGroup A] [Module F₂ A] in
/-- Relative to any compatible parent, `occupiedSupport` is the canonical
projection support and hence does not depend on the chosen parent triangle. -/
theorem occupiedSupport_eq_projectionSupport
    {tau : Finset Gamma} {F : Finset (Gamma × A)}
    (hcompatible : CompatibleParent (A := A) tau F) :
    occupiedSupport (A := A) tau F = projectionSupport F := by
  ext x
  rw [mem_occupiedSupport, mem_projectionSupport]
  constructor
  · rintro ⟨_hxTau, a, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨mem_fibersAbove.mp (hcompatible ha), a, ha⟩

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Every lifted face projects into a base triangle, so it meets at most three
base fibers. -/
theorem projectionSupport_card_le_three
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F) :
    (projectionSupport F).card ≤ 3 := by
  obtain ⟨_hcard, tau, htau, hcompatible⟩ :=
    (lifted_isFace_iff base d hdimension hd hm F).mp hF
  have hsubset : projectionSupport F ⊆ tau := by
    intro x hx
    obtain ⟨a, ha⟩ := mem_projectionSupport.mp hx
    exact mem_fibersAbove.mp (hcompatible ha)
  calc
    (projectionSupport F).card ≤ tau.card := Finset.card_le_card hsubset
    _ = 3 := by simpa [hdimension] using base.complex.top_card tau htau

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- The base projection of every lifted face is itself a face of the base
complex. -/
theorem projectionSupport_isFace
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace F) :
    base.complex.IsFace (projectionSupport F) := by
  obtain ⟨_hcard, tau, htau, hcompatible⟩ :=
    (lifted_isFace_iff base d hdimension hd hm F).mp hF
  refine ⟨tau, htau, ?_⟩
  intro x hx
  obtain ⟨a, ha⟩ := mem_projectionSupport.mp hx
  exact mem_fibersAbove.mp (hcompatible ha)

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Exhaustive occupancy split for a codimension-two face of a `d`-lift. -/
theorem codimensionTwo_projectionSupport_trichotomy
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 3 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (F : Finset (Gamma × A))
    (hF : (measuredComplex (A := A) base.complex d hdimension (by omega) hm).IsFace F)
    (hcodim : F.card + 1 = d) :
    (projectionSupport F).card = 1 ∨
      (projectionSupport F).card = 2 ∨
      (projectionSupport F).card = 3 := by
  have hFcardPositive : 0 < F.card := by omega
  have hFnonempty : F.Nonempty := Finset.card_pos.mp hFcardPositive
  have hpositive : 0 < (projectionSupport F).card :=
    Finset.card_pos.mpr ((projectionSupport_nonempty_iff F).2 hFnonempty)
  have hupper := projectionSupport_card_le_three (A := A) base d hdimension
    (by omega) hm F hF
  omega

end WeightedLift

end HDXLean
