import HDXLean.WeightedLiftGenerators
import HDXLean.WeightedLiftMeasure

/-!
# Cayley one-skeleton of the weighted dimension lift

This file proves equation (5.2) from the concrete lifted top-face set.  The
key observation is that two lifted vertices form an edge exactly when their
base coordinates form a face of the base two-complex; equality of base
coordinates gives the complete graph inside each fiber.
-/

namespace HDXLean

namespace WeightedLift

variable {Gamma A : Type*}
  [AddCommGroup Gamma] [Module F₂ Gamma] [Fintype Gamma] [DecidableEq Gamma]
  [AddCommGroup A] [Module F₂ A] [Fintype A] [DecidableEq A]

omit [AddCommGroup Gamma] [Module F₂ Gamma]
  [AddCommGroup A] [Module F₂ A] [DecidableEq A] in
/-- The capacity of the three fibers over a base triangle. -/
theorem parent_capacity {X : MeasuredComplex Gamma} {tau : Finset Gamma}
    (htau : tau ∈ X.topFaces) (hdimension : X.dim = 2)
    {d : ℕ} (hd : 2 ≤ d) (hm : 2 * d ≤ Fintype.card A) :
    d + 1 ≤ (fibersAbove (A := A) tau).card := by
  rw [card_fibersAbove, X.top_card tau htau, hdimension]
  omega

omit [AddCommGroup Gamma] [Module F₂ Gamma]
  [AddCommGroup A] [Module F₂ A] [DecidableEq A] in
/-- Every small compatible set extends to a lifted top face. -/
theorem extend_to_topFace {X : MeasuredComplex Gamma} {tau : Finset Gamma}
    (htau : tau ∈ X.topFaces) (hdimension : X.dim = 2)
    {d : ℕ} (hd : 2 ≤ d) (hm : 2 * d ≤ Fintype.card A)
    {F : Finset (Gamma × A)} (hF : CompatibleParent (A := A) tau F)
    (hcard : F.card ≤ d + 1) :
    ∃ T ∈ topFaces (A := A) X d, F ⊆ T := by
  obtain ⟨T, hFT, hTparent, hTcard⟩ :=
    Finset.exists_subsuperset_card_eq hF hcard
      (parent_capacity (A := A) htau hdimension hd hm)
  exact ⟨T, mem_topFaces.mpr ⟨hTcard, tau, htau, hTparent⟩, hFT⟩

omit [Module F₂ Gamma] [AddCommGroup A] [Module F₂ A] in
/-- Pair faces in the lift are exactly pair faces after projection to the
base complex. -/
theorem lifted_pair_isFace_iff
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (z w : Gamma × A) :
    (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace {z, w} ↔
      base.complex.IsFace {z.1, w.1} := by
  constructor
  · rintro ⟨T, hT, hpair⟩
    obtain ⟨-, tau, htau, hcompatible⟩ := mem_topFaces.mp hT
    have hzT : z ∈ T := hpair (by simp)
    have hwT : w ∈ T := hpair (by simp)
    have hzTau : z.1 ∈ tau := mem_fibersAbove.mp (hcompatible hzT)
    have hwTau : w.1 ∈ tau := mem_fibersAbove.mp (hcompatible hwT)
    refine ⟨tau, htau, ?_⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hzTau
    · exact hwTau
  · rintro ⟨tau, htau, hpair⟩
    have hcompatible : CompatibleParent (A := A) tau {z, w} := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact mem_fibersAbove.mpr (hpair (by simp))
      · exact mem_fibersAbove.mpr (hpair (by simp))
    have hcard : ({z, w} : Finset (Gamma × A)).card ≤ d + 1 := by
      calc
        ({z, w} : Finset (Gamma × A)).card ≤ 2 := Finset.card_insert_le _ _
        _ ≤ d + 1 := by omega
    obtain ⟨T, hT, hsub⟩ :=
      extend_to_topFace (A := A) htau hdimension hd hm hcompatible hcard
    exact ⟨T, hT, hsub⟩

/-- Equation (5.2) as a Cayley edge criterion. -/
theorem lifted_edge_iff_generators
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) (z w : Gamma × A) :
    (measuredComplex (A := A) base.complex d hdimension hd hm).IsFace {z, w} ↔
      z = w ∨ w - z ∈ generators (A := A) base.cayley.generators := by
  rw [lifted_pair_isFace_iff base d hdimension hd hm,
    base.cayley.edge_iff]
  rcases z with ⟨x, a⟩
  rcases w with ⟨y, b⟩
  change (x = y ∨ y - x ∈ base.cayley.generators) ↔
    (x, a) = (y, b) ∨
      (y - x, b - a) ∈ generators (A := A) base.cayley.generators
  rw [mem_generators_iff]
  constructor
  · rintro (hxy | hedge)
    · by_cases hab : a = b
      · left
        exact Prod.ext hxy hab
      · right
        left
        exact ⟨sub_eq_zero.mpr hxy.symm, sub_ne_zero.mpr (Ne.symm hab)⟩
    · exact Or.inr (Or.inr hedge)
  · rintro (hsame | hfiber | hedge)
    · exact Or.inl (congrArg Prod.fst hsame)
    · exact Or.inl (sub_eq_zero.mp hfiber.1).symm
    · exact Or.inr hedge

/-- The Cayley presentation of the lifted one-skeleton. -/
noncomputable def cayleyPresentation
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) :
    CayleyPresentation
      (measuredComplex (A := A) base.complex d hdimension hd hm) where
  generators := generators (A := A) base.cayley.generators
  zero_not_mem := zero_not_mem_generators base.cayley.zero_not_mem
  neg_mem_iff := neg_mem_generators_iff base.cayley.neg_mem_iff
  edge_iff := lifted_edge_iff_generators base d hdimension hd hm

/-- Exact degree formula for the concrete lifted Cayley presentation. -/
theorem cayley_degree
    (base : CayleyComplex (V := Gamma)) (d : ℕ)
    (hdimension : base.complex.dim = 2) (hd : 2 ≤ d)
    (hm : 2 * d ≤ Fintype.card A) :
    (cayleyPresentation (A := A) base d hdimension hd hm).degree =
      Fintype.card A * (base.cayley.degree + 1) - 1 := by
  exact card_generators base.cayley.zero_not_mem

/-- The lifted generators span the product whenever the base Cayley
generators span the base group. -/
theorem cayley_generators_span
    (base : CayleyComplex (V := Gamma))
    (hspan : Submodule.span F₂ (base.cayley.generators : Set Gamma) = ⊤) :
    Submodule.span F₂
      (generators (A := A) base.cayley.generators : Set (Gamma × A)) = ⊤ :=
  span_generators_eq_top hspan

end WeightedLift

end HDXLean
