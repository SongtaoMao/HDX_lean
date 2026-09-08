import HDXLean.AlgebraicGeometry
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Evaluation directions: the linear-algebra bridge in Section 4

This file proves the paper-owned deductions from evaluations on a finite
dimensional function space: zero bounds imply dual spanning and distance,
and a two-point Riemann--Roch dimension drop implies projective separation.
No direction set, spanning certificate, or distance conclusion is assumed.
The geometric Riemann--Roch and zero-divisor facts remain separate inputs
to these general lemmas; constructing them for the actual curve is a
distinct integration obligation.
-/

namespace HDXLean.RiemannRochEvaluation

open scoped BigOperators

variable {F W I : Type*} [Field F] [DecidableEq F] [AddCommGroup W] [Module F W]
  [FiniteDimensional F W] [Fintype I]

omit [DecidableEq F] [FiniteDimensional F W] [Fintype I] in
/-- A strict two-point dimension drop produces a section vanishing at one
point and not the other. This is linear algebra, not an additional RR axiom. -/
theorem separates_of_kernel_finrank_lt (e : I → Module.Dual F W)
    {i j : I}
    (hdim : Module.finrank F (LinearMap.ker (e j) ⊓ LinearMap.ker (e i) : Submodule F W) <
      Module.finrank F (LinearMap.ker (e j))) :
    ∃ w : W, e j w = 0 ∧ e i w ≠ 0 := by
  have hlt : LinearMap.ker (e j) ⊓ LinearMap.ker (e i) < LinearMap.ker (e j) := by
    refine lt_iff_le_and_ne.mpr ⟨inf_le_left, ?_⟩
    intro heq
    rw [heq] at hdim
    exact (lt_irrefl _ hdim)
  obtain ⟨w, hj, hi⟩ := SetLike.exists_of_lt hlt
  refine ⟨w, hj, ?_⟩
  intro he
  exact hi ⟨hj, he⟩

/-- Nonzero functions cannot vanish at every selected point once there are
more points than the zero-divisor bound. Hence the evaluations span the dual. -/
theorem span_evaluations_eq_top (e : I → Module.Dual F W) (zeroBound : ℕ)
    (hpoints : zeroBound < Fintype.card I)
    (hzeros : ∀ w : W, w ≠ 0 →
      (Finset.univ.filter fun i ↦ e i w = 0).card ≤ zeroBound) :
    Submodule.span F (Set.range e) = ⊤ := by
  classical
  apply Submodule.span_eq_top_of_ne_zero
  intro w hw
  have hex : ∃ i, e i w ≠ 0 := by
    by_contra! he
    have hz := hzeros w hw
    simp only [he, Finset.filter_true, Finset.card_univ] at hz
    omega
  obtain ⟨i, hi⟩ := hex
  exact ⟨e i, ⟨i, rfl⟩, hi⟩

omit [DecidableEq F] [FiniteDimensional F W] [Fintype I] in
/-- Constant-one evaluation makes every selected evaluation nonzero. -/
theorem evaluation_ne_zero (e : I → Module.Dual F W) (one : W)
    (hone : ∀ i, e i one = 1) (i : I) : e i ≠ 0 := by
  intro he
  have h := hone i
  rw [he, LinearMap.zero_apply] at h
  exact zero_ne_one h

omit [DecidableEq F] [FiniteDimensional F W] [Fintype I] in
/-- The separating section, rather than an assumed projective-distinctness
certificate, rules out proportional evaluations at different points. -/
theorem evaluations_projectively_distinct (e : I → Module.Dual F W)
    (hsep : ∀ i j, i ≠ j → ∃ w : W, e j w = 0 ∧ e i w ≠ 0)
    {i j : I} {c : F} (he : e i = c • e j) : i = j := by
  by_contra hij
  obtain ⟨w, hj, hi⟩ := hsep i j hij
  apply hi
  rw [he, LinearMap.smul_apply, hj, smul_zero]

/-- The literal coordinate representatives of the selected evaluations.
The coordinate equivalence only chooses a basis; it supplies no geometric
spanning, separation or distance assertion. -/
noncomputable def directions {t : ℕ} (e : I → Module.Dual F W)
    (coordinates : Module.Dual F W ≃ₗ[F] CoordinateSpace F t)
    (one : W) (hone : ∀ i, e i one = 1)
    (hsep : ∀ i j, i ≠ j → ∃ w : W, e j w = 0 ∧ e i w ≠ 0)
    (zeroBound : ℕ) (hpoints : zeroBound < Fintype.card I)
    (hzeros : ∀ w : W, w ≠ 0 →
      (Finset.univ.filter fun i ↦ e i w = 0).card ≤ zeroBound) :
    DirectionSet F t I where
  representative i := coordinates (e i)
  representative_ne_zero i := by
    intro he
    apply evaluation_ne_zero e one hone i
    apply coordinates.injective
    simpa using he
  projectivelyDistinct := by
    intro i j c _hc he
    apply evaluations_projectively_distinct e hsep
    apply coordinates.injective
    simpa only [map_smul] using he
  spans := by
    have hspan := span_evaluations_eq_top e zeroBound hpoints hzeros
    rw [show Set.range (fun i ↦ coordinates (e i)) =
      coordinates.toLinearMap '' Set.range e by ext x; simp]
    rw [← Submodule.map_span, hspan, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr coordinates.surjective

/-- The zero-divisor bound gives the distance of the actual direction set.
Reflexivity identifies every functional on the dual with evaluation at a
function; thus no arbitrary coordinate functional is left untreated. -/
theorem directions_distance {t : ℕ} (e : I → Module.Dual F W)
    (coordinates : Module.Dual F W ≃ₗ[F] CoordinateSpace F t)
    (one : W) (hone : ∀ i, e i one = 1)
    (hsep : ∀ i j, i ≠ j → ∃ w : W, e j w = 0 ∧ e i w ≠ 0)
    (zeroBound : ℕ) (hpoints : zeroBound < Fintype.card I)
    (hzeros : ∀ w : W, w ≠ 0 →
      (Finset.univ.filter fun i ↦ e i w = 0).card ≤ zeroBound) :
    HasLowerDistance F
      (directions e coordinates one hone hsep zeroBound hpoints hzeros)
      (Fintype.card I - zeroBound) := by
  classical
  intro functional hf
  let phi : Module.Dual F (Module.Dual F W) :=
    functional.comp coordinates.toLinearMap
  obtain ⟨w, hw⟩ := (Module.evalEquiv F W).surjective phi
  have hwne : w ≠ 0 := by
    intro hwzero
    apply hf
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := coordinates.surjective x
    have he := LinearMap.congr_fun hw y
    simpa [hwzero, phi] using he.symm
  have heval (i : I) : functional (coordinates (e i)) = e i w := by
    have he := LinearMap.congr_fun hw (e i)
    exact he.symm
  have hz := hzeros w hwne
  have hcount := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset I)) (p := fun i ↦ e i w = 0)
  simp only [Finset.card_univ] at hcount
  simp only [directionWeight, directions]
  simp_rw [heval]
  have heq : (Finset.univ.filter fun i ↦ ¬ e i w = 0) =
      (Finset.univ.filter fun i ↦ e i w ≠ 0) := by ext i; simp
  rw [heq] at hcount
  omega

/-- A coordinate choice for the dual is obtained from its dimension, not
supplied together with hidden geometric properties. -/
noncomputable def dualCoordinates {t : ℕ} (hdim : Module.finrank F W = t) :
    Module.Dual F W ≃ₗ[F] CoordinateSpace F t :=
  LinearEquiv.ofFinrankEq (R := F) (Module.Dual F W) (CoordinateSpace F t) (by
    simpa only [Subspace.dual_finrank_eq, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] using hdim)

/-- Specialization of the evaluation construction to `G = 3g P_infinity`.
The inputs are function-space dimensions and a zero bound, not the final
direction-set certificate. Their geometric derivation must be provided by
the separately formulated RR/zero-divisor literature interface. -/
noncomputable def riemannRochLevel [Fintype F]
    (P : SquareFieldParameters F) (g : ℕ) (hg : 4 ≤ g)
    (e : Fin ((P.q - 2) * g) → Module.Dual F W)
    (hdim : Module.finrank F W = 2 * g + 1)
    (one : W) (hone : ∀ i, e i one = 1)
    (hdrop : ∀ i j, i ≠ j →
      Module.finrank F (LinearMap.ker (e j) ⊓ LinearMap.ker (e i) : Submodule F W) <
        Module.finrank F (LinearMap.ker (e j)))
    (hzeros : ∀ w : W, w ≠ 0 →
      (Finset.univ.filter fun i ↦ e i w = 0).card ≤ 3 * g)
    (coordinates : Module.Dual F W ≃ₗ[F] CoordinateSpace F (2 * g + 1) :=
      dualCoordinates hdim) :
    RiemannRochLevelInput P g := by
  have hq : 6 ≤ P.q - 2 := by have := P.q_ge_eight; omega
  have hpoints : 3 * g < Fintype.card (Fin ((P.q - 2) * g)) := by
    rw [Fintype.card_fin]
    have := Nat.mul_le_mul_right g hq
    omega
  have hsep : ∀ i j, i ≠ j → ∃ w : W, e j w = 0 ∧ e i w ≠ 0 :=
    fun i j hij ↦ separates_of_kernel_finrank_lt e (hdrop i j hij)
  let coord := coordinates
  refine { t := 2 * g + 1, t_eq := rfl
           directions := directions e coord one hone hsep (3 * g) hpoints hzeros
           zeroDivisorDistance := ?_ }
  have hdist := directions_distance e coord one hone hsep (3 * g) hpoints hzeros
  have hsub : Fintype.card (Fin ((P.q - 2) * g)) - 3 * g = (P.q - 5) * g := by
    rw [Fintype.card_fin, ← Nat.sub_mul]
    congr 1
  simpa only [hsub] using hdist

end HDXLean.RiemannRochEvaluation
