import HDXLean.CurveRiemannRochCited
import HDXLean.EvaluationProductRealization
import Mathlib.Data.Fin.Embedding

/-!
# Applying the cited curve facts at a Section 4 level

This file only specializes the stated RR and zero-divisor inputs. It selects
the required rational points, proves the one- and two-point dimension drop,
and feeds one common evaluation basis to the existing direction and minor
constructions. It does not prove Riemann--Roch or geometric integrality.
-/

namespace HDXLean.CurveRiemannRochLevel

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct
open CurveRiemannRochCited

universe u v

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {K : Type v} [Field K] [IsAlgClosed K] [Algebra F K]
variable {g : ℕ} (data : OnePointData F K g)

/-- Select distinct rational points from the cited point-count bound. -/
noncomputable def selectedPoints {n : ℕ} (hn : n ≤ Fintype.card data.Point) :
    Fin n ↪ data.Point :=
  (Fin.castLEEmb hn).trans (Fintype.equivFin data.Point).symm.toEmbedding

/-- RR with no imposed zeros gives the exact dimension used for `W`. -/
theorem ambient_finrank (m : ℕ) (hm : m = 3 * g) :
    Module.finrank F (data.space m) = 2 * g + 1 := by
  have hrr := data.rr_vanishing m ∅ (by simp only [Finset.card_empty]; omega)
  have hempty : vanishingSpace (data.space m) data.evaluation ∅ = ⊤ := rfl
  rw [hempty] at hrr
  have htop : Module.finrank F (⊤ : Submodule F (data.space m)) =
      Module.finrank F (data.space m) := finrank_top F (data.space m)
  rw [htop] at hrr
  simp only [Finset.card_empty, Nat.sub_zero] at hrr
  omega

/-- RR with one and two distinct imposed zeros gives the strict kernel
dimension drop. These are applications of the citation, not a new RR proof. -/
theorem kernel_drop (m : ℕ) (hm : m = 3 * g) (hg : 4 ≤ g)
    (p q : data.Point) (hpq : p ≠ q) :
    Module.finrank F
        (LinearMap.ker (data.eval m q) ⊓ LinearMap.ker (data.eval m p) :
          Submodule F (data.space m)) <
      Module.finrank F (LinearMap.ker (data.eval m q)) := by
  have hsingle := data.rr_vanishing m {q} (by simp only [Finset.card_singleton]; omega)
  have hcard : ({q, p} : Finset data.Point).card = 2 := by
    simp [Ne.symm hpq]
  have hdouble := data.rr_vanishing m {q, p} (by rw [hcard]; omega)
  have hvan_single : vanishingSpace (data.space m) data.evaluation {q} =
      LinearMap.ker (data.eval m q) :=
    Finset.inf_singleton
  have hvan_double : vanishingSpace (data.space m) data.evaluation {q, p} =
      LinearMap.ker (data.eval m q) ⊓ LinearMap.ker (data.eval m p) := by
    change ({q, p} : Finset data.Point).inf (fun x ↦ LinearMap.ker (data.eval m x)) = _
    rw [Finset.inf_insert, Finset.inf_singleton]
  rw [hvan_single, Finset.card_singleton] at hsingle
  rw [hvan_double, hcard] at hdouble
  change Module.finrank F (LinearMap.ker (data.eval m q)) = m + 1 - g - 1 at hsingle
  change Module.finrank F
      (LinearMap.ker (data.eval m q) ⊓ LinearMap.ker (data.eval m p) :
        Submodule F (data.space m)) = m + 1 - g - 2 at hdouble
  omega

/-- Restricting to an injectively selected point family cannot increase
the number of zeros. -/
theorem selected_zero_bound {n : ℕ} (selected : Fin n ↪ data.Point)
    (m : ℕ) (w : data.space m) (hw : w ≠ 0) :
    (Finset.univ.filter fun i ↦ data.eval m (selected i) w = 0).card ≤ m := by
  classical
  apply le_trans _ (data.zero_bound m w hw)
  apply Finset.card_le_card_of_injOn selected
  · intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (Finset.mem_filter.mp hi).2
  · exact selected.injective.injOn

/-- Complete one-level construction from the precisely stated curve/RR
citations and Eisenbud's determinantal input. No basis, direction set,
function family, matrix, genericity, or minor-independence conclusion is
supplied independently by the caller. -/
noncomputable def levelWithMinors (P : SquareFieldParameters F) (data : OnePointData F K g)
    (hg : 4 ≤ g) (hpoints : (P.q - 2) * g ≤ Fintype.card data.Point)
    (eisenbud : OneGenericMatrix.EisenbudMinimalGeneratorsInput.{v,0} K) :
    Σ level : RiemannRochLevelInput P g, ConcreteMaximalMinorLevelData P level := by
  classical
  let a := SectionFourSubspaces.degreeA g
  let b := SectionFourSubspaces.degreeB g
  let m := a + b
  have hm : m = 3 * g := SectionFourSubspaces.degreeA_add_degreeB g
  let W := data.space m
  let selected := selectedPoints data hpoints
  let e : Fin ((P.q - 2) * g) → Module.Dual F W :=
    fun i ↦ data.eval m (selected i)
  have hdim : Module.finrank F W = 2 * g + 1 := ambient_finrank data m hm
  have hone : ∀ i, e i (data.one m) = 1 := fun i ↦ data.eval_one m (selected i)
  have hdrop : ∀ i j, i ≠ j →
      Module.finrank F (LinearMap.ker (e j) ⊓ LinearMap.ker (e i) : Submodule F W) <
        Module.finrank F (LinearMap.ker (e j)) := by
    intro i j hij
    exact kernel_drop data m hm hg (selected i) (selected j) (selected.injective.ne hij)
  have hzeros : ∀ w : W, w ≠ 0 →
      (Finset.univ.filter fun i ↦ e i w = 0).card ≤ 3 * g := by
    intro w hw
    exact (selected_zero_bound data selected m w hw).trans_eq hm
  have hmany : 3 * g < Fintype.card (Fin ((P.q - 2) * g)) := by
    have hq : 6 ≤ P.q - 2 := by have := P.q_ge_eight; omega
    have hmul := Nat.mul_le_mul_right g hq
    simp only [Fintype.card_fin]
    omega
  have hspan : Submodule.span F (Set.range e) = ⊤ :=
    RiemannRochEvaluation.span_evaluations_eq_top e (3 * g) hmany hzeros
  let hBasis := EvaluationMultiplication.exists_evaluation_basis e hspan hdim
  let basis := Classical.choose hBasis
  have hbasis := Classical.choose_spec hBasis
  let level := RiemannRochEvaluation.riemannRochLevel P g hg e hdim
    (data.one m) hone hdrop hzeros basis.equivFun
  let families := SectionFourSubspaces.selectFamilies F (data.space a) (data.space b) g
    (data.rr_lower a) (data.rr_lower b)
  refine ⟨level, ?_⟩
  refine EvaluationProductRealization.concreteLevelFromEvaluationBasis P level
    (SectionFourSubspaces.rowCount_pos g hg) basis (data.multiplication a b)
    families.row families.column families.row_independent families.column_independent
    e (fun i ↦ data.eval a (selected i)) (fun i ↦ data.eval b (selected i))
    (fun i x y ↦ data.eval_multiplication a b (selected i) x y)
    hbasis (fun i ↦ rfl)
    (data.space a).subtype (data.space b).subtype (data.space m).subtype
    (data.space a).injective_subtype (data.space b).injective_subtype
    (fun x y ↦ rfl) eisenbud

end HDXLean.CurveRiemannRochLevel
