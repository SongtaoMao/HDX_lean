import HDXLean.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Fintype.BigOperators

/-!
# Multilinear interpolation on the Boolean cube

This file proves the internal interpolation fact used in Proposition 4.7:
a multilinear polynomial is determined by its values on `{0,1}^t`.  We use
the squarefree-monomial coefficient model, indexed by finite subsets of the
coordinate set, so the proof is finite and characteristic-independent.
-/

namespace HDXLean

open scoped BigOperators

namespace BooleanCube

variable {F : Type*} [CommRing F]

/-- Coefficients of a multilinear polynomial in `t` variables, indexed by
its squarefree monomials. -/
abbrev Coefficients (t : ℕ) := Finset (Fin t) → F

/-- The Boolean point associated with a set of active coordinates. -/
def point {t : ℕ} (T : Finset (Fin t)) : Fin t → F :=
  fun i ↦ if i ∈ T then 1 else 0

/-- Evaluation of the squarefree-monomial expansion. -/
noncomputable def evaluate {t : ℕ} (c : Coefficients (F := F) t)
    (x : Fin t → F) : F :=
  ∑ S : Finset (Fin t), c S * ∏ i ∈ S, x i

theorem monomial_point {t : ℕ} (S T : Finset (Fin t)) :
    (∏ i ∈ S, point (F := F) T i) = if S ⊆ T then 1 else 0 := by
  classical
  by_cases hsubset : S ⊆ T
  · rw [if_pos hsubset]
    apply Finset.prod_eq_one
    intro i hi
    simp [point, hsubset hi]
  · rw [if_neg hsubset]
    obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hsubset
    apply Finset.prod_eq_zero hiS
    simp [point, hiT]

/-- Evaluation at the Boolean point `1_T` is the sum of all coefficients
whose monomials are contained in `T`. -/
theorem evaluate_point {t : ℕ} (c : Coefficients (F := F) t)
    (T : Finset (Fin t)) :
    evaluate c (point T) = ∑ S ∈ T.powerset, c S := by
  classical
  unfold evaluate
  simp_rw [monomial_point]
  rw [show (∑ S : Finset (Fin t), c S * if S ⊆ T then 1 else 0) =
      ∑ S : Finset (Fin t), if S ⊆ T then c S else 0 by
    apply Finset.sum_congr rfl
    intro S _hS
    split_ifs <;> simp]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext S
    simp
  · intro S _hS
    rfl

/-- Multilinear coefficient vectors are determined by their Boolean-cube
values. -/
theorem evaluate_on_points_injective {t : ℕ} :
    Function.Injective
      (fun c : Coefficients (F := F) t ↦ fun T : Finset (Fin t) ↦
        evaluate c (point T)) := by
  classical
  intro c d heval
  funext T
  induction T using Finset.strongInduction with
  | H T ih =>
      have hsum := congrFun heval T
      change evaluate c (point T) = evaluate d (point T) at hsum
      rw [evaluate_point, evaluate_point] at hsum
      have hTmem : T ∈ T.powerset := Finset.mem_powerset.mpr Finset.Subset.rfl
      rw [← Finset.sum_erase_add _ _ hTmem,
        ← Finset.sum_erase_add _ _ hTmem] at hsum
      have hlower :
          (∑ S ∈ T.powerset.erase T, c S) =
            ∑ S ∈ T.powerset.erase T, d S := by
        apply Finset.sum_congr rfl
        intro S hS
        have hsubset : S ⊆ T :=
          Finset.mem_powerset.mp (Finset.mem_of_mem_erase hS)
        have hne : S ≠ T := Finset.ne_of_mem_erase hS
        exact ih S (Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hne⟩)
      rw [hlower] at hsum
      exact add_left_cancel hsum

/-- Evaluation of squarefree coefficient vectors as a linear map to all
functions on the ambient coordinate space. -/
noncomputable def evaluationLinear (t : ℕ) :
    Coefficients (F := F) t →ₗ[F] ((Fin t → F) → F) where
  toFun c := evaluate c
  map_add' c d := by
    funext x
    change evaluate (c + d) x = evaluate c x + evaluate d x
    unfold evaluate
    simp only [Pi.add_apply, add_mul]
    rw [Finset.sum_add_distrib]
  map_smul' a c := by
    funext x
    change evaluate (a • c) x = a • evaluate c x
    unfold evaluate
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _hS
    ring

/-- The full evaluation linear map is injective, since its restriction to
the Boolean cube already determines every coefficient. -/
theorem evaluationLinear_injective (t : ℕ) :
    Function.Injective (evaluationLinear (F := F) t) := by
  intro c d heval
  apply evaluate_on_points_injective
  funext T
  exact congrFun heval (point T)

end BooleanCube

end HDXLean
