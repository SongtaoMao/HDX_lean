import HDXLean.CharTwoTriples
import HDXLean.RelationMatrix
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Order

/-!
# Kernel separation forces row-code distance three

This file supplies the final, purely linear-algebraic step of Lemma 3.6.  It
does not depend on the special relation matrix: any binary matrix whose kernel
detects every coordinate and separates every pair of coordinates has row-code
minimum distance at least three.
-/

namespace HDXLean

open scoped BigOperators

namespace KernelDistance

variable {R C : Type*} [Fintype R] [DecidableEq R]
  [Fintype C] [DecidableEq C]

/-- The standard binary dot product. -/
def dot (x y : C → F₂) : F₂ :=
  ∑ c : C, x c * y c

/-- Support of a binary vector. -/
def support (x : C → F₂) : Finset C :=
  Finset.univ.filter fun c ↦ x c ≠ 0

omit [DecidableEq C] in
@[simp]
theorem card_support (x : C → F₂) : (support x).card = hammingWeight x :=
  rfl

omit [DecidableEq C] in
theorem dot_eq_sum_support (x y : C → F₂) :
    dot x y = ∑ c ∈ support x, x c * y c := by
  classical
  rw [dot, support, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : x c = 0 <;> simp [hc]

omit [Fintype R] [DecidableEq R] [DecidableEq C] in
theorem rowCode_dot_kernel_zero (H : BinaryMatrix R C)
    {rowWord kernelWord : C → F₂}
    (hrow : rowWord ∈ rowCode H)
    (hkernel : kernelWord ∈ RelationMatrix.kernel H) :
    dot rowWord kernelWord = 0 := by
  have hmap : RelationMatrix.linearMap H kernelWord = 0 :=
    LinearMap.mem_ker.mp hkernel
  refine Submodule.span_induction (p := fun y _ ↦ dot y kernelWord = 0) ?_ ?_ ?_ ?_ hrow
  · intro y hy
    obtain ⟨r, rfl⟩ := hy
    have hr := congrFun hmap r
    simpa [dot, RelationMatrix.linearMap, RelationMatrix.apply] using hr
  · simp [dot]
  · intro x y _ _ hx hy
    calc
      dot (x + y) kernelWord = dot x kernelWord + dot y kernelWord := by
        simp [dot, add_mul, Finset.sum_add_distrib]
      _ = 0 := by rw [hx, hy, add_zero]
  · intro a x _ hx
    calc
      dot (a • x) kernelWord = a * dot x kernelWord := by
        simp [dot, Finset.mul_sum, mul_assoc]
      _ = 0 := by rw [hx, mul_zero]

omit [DecidableEq C] in
/-- Every nonzero vector has nonempty support. -/
theorem support_nonempty {x : C → F₂} (hx : x ≠ 0) :
    (support x).Nonempty := by
  classical
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  apply hx
  funext c
  have hc : c ∉ support x := by simp [hempty]
  simpa [support] using hc

/-- Kernel detection and pair separation, in the exact quantifier order used
by the proof of Lemma 3.6. -/
structure SeparatesCoordinates (H : BinaryMatrix R C) : Prop where
  detects : ∀ c, ∃ x, x ∈ RelationMatrix.kernel H ∧ x c ≠ 0
  separates : ∀ c c', c ≠ c' →
    ∃ x, x ∈ RelationMatrix.kernel H ∧ x c ≠ x c'

omit [Fintype R] [DecidableEq R] in
/-- The separation conclusion of Lemma 3.6 implies minimum distance at least
three for the binary row code. -/
theorem rowDistanceAtLeastThree_of_separates
    (H : BinaryMatrix R C) (hsep : SeparatesCoordinates H) :
    RowDistanceAtLeastThree H := by
  intro y hyRow hyNonzero
  by_contra hnot
  have hlt : hammingWeight y < 3 := Nat.lt_of_not_ge hnot
  have hpos : 0 < hammingWeight y := by
    simpa [← card_support] using Finset.card_pos.mpr (support_nonempty hyNonzero)
  have hcases : hammingWeight y = 1 ∨ hammingWeight y = 2 := by omega
  rcases hcases with hone | htwo
  · have hsCard : (support y).card = 1 := by
      rw [card_support]
      exact hone
    obtain ⟨c, hsupport⟩ := Finset.card_eq_one.mp hsCard
    change support y = {c} at hsupport
    obtain ⟨x, hxKernel, hxc⟩ := hsep.detects c
    have hyc : y c ≠ 0 := by
      have hcMem : c ∈ support y := by rw [hsupport]; simp
      exact (Finset.mem_filter.mp hcMem).2
    have hdotZero := rowCode_dot_kernel_zero H hyRow hxKernel
    have hdot : dot y x = y c * x c := by
      rw [dot_eq_sum_support]
      have hsum := congrArg (fun s : Finset C ↦ s.sum fun z ↦ y z * x z) hsupport
      simpa using hsum
    exact (mul_ne_zero hyc hxc) (hdot ▸ hdotZero)
  · have hsCard : (support y).card = 2 := by
      rw [card_support]
      exact htwo
    obtain ⟨c, c', hcc', hsupport⟩ := Finset.card_eq_two.mp hsCard
    change support y = {c, c'} at hsupport
    obtain ⟨x, hxKernel, hxcc'⟩ := hsep.separates c c' hcc'
    have hyc : y c ≠ 0 := by
      have hcMem : c ∈ support y := by rw [hsupport]; simp
      exact (Finset.mem_filter.mp hcMem).2
    have hyc' : y c' ≠ 0 := by
      have hcMem : c' ∈ support y := by rw [hsupport]; simp
      exact (Finset.mem_filter.mp hcMem).2
    have hycOne : y c = 1 := Fin.eq_one_of_ne_zero (y c) hyc
    have hyc'One : y c' = 1 := Fin.eq_one_of_ne_zero (y c') hyc'
    have hsum : x c + x c' ≠ 0 :=
      (CharTwoTriples.add_eq_zero_iff_eq (x c) (x c')).not.mpr hxcc'
    have hdotZero := rowCode_dot_kernel_zero H hyRow hxKernel
    have hdot : dot y x = x c + x c' := by
      rw [dot_eq_sum_support]
      have hsum := congrArg (fun s : Finset C ↦ s.sum fun z ↦ y z * x z) hsupport
      simpa [hcc', hycOne, hyc'One] using hsum
    exact hsum (hdot ▸ hdotZero)

end KernelDistance

end HDXLean
