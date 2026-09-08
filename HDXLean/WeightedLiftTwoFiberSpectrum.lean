import HDXLean.WeightedLiftSpectrum
import HDXLean.WeightedLiftLinks
import HDXLean.WeightedGraphScaling
import HDXLean.Relabeling

/-!
# The two-occupied-fiber conditioned walk

This file formalizes the middle row of the spectral table on page 15.  A
codimension-two face meeting two base fibers with positive occupancies `a`
and `b` has `a + b = d - 1`.  Its link splits into the unused labels in the
two occupied fibers and the labeled fibers above possible third vertices.

The model below keeps the conditional distribution of possible third
vertices as an arbitrary positive probability `omega`.  Thus the calculation
also covers a non-uniform weighted base complex.  The edge weights are the
conditioned weights after deleting their common positive normalization.
-/

namespace HDXLean

open scoped BigOperators

namespace WeightedLift

universe u

/-- Vertices in the conditioned link: unused labels in the first occupied
fiber, unused labels in the second one, and a label over a possible third
base vertex. -/
abbrev TwoFiberVertex (Z : Type u) (m a b : ℕ) :=
  Fin (m - a) ⊕ (Fin (m - b) ⊕ (Z × Fin m))

/-- Numerical data for a codimension-two face meeting exactly two fibers.
`omega` is the conditional distribution of the possible third base vertex. -/
structure TwoFiberData (Z : Type u) [Fintype Z] (d m a b : ℕ) where
  hd : 3 ≤ d
  hm : 2 * d ≤ m
  ha : 0 < a
  hb : 0 < b
  occupancy_sum : a + b = d - 1
  omega : Z → ℝ
  omega_pos : ∀ z, 0 < omega z
  omega_sum : ∑ z : Z, omega z = 1

namespace TwoFiberData

variable {Z : Type u} [Fintype Z] {d m a b : ℕ}

theorem a_le_d_sub_two (D : TwoFiberData Z d m a b) : a ≤ d - 2 := by
  have hd := D.hd
  have hb := D.hb
  have hab := D.occupancy_sum
  omega

theorem b_le_d_sub_two (D : TwoFiberData Z d m a b) : b ≤ d - 2 := by
  have hd := D.hd
  have ha := D.ha
  have hab := D.occupancy_sum
  omega

theorem a_lt_m (D : TwoFiberData Z d m a b) : a < m := by
  have hd := D.hd
  have hm := D.hm
  have haBound := D.a_le_d_sub_two
  omega

theorem b_lt_m (D : TwoFiberData Z d m a b) : b < m := by
  have hd := D.hd
  have hm := D.hm
  have hbBound := D.b_le_d_sub_two
  omega

theorem one_lt_m_sub_a (D : TwoFiberData Z d m a b) : 1 < m - a := by
  have hd := D.hd
  have hm := D.hm
  have haBound := D.a_le_d_sub_two
  omega

theorem one_lt_m_sub_b (D : TwoFiberData Z d m a b) : 1 < m - b := by
  have hd := D.hd
  have hm := D.hm
  have hbBound := D.b_le_d_sub_two
  omega

theorem one_lt_m (D : TwoFiberData Z d m a b) : 1 < m := by
  have hd := D.hd
  have hm := D.hm
  omega

theorem d_pos (D : TwoFiberData Z d m a b) : 0 < d := by
  have hd := D.hd
  omega

theorem d_add_one_pos (_D : TwoFiberData Z d m a b) : 0 < d + 1 := by omega

end TwoFiberData

section Model

variable {Z : Type u} [Fintype Z] [DecidableEq Z]
  {d m a b : ℕ}

/-- The exact symmetric conditioned edge weights, with their common global
factor removed. -/
noncomputable def twoFiberEdgeWeight (D : TwoFiberData Z d m a b)
    (u v : TwoFiberVertex Z m a b) : ℝ :=
  match u, v with
  | Sum.inl i, Sum.inl j =>
      if i = j then 0 else
        (a : ℝ) * (a + 1 : ℕ) /
          ((m - a : ℕ) * (m - a - 1 : ℕ))
  | Sum.inl _, Sum.inr (Sum.inl _) =>
      (a : ℝ) * b / ((m - a : ℕ) * (m - b : ℕ))
  | Sum.inr (Sum.inl _), Sum.inl _ =>
      (a : ℝ) * b / ((m - a : ℕ) * (m - b : ℕ))
  | Sum.inl _, Sum.inr (Sum.inr (z, _)) =>
      (a : ℝ) * D.omega z / ((m - a : ℕ) * m)
  | Sum.inr (Sum.inr (z, _)), Sum.inl _ =>
      (a : ℝ) * D.omega z / ((m - a : ℕ) * m)
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j) =>
      if i = j then 0 else
        (b : ℝ) * (b + 1 : ℕ) /
          ((m - b : ℕ) * (m - b - 1 : ℕ))
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr (z, _)) =>
      (b : ℝ) * D.omega z / ((m - b : ℕ) * m)
  | Sum.inr (Sum.inr (z, _)), Sum.inr (Sum.inl _) =>
      (b : ℝ) * D.omega z / ((m - b : ℕ) * m)
  | Sum.inr (Sum.inr (z, i)), Sum.inr (Sum.inr (w, j)) =>
      if z = w ∧ i ≠ j then
        D.omega z / ((m : ℝ) * (m - 1 : ℕ))
      else 0

theorem twoFiberEdgeWeight_symm (D : TwoFiberData Z d m a b)
    (u v : TwoFiberVertex Z m a b) :
    twoFiberEdgeWeight D u v = twoFiberEdgeWeight D v u := by
  rcases u with i | u <;> rcases v with j | v
  · simp only [twoFiberEdgeWeight]
    by_cases h : i = j
    · subst j; simp
    · simp [h, Ne.symm h]
  · rcases v with j | v <;> simp [twoFiberEdgeWeight]
  · rcases u with i | u <;> simp [twoFiberEdgeWeight]
  · rcases u with i | ⟨z, i⟩ <;> rcases v with j | ⟨w, j⟩
    · simp only [twoFiberEdgeWeight]
      by_cases h : i = j
      · subst j; simp
      · simp [h, Ne.symm h]
    · simp [twoFiberEdgeWeight]
    · simp [twoFiberEdgeWeight]
    · simp only [twoFiberEdgeWeight]
      by_cases hzw : z = w
      · subst w
        by_cases hij : i = j
        · subst j; simp
        · simp [hij, Ne.symm hij]
      · simp [hzw, Ne.symm hzw]

theorem twoFiberEdgeWeight_self (D : TwoFiberData Z d m a b)
    (u : TwoFiberVertex Z m a b) : twoFiberEdgeWeight D u u = 0 := by
  rcases u with i | u
  · simp [twoFiberEdgeWeight]
  · rcases u with j | ⟨z, k⟩ <;> simp [twoFiberEdgeWeight]

theorem twoFiberEdgeWeight_nonneg (D : TwoFiberData Z d m a b)
    (u v : TwoFiberVertex Z m a b) : 0 ≤ twoFiberEdgeWeight D u v := by
  rcases u with i | u <;> rcases v with j | v
  · simp only [twoFiberEdgeWeight]
    split_ifs <;> positivity
  · rcases v with j | ⟨z, k⟩
    · simp only [twoFiberEdgeWeight]; positivity
    · have hz : 0 ≤ D.omega z := (D.omega_pos z).le
      simp only [twoFiberEdgeWeight]
      positivity
  · rcases u with i | ⟨z, k⟩
    · simp only [twoFiberEdgeWeight]; positivity
    · have hz : 0 ≤ D.omega z := (D.omega_pos z).le
      simp only [twoFiberEdgeWeight]
      positivity
  · rcases u with i | ⟨z, k⟩ <;> rcases v with j | ⟨w, l⟩
    · simp only [twoFiberEdgeWeight]
      split_ifs <;> positivity
    · have hw : 0 ≤ D.omega w := (D.omega_pos w).le
      simp only [twoFiberEdgeWeight]
      positivity
    · have hz : 0 ≤ D.omega z := (D.omega_pos z).le
      simp only [twoFiberEdgeWeight]
      positivity
    · simp only [twoFiberEdgeWeight]
      split_ifs
      · have hz : 0 ≤ D.omega z := (D.omega_pos z).le
        positivity
      · positivity

/-- The concrete weighted graph realizing the conditioned walk. -/
noncomputable def twoFiberGraph (D : TwoFiberData Z d m a b) :
    WeightedGraph (TwoFiberVertex Z m a b) where
  weight := twoFiberEdgeWeight D
  weight_symm := twoFiberEdgeWeight_symm D
  weight_self := twoFiberEdgeWeight_self D
  weight_nonneg := twoFiberEdgeWeight_nonneg D

/-- Every vertex in the first occupied fiber has the same stationary degree. -/
theorem twoFiberGraph_degree_left (D : TwoFiberData Z d m a b)
    (i : Fin (m - a)) :
    (twoFiberGraph D).degree (Sum.inl i) =
      (a : ℝ) * (d + 1 : ℕ) / (m - a : ℕ) := by
  classical
  unfold WeightedGraph.degree twoFiberGraph
  simp only [Fintype.sum_sum_type, twoFiberEdgeWeight]
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, Finset.card_filter,
    Finset.filter_ne, Finset.card_erase_of_mem, Finset.mem_univ,
    Finset.card_univ, Fintype.card_fin, Fintype.sum_prod_type]
  have hmPos : 0 < m := by
    have hmOne := D.one_lt_m
    omega
  have hmaPos : 0 < m - a := Nat.sub_pos_of_lt D.a_lt_m
  have hmbPos : 0 < m - b := Nat.sub_pos_of_lt D.b_lt_m
  have hmaOnePos : 0 < m - a - 1 := Nat.sub_pos_of_lt D.one_lt_m_sub_a
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hmPos.ne'
  have hma0 : ((m - a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmaPos.ne'
  have hmb0 : ((m - b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmbPos.ne'
  have hmaOne0 : ((m - a - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hmaOnePos.ne'
  have hthird :
      (∑ z : Z, (m : ℝ) *
        ((a : ℝ) * D.omega z / ((m - a : ℕ) * m))) =
        (a : ℝ) / (m - a : ℕ) := by
    calc
      _ = ∑ z : Z, ((a : ℝ) / (m - a : ℕ)) * D.omega z := by
        apply Finset.sum_congr rfl
        intro z _hz
        field_simp
        <;> ring
      _ = ((a : ℝ) / (m - a : ℕ)) * ∑ z : Z, D.omega z := by
        rw [Finset.mul_sum]
      _ = (a : ℝ) / (m - a : ℕ) := by rw [D.omega_sum, mul_one]
  rw [hthird]
  have hdOne : 1 ≤ d := by
    have hd := D.hd
    omega
  have habReal : (a : ℝ) + b = (d : ℝ) - 1 := by
    have h := congrArg (fun n : ℕ ↦ (n : ℝ)) D.occupancy_sum
    simpa only [Nat.cast_add, Nat.cast_sub hdOne, Nat.cast_one] using h
  norm_num only [Nat.cast_add, Nat.cast_one]
  field_simp
  nlinarith

/-- Every vertex in the second occupied fiber has the same stationary degree. -/
theorem twoFiberGraph_degree_right (D : TwoFiberData Z d m a b)
    (i : Fin (m - b)) :
    (twoFiberGraph D).degree (Sum.inr (Sum.inl i)) =
      (b : ℝ) * (d + 1 : ℕ) / (m - b : ℕ) := by
  classical
  unfold WeightedGraph.degree twoFiberGraph
  simp only [Fintype.sum_sum_type, twoFiberEdgeWeight]
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, Finset.card_filter,
    Finset.filter_ne, Finset.card_erase_of_mem, Finset.mem_univ,
    Finset.card_univ, Fintype.card_fin, Fintype.sum_prod_type]
  have hmPos : 0 < m := by
    have hmOne := D.one_lt_m
    omega
  have hmaPos : 0 < m - a := Nat.sub_pos_of_lt D.a_lt_m
  have hmbPos : 0 < m - b := Nat.sub_pos_of_lt D.b_lt_m
  have hmbOnePos : 0 < m - b - 1 := Nat.sub_pos_of_lt D.one_lt_m_sub_b
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hmPos.ne'
  have hma0 : ((m - a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmaPos.ne'
  have hmb0 : ((m - b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmbPos.ne'
  have hmbOne0 : ((m - b - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hmbOnePos.ne'
  have hthird :
      (∑ z : Z, (m : ℝ) *
        ((b : ℝ) * D.omega z / ((m - b : ℕ) * m))) =
        (b : ℝ) / (m - b : ℕ) := by
    calc
      _ = ∑ z : Z, ((b : ℝ) / (m - b : ℕ)) * D.omega z := by
        apply Finset.sum_congr rfl
        intro z _hz
        field_simp
      _ = ((b : ℝ) / (m - b : ℕ)) * ∑ z : Z, D.omega z := by
        rw [Finset.mul_sum]
      _ = (b : ℝ) / (m - b : ℕ) := by rw [D.omega_sum, mul_one]
  rw [hthird]
  have hdOne : 1 ≤ d := by
    have hd := D.hd
    omega
  have habReal : (a : ℝ) + b = (d : ℝ) - 1 := by
    have h := congrArg (fun n : ℕ ↦ (n : ℝ)) D.occupancy_sum
    simpa only [Nat.cast_add, Nat.cast_sub hdOne, Nat.cast_one] using h
  norm_num only [Nat.cast_add, Nat.cast_one]
  field_simp
  nlinarith

/-- A vertex over a possible third base vertex `z` has degree proportional
to its conditional weight. -/
theorem twoFiberGraph_degree_third (D : TwoFiberData Z d m a b)
    (z : Z) (i : Fin m) :
    (twoFiberGraph D).degree (Sum.inr (Sum.inr (z, i))) =
      (d : ℝ) * D.omega z / m := by
  classical
  unfold WeightedGraph.degree twoFiberGraph
  simp only [Fintype.sum_sum_type, twoFiberEdgeWeight]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fin, Fintype.sum_prod_type]
  have hmPos : 0 < m := by
    have hmOne := D.one_lt_m
    omega
  have hmaPos : 0 < m - a := Nat.sub_pos_of_lt D.a_lt_m
  have hmbPos : 0 < m - b := Nat.sub_pos_of_lt D.b_lt_m
  have hmOnePos : 0 < m - 1 := Nat.sub_pos_of_lt D.one_lt_m
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hmPos.ne'
  have hma0 : ((m - a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmaPos.ne'
  have hmb0 : ((m - b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmbPos.ne'
  have hmOne0 : ((m - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmOnePos.ne'
  have hpetal :
      (∑ w : Z, ∑ j : Fin m,
        if z = w ∧ i ≠ j then
          D.omega z / ((m : ℝ) * (m - 1 : ℕ)) else 0) =
        D.omega z / m := by
    rw [Fintype.sum_eq_single z]
    · simp only [true_and]
      simp [Finset.sum_ite, Finset.filter_ne, Finset.card_erase_of_mem]
      field_simp
    · intro w hwz
      have hzw : z ≠ w := Ne.symm hwz
      simp [hzw]
  rw [hpetal]
  have hdOne : 1 ≤ d := by
    have hd := D.hd
    omega
  have habReal : (a : ℝ) + b = (d : ℝ) - 1 := by
    have h := congrArg (fun n : ℕ ↦ (n : ℝ)) D.occupancy_sum
    simpa only [Nat.cast_add, Nat.cast_sub hdOne, Nat.cast_one] using h
  have hcoeff : (a : ℝ) + b + 1 = d := by linarith
  field_simp
  rw [← hcoeff]
  ring

/-! ## Exact random-walk block formula -/

/-- Sum over all labels except the current one. -/
noncomputable def sumExcept {n : ℕ} (i : Fin n) (f : Fin n → ℝ) : ℝ :=
  ∑ j ∈ (Finset.univ.erase i), f j

/-- Average on the unused labels in the first occupied fiber. -/
noncomputable def leftAverage (f : TwoFiberVertex Z m a b → ℝ) : ℝ :=
  (∑ i : Fin (m - a), f (Sum.inl i)) / (m - a : ℕ)

/-- Average on the unused labels in the second occupied fiber. -/
noncomputable def rightAverage (f : TwoFiberVertex Z m a b → ℝ) : ℝ :=
  (∑ i : Fin (m - b), f (Sum.inr (Sum.inl i))) / (m - b : ℕ)

/-- Average inside one possible third fiber. -/
noncomputable def thirdFiberAverage
    (f : TwoFiberVertex Z m a b → ℝ) (z : Z) : ℝ :=
  (∑ i : Fin m, f (Sum.inr (Sum.inr (z, i)))) / m

/-- Conditional weighted average of all possible third fibers. -/
noncomputable def thirdAverage (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) : ℝ :=
  ∑ z : Z, D.omega z * thirdFiberAverage f z

/-- The three-block formula for the normalized conditioned walk. -/
noncomputable def twoFiberOperator (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    TwoFiberVertex Z m a b → ℝ
  | Sum.inl i =>
      (a + 1 : ℕ) / ((d + 1 : ℕ) * (m - a - 1 : ℕ)) *
          sumExcept i (fun j ↦ f (Sum.inl j)) +
        (b : ℝ) / (d + 1 : ℕ) * rightAverage f +
        1 / (d + 1 : ℕ) * thirdAverage D f
  | Sum.inr (Sum.inl i) =>
      (a : ℝ) / (d + 1 : ℕ) * leftAverage f +
        (b + 1 : ℕ) / ((d + 1 : ℕ) * (m - b - 1 : ℕ)) *
          sumExcept i (fun j ↦ f (Sum.inr (Sum.inl j))) +
        1 / (d + 1 : ℕ) * thirdAverage D f
  | Sum.inr (Sum.inr (z, i)) =>
      (a : ℝ) / d * leftAverage f +
        (b : ℝ) / d * rightAverage f +
        1 / ((d : ℝ) * (m - 1 : ℕ)) *
          sumExcept i (fun j ↦ f (Sum.inr (Sum.inr (z, j))))

private theorem weightedSum_left (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) (i : Fin (m - a)) :
    (∑ v : TwoFiberVertex Z m a b,
      (twoFiberGraph D).weight (Sum.inl i) v * f v) =
      ((a : ℝ) * (a + 1 : ℕ) /
          ((m - a : ℕ) * (m - a - 1 : ℕ))) *
          sumExcept i (fun j ↦ f (Sum.inl j)) +
        ((a : ℝ) * b / ((m - a : ℕ) * (m - b : ℕ))) *
          ∑ j : Fin (m - b), f (Sum.inr (Sum.inl j)) +
        ∑ z : Z,
          ((a : ℝ) * D.omega z / ((m - a : ℕ) * m)) *
            ∑ j : Fin m, f (Sum.inr (Sum.inr (z, j))) := by
  classical
  simp only [twoFiberGraph, Fintype.sum_sum_type, twoFiberEdgeWeight]
  simp [Finset.sum_ite, Finset.filter_ne, sumExcept, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  ring

private theorem weightedSum_right (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) (i : Fin (m - b)) :
    (∑ v : TwoFiberVertex Z m a b,
      (twoFiberGraph D).weight (Sum.inr (Sum.inl i)) v * f v) =
      ((a : ℝ) * b / ((m - a : ℕ) * (m - b : ℕ))) *
          ∑ j : Fin (m - a), f (Sum.inl j) +
        ((b : ℝ) * (b + 1 : ℕ) /
          ((m - b : ℕ) * (m - b - 1 : ℕ))) *
          sumExcept i (fun j ↦ f (Sum.inr (Sum.inl j))) +
        ∑ z : Z,
          ((b : ℝ) * D.omega z / ((m - b : ℕ) * m)) *
            ∑ j : Fin m, f (Sum.inr (Sum.inr (z, j))) := by
  classical
  simp only [twoFiberGraph, Fintype.sum_sum_type, twoFiberEdgeWeight]
  simp [Finset.sum_ite, Finset.filter_ne, sumExcept, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  ring

private theorem weightedSum_third (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) (z : Z) (i : Fin m) :
    (∑ v : TwoFiberVertex Z m a b,
      (twoFiberGraph D).weight (Sum.inr (Sum.inr (z, i))) v * f v) =
      ((a : ℝ) * D.omega z / ((m - a : ℕ) * m)) *
          ∑ j : Fin (m - a), f (Sum.inl j) +
        ((b : ℝ) * D.omega z / ((m - b : ℕ) * m)) *
          ∑ j : Fin (m - b), f (Sum.inr (Sum.inl j)) +
        (D.omega z / ((m : ℝ) * (m - 1 : ℕ))) *
          sumExcept i (fun j ↦ f (Sum.inr (Sum.inr (z, j)))) := by
  classical
  simp only [twoFiberGraph, Fintype.sum_sum_type, twoFiberEdgeWeight]
  simp only [Fintype.sum_prod_type]
  simp_rw [ite_mul, zero_mul]
  rw [Fintype.sum_eq_single z]
  · simp only [true_and]
    simp [Finset.sum_ite, Finset.filter_ne, sumExcept]
    simp_rw [← Finset.mul_sum]
    ring
  · intro w hwz
    have hzw : z ≠ w := Ne.symm hwz
    simp [hzw]

/-- The block formula is exactly the random-walk operator of the symmetric
conditioned graph. -/
theorem twoFiberGraph_walk_eq_operator (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    (twoFiberGraph D).walk f = twoFiberOperator D f := by
  classical
  have hmPos : 0 < m := by
    have hmOne := D.one_lt_m
    omega
  have hmaPos : 0 < m - a := Nat.sub_pos_of_lt D.a_lt_m
  have hmbPos : 0 < m - b := Nat.sub_pos_of_lt D.b_lt_m
  have hmaOnePos : 0 < m - a - 1 := Nat.sub_pos_of_lt D.one_lt_m_sub_a
  have hmbOnePos : 0 < m - b - 1 := Nat.sub_pos_of_lt D.one_lt_m_sub_b
  have hmOnePos : 0 < m - 1 := Nat.sub_pos_of_lt D.one_lt_m
  have hdPos : 0 < d := D.d_pos
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hmPos.ne'
  have hma0 : ((m - a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmaPos.ne'
  have hmb0 : ((m - b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmbPos.ne'
  have hmaOne0 : ((m - a - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hmaOnePos.ne'
  have hmbOne0 : ((m - b - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hmbOnePos.ne'
  have hmOne0 : ((m - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmOnePos.ne'
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hdPos.ne'
  have hdAdd0 : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast D.ha.ne'
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast D.hb.ne'
  funext u
  rcases u with i | u
  · rw [WeightedGraph.walk, weightedSum_left, twoFiberGraph_degree_left]
    simp only [twoFiberOperator, rightAverage, thirdAverage, thirdFiberAverage]
    have hthird :
        (∑ z : Z, ((a : ℝ) * D.omega z / ((m - a : ℕ) * m)) *
            ∑ j : Fin m, f (Sum.inr (Sum.inr (z, j)))) =
          ((a : ℝ) / (m - a : ℕ)) *
            ∑ z : Z, D.omega z *
              ((∑ j : Fin m, f (Sum.inr (Sum.inr (z, j)))) / m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _hz
      field_simp
    rw [hthird]
    field_simp
  · rcases u with i | ⟨z, i⟩
    · rw [WeightedGraph.walk, weightedSum_right, twoFiberGraph_degree_right]
      simp only [twoFiberOperator, leftAverage, thirdAverage, thirdFiberAverage]
      have hthird :
          (∑ z : Z, ((b : ℝ) * D.omega z / ((m - b : ℕ) * m)) *
              ∑ j : Fin m, f (Sum.inr (Sum.inr (z, j)))) =
            ((b : ℝ) / (m - b : ℕ)) *
              ∑ z : Z, D.omega z *
                ((∑ j : Fin m, f (Sum.inr (Sum.inr (z, j)))) / m) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _hz
        field_simp
      rw [hthird]
      field_simp
    · rw [WeightedGraph.walk, weightedSum_third, twoFiberGraph_degree_third]
      simp only [twoFiberOperator, leftAverage, rightAverage]
      have homega0 : D.omega z ≠ 0 := (D.omega_pos z).ne'
      field_simp

/-! ## The invariant summands -/

theorem sumExcept_eq_total_sub {n : ℕ} (i : Fin n) (f : Fin n → ℝ) :
    sumExcept i f = (∑ j : Fin n, f j) - f i := by
  classical
  rw [sumExcept, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  ring

theorem sumExcept_eq_neg {n : ℕ} (i : Fin n) (f : Fin n → ℝ)
    (hsum : ∑ j : Fin n, f j = 0) :
    sumExcept i f = -f i := by
  rw [sumExcept_eq_total_sub, hsum]
  ring

theorem sumExcept_const {n : ℕ} (i : Fin n) (c : ℝ) :
    sumExcept i (fun _ ↦ c) = (n - 1 : ℕ) * c := by
  classical
  simp [sumExcept, Finset.card_erase_of_mem]

@[simp] theorem sumExcept_zero {n : ℕ} (i : Fin n) :
    sumExcept i (fun _ ↦ (0 : ℝ)) = 0 := by
  simp [sumExcept]

/-- Functions constant on each of the three aggregate blocks. -/
def quotientFunction (L R T : ℝ) : TwoFiberVertex Z m a b → ℝ
  | Sum.inl _ => L
  | Sum.inr (Sum.inl _) => R
  | Sum.inr (Sum.inr _) => T

/-- Zero-sum functions supported on the first occupied fiber. -/
def leftMode (phi : Fin (m - a) → ℝ) : TwoFiberVertex Z m a b → ℝ
  | Sum.inl i => phi i
  | Sum.inr _ => 0

/-- Zero-sum functions supported on the second occupied fiber. -/
def rightMode (phi : Fin (m - b) → ℝ) : TwoFiberVertex Z m a b → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl i) => phi i
  | Sum.inr (Sum.inr _) => 0

/-- Simultaneous zero-sum variation inside every possible third fiber. -/
def thirdWithinMode (phi : Z → Fin m → ℝ) :
    TwoFiberVertex Z m a b → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (z, i)) => phi z i

/-- Variation between possible third fibers, constant on each label fiber. -/
def thirdPetalMode (c : Z → ℝ) : TwoFiberVertex Z m a b → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (z, _)) => c z

theorem leftAverage_quotientFunction (D : TwoFiberData Z d m a b)
    (L R T : ℝ) :
    leftAverage (m := m) (a := a) (b := b)
      (quotientFunction (Z := Z) (m := m) (a := a) (b := b) L R T) = L := by
  have hpos : 0 < m - a := Nat.sub_pos_of_lt D.a_lt_m
  simp [leftAverage, quotientFunction]
  field_simp

theorem rightAverage_quotientFunction (D : TwoFiberData Z d m a b)
    (L R T : ℝ) :
    rightAverage (m := m) (a := a) (b := b)
      (quotientFunction (Z := Z) (m := m) (a := a) (b := b) L R T) = R := by
  have hpos : 0 < m - b := Nat.sub_pos_of_lt D.b_lt_m
  simp [rightAverage, quotientFunction]
  field_simp

theorem thirdFiberAverage_quotientFunction (D : TwoFiberData Z d m a b)
    (L R T : ℝ) (z : Z) :
    thirdFiberAverage (m := m) (a := a) (b := b)
      (quotientFunction (Z := Z) (m := m) (a := a) (b := b) L R T) z = T := by
  have hpos : 0 < m := by
    have hmOne := D.one_lt_m
    omega
  simp [thirdFiberAverage, quotientFunction]
  field_simp

theorem thirdAverage_quotientFunction (D : TwoFiberData Z d m a b)
    (L R T : ℝ) :
    thirdAverage D
      (quotientFunction (Z := Z) (m := m) (a := a) (b := b) L R T) = T := by
  simp_rw [thirdAverage, thirdFiberAverage_quotientFunction D]
  rw [← Finset.sum_mul, D.omega_sum, one_mul]

/-- The exact `3 × 3` quotient matrix displayed in the paper. -/
theorem twoFiberOperator_quotientFunction (D : TwoFiberData Z d m a b)
    (L R T : ℝ) :
    twoFiberOperator D
      (quotientFunction (Z := Z) (m := m) (a := a) (b := b) L R T) =
      quotientFunction (Z := Z) (m := m) (a := a) (b := b)
        (((a + 1 : ℕ) / (d + 1 : ℕ)) * L +
          ((b : ℝ) / (d + 1 : ℕ)) * R +
          (1 / (d + 1 : ℕ)) * T)
        (((a : ℝ) / (d + 1 : ℕ)) * L +
          ((b + 1 : ℕ) / (d + 1 : ℕ)) * R +
          (1 / (d + 1 : ℕ)) * T)
        (((a : ℝ) / d) * L + ((b : ℝ) / d) * R + (1 / (d : ℝ)) * T) := by
  funext u
  rcases u with i | u
  · simp only [twoFiberOperator, quotientFunction]
    rw [rightAverage_quotientFunction D,
      thirdAverage_quotientFunction D, sumExcept_const]
    have hpos : 0 < m - a - 1 := Nat.sub_pos_of_lt D.one_lt_m_sub_a
    have h0 : ((m - a - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp
  · rcases u with i | ⟨z, i⟩
    · simp only [twoFiberOperator, quotientFunction]
      rw [leftAverage_quotientFunction D, thirdAverage_quotientFunction D,
        sumExcept_const]
      have hpos : 0 < m - b - 1 := Nat.sub_pos_of_lt D.one_lt_m_sub_b
      have h0 : ((m - b - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
      field_simp
    · simp only [twoFiberOperator, quotientFunction]
      rw [leftAverage_quotientFunction D, rightAverage_quotientFunction D,
        sumExcept_const]
      have hpos : 0 < m - 1 := Nat.sub_pos_of_lt D.one_lt_m
      have h0 : ((m - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
      field_simp

/-- The stationary quotient vector. -/
theorem quotient_stationary (D : TwoFiberData Z d m a b) :
    twoFiberOperator D
      (quotientFunction (Z := Z) (m := m) (a := a) (b := b) 1 1 1) =
      quotientFunction (Z := Z) (m := m) (a := a) (b := b) 1 1 1 := by
  rw [twoFiberOperator_quotientFunction]
  have hdOne : 1 ≤ d := by
    have hd := D.hd
    omega
  have hab : (a : ℝ) + b = (d : ℝ) - 1 := by
    have h := congrArg (fun n : ℕ ↦ (n : ℝ)) D.occupancy_sum
    simpa only [Nat.cast_add, Nat.cast_sub hdOne, Nat.cast_one] using h
  funext u
  rcases u with i | u
  · simp [quotientFunction]
    field_simp
    nlinarith
  · rcases u with i | ⟨z, i⟩ <;> simp [quotientFunction]
    · field_simp
      nlinarith
    · field_simp
      nlinarith

/-- First nonstationary quotient mode, with eigenvalue `1/(d+1)`. -/
theorem quotient_difference_eigenmode (D : TwoFiberData Z d m a b) :
    twoFiberOperator D
      (quotientFunction (Z := Z) (m := m) (a := a) (b := b) b (-(a : ℝ)) 0) =
      fun v ↦ (1 / (d + 1 : ℕ)) *
        quotientFunction (Z := Z) (m := m) (a := a) (b := b)
          b (-(a : ℝ)) 0 v := by
  rw [twoFiberOperator_quotientFunction]
  funext u
  rcases u with i | u
  · simp [quotientFunction]
    ring
  · rcases u with i | ⟨z, i⟩ <;> simp [quotientFunction] <;> ring

/-- Second nonstationary quotient mode, with eigenvalue `1/(d(d+1))`. -/
theorem quotient_radial_eigenmode (D : TwoFiberData Z d m a b) :
    let q := quotientFunction (Z := Z) (m := m) (a := a) (b := b)
      d d (-((d : ℝ) ^ 2 - 1))
    twoFiberOperator D q = fun v ↦ (1 / ((d : ℝ) * (d + 1 : ℕ))) * q v := by
  dsimp only
  rw [twoFiberOperator_quotientFunction]
  have hdOne : 1 ≤ d := by
    have hd := D.hd
    omega
  have hab : (a : ℝ) + b = (d : ℝ) - 1 := by
    have h := congrArg (fun n : ℕ ↦ (n : ℝ)) D.occupancy_sum
    simpa only [Nat.cast_add, Nat.cast_sub hdOne, Nat.cast_one] using h
  funext u
  rcases u with i | u
  · simp [quotientFunction]
    field_simp
    nlinarith
  · rcases u with i | ⟨z, i⟩ <;> simp [quotientFunction]
    · field_simp
      nlinarith
    · have hd0 : (d : ℝ) ≠ 0 := by positivity
      rw [div_mul_cancel₀ _ hd0, div_mul_cancel₀ _ hd0]
      have hab' : (a : ℝ) + b = d - 1 := hab
      rw [show (a : ℝ) + b = d - 1 from hab']
      field_simp
      ring

/-- Zero-sum variation in the first occupied fiber has the first eigenvalue
in (5.3). -/
theorem leftMode_eigenmode (D : TwoFiberData Z d m a b)
    (phi : Fin (m - a) → ℝ) (hsum : ∑ i, phi i = 0) :
    twoFiberOperator D (leftMode (Z := Z) (b := b) phi) =
      fun v ↦
        (-(a + 1 : ℕ) /
          ((d + 1 : ℕ) * (m - a - 1 : ℕ))) *
          leftMode (Z := Z) (b := b) phi v := by
  funext u
  rcases u with i | u
  · simp only [twoFiberOperator, leftMode]
    rw [sumExcept_eq_neg _ _ hsum]
    simp [rightAverage, thirdAverage, thirdFiberAverage, leftMode]
    ring
  · rcases u with i | ⟨z, i⟩
    · simp [twoFiberOperator, leftMode, leftAverage, hsum,
        thirdAverage, thirdFiberAverage]
    · simp [twoFiberOperator, leftMode, leftAverage, hsum, rightAverage]

/-- Zero-sum variation in the second occupied fiber has the second
eigenvalue in (5.3). -/
theorem rightMode_eigenmode (D : TwoFiberData Z d m a b)
    (phi : Fin (m - b) → ℝ) (hsum : ∑ i, phi i = 0) :
    twoFiberOperator D (rightMode (Z := Z) (a := a) phi) =
      fun v ↦
        (-(b + 1 : ℕ) /
          ((d + 1 : ℕ) * (m - b - 1 : ℕ))) *
          rightMode (Z := Z) (a := a) phi v := by
  funext u
  rcases u with i | u
  · simp [twoFiberOperator, rightMode, rightAverage, hsum,
      thirdAverage, thirdFiberAverage]
  · rcases u with i | ⟨z, i⟩
    · simp only [twoFiberOperator, rightMode]
      rw [sumExcept_eq_neg _ _ hsum]
      simp [leftAverage, thirdAverage, thirdFiberAverage, rightMode]
      ring
    · simp [twoFiberOperator, rightMode, leftAverage, rightAverage, hsum]

/-- Zero-sum variation inside each possible third fiber has the third
eigenvalue in (5.3). -/
theorem thirdWithinMode_eigenmode (D : TwoFiberData Z d m a b)
    (phi : Z → Fin m → ℝ) (hsum : ∀ z, ∑ i, phi z i = 0) :
    twoFiberOperator D (thirdWithinMode (a := a) (b := b) phi) =
      fun v ↦
        (-1 / ((d : ℝ) * (m - 1 : ℕ))) *
          thirdWithinMode (a := a) (b := b) phi v := by
  funext u
  rcases u with i | u
  · simp only [twoFiberOperator, thirdWithinMode]
    simp [rightAverage, thirdAverage, thirdFiberAverage,
      thirdWithinMode, hsum]
  · rcases u with i | ⟨z, i⟩
    · simp only [twoFiberOperator, thirdWithinMode]
      simp [leftAverage, thirdAverage, thirdFiberAverage,
        thirdWithinMode, hsum]
    · simp only [twoFiberOperator, thirdWithinMode]
      rw [sumExcept_eq_neg _ _ (hsum z)]
      simp [leftAverage, rightAverage, thirdWithinMode]
      ring

theorem thirdFiberAverage_thirdPetalMode (D : TwoFiberData Z d m a b)
    (c : Z → ℝ) (z : Z) :
    thirdFiberAverage (m := m) (a := a) (b := b)
      (thirdPetalMode (m := m) (a := a) (b := b) c) z = c z := by
  have hmPos : 0 < m := by
    have hmOne := D.one_lt_m
    omega
  simp [thirdFiberAverage, thirdPetalMode]
  field_simp

theorem thirdAverage_thirdPetalMode (D : TwoFiberData Z d m a b)
    (c : Z → ℝ) :
    thirdAverage D (thirdPetalMode (m := m) (a := a) (b := b) c) =
      ∑ z : Z, D.omega z * c z := by
  simp_rw [thirdAverage, thirdFiberAverage_thirdPetalMode D]

/-- Weighted zero-mean variation among possible third fibers is the
`1/d` petal eigenspace (when that space is nonzero). -/
theorem thirdPetalMode_eigenmode (D : TwoFiberData Z d m a b)
    (c : Z → ℝ) (hweighted : ∑ z : Z, D.omega z * c z = 0) :
    twoFiberOperator D (thirdPetalMode (m := m) (a := a) (b := b) c) =
      fun v ↦ (1 / (d : ℝ)) *
        thirdPetalMode (m := m) (a := a) (b := b) c v := by
  funext u
  rcases u with i | u
  · simp only [twoFiberOperator, thirdPetalMode]
    rw [thirdAverage_thirdPetalMode D, hweighted]
    simp [rightAverage, thirdPetalMode]
  · rcases u with i | ⟨z, i⟩
    · simp only [twoFiberOperator, thirdPetalMode]
      rw [thirdAverage_thirdPetalMode D, hweighted]
      simp [leftAverage, thirdPetalMode]
    · simp only [twoFiberOperator, thirdPetalMode]
      rw [sumExcept_const]
      simp [leftAverage, rightAverage, thirdPetalMode]
      have hmOnePos : 0 < m - 1 := Nat.sub_pos_of_lt D.one_lt_m
      have hmOne0 : ((m - 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast hmOnePos.ne'
      field_simp

/-! ## Completeness of the block decomposition -/

noncomputable def quotientPart (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) : TwoFiberVertex Z m a b → ℝ :=
  quotientFunction (Z := Z) (m := m) (a := a) (b := b)
    (leftAverage f) (rightAverage f) (thirdAverage D f)

noncomputable def leftResidual (f : TwoFiberVertex Z m a b → ℝ) :
    TwoFiberVertex Z m a b → ℝ :=
  leftMode (Z := Z) (b := b) (fun i ↦ f (Sum.inl i) - leftAverage f)

noncomputable def rightResidual (f : TwoFiberVertex Z m a b → ℝ) :
    TwoFiberVertex Z m a b → ℝ :=
  rightMode (Z := Z) (a := a)
    (fun i ↦ f (Sum.inr (Sum.inl i)) - rightAverage f)

noncomputable def thirdWithinResidual
    (f : TwoFiberVertex Z m a b → ℝ) : TwoFiberVertex Z m a b → ℝ :=
  thirdWithinMode (a := a) (b := b)
    (fun z i ↦ f (Sum.inr (Sum.inr (z, i))) - thirdFiberAverage f z)

noncomputable def thirdPetalResidual (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) : TwoFiberVertex Z m a b → ℝ :=
  thirdPetalMode (m := m) (a := a) (b := b)
    (fun z ↦ thirdFiberAverage f z - thirdAverage D f)

theorem leftResidual_sum_zero (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    ∑ i : Fin (m - a),
      (f (Sum.inl i) - leftAverage f) = 0 := by
  have hpos : 0 < m - a := Nat.sub_pos_of_lt D.a_lt_m
  unfold leftAverage
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  field_simp
  ring

theorem rightResidual_sum_zero (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    ∑ i : Fin (m - b),
      (f (Sum.inr (Sum.inl i)) - rightAverage f) = 0 := by
  have hpos : 0 < m - b := Nat.sub_pos_of_lt D.b_lt_m
  unfold rightAverage
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  field_simp
  ring

theorem thirdWithinResidual_sum_zero (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) (z : Z) :
    ∑ i : Fin m,
      (f (Sum.inr (Sum.inr (z, i))) - thirdFiberAverage f z) = 0 := by
  have hmPos : 0 < m := by
    have hmOne := D.one_lt_m
    omega
  unfold thirdFiberAverage
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  field_simp
  ring

theorem thirdPetalResidual_weighted_zero (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    ∑ z : Z, D.omega z *
      (thirdFiberAverage f z - thirdAverage D f) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  unfold thirdAverage
  rw [D.omega_sum, one_mul]
  ring

/-- Every function is the sum of its quotient, two occupied-fiber residuals,
third-fiber internal residual, and third-fiber petal residual.  This proves
that the invariant spaces used in the spectral calculation span the whole
conditioned link. -/
theorem twoFiber_complete_decomposition (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    f = fun v ↦
      quotientPart D f v + leftResidual f v + rightResidual f v +
        thirdWithinResidual f v + thirdPetalResidual D f v := by
  funext u
  rcases u with i | u
  · simp [quotientPart, leftResidual, rightResidual,
      thirdWithinResidual, thirdPetalResidual, quotientFunction, leftMode,
      rightMode, thirdWithinMode, thirdPetalMode]
  · rcases u with i | ⟨z, i⟩
    · simp [quotientPart, leftResidual, rightResidual,
        thirdWithinResidual, thirdPetalResidual, quotientFunction, leftMode,
        rightMode, thirdWithinMode, thirdPetalMode]
    · simp [quotientPart, leftResidual, rightResidual,
        thirdWithinResidual, thirdPetalResidual, quotientFunction, leftMode,
        rightMode, thirdWithinMode, thirdPetalMode]
      ring

theorem operator_leftResidual (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    twoFiberOperator D (leftResidual f) =
      fun v ↦ (-(a + 1 : ℕ) /
        ((d + 1 : ℕ) * (m - a - 1 : ℕ))) * leftResidual f v := by
  unfold leftResidual
  exact leftMode_eigenmode D _ (leftResidual_sum_zero D f)

theorem operator_rightResidual (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    twoFiberOperator D (rightResidual f) =
      fun v ↦ (-(b + 1 : ℕ) /
        ((d + 1 : ℕ) * (m - b - 1 : ℕ))) * rightResidual f v := by
  unfold rightResidual
  exact rightMode_eigenmode D _ (rightResidual_sum_zero D f)

theorem operator_thirdWithinResidual (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    twoFiberOperator D (thirdWithinResidual f) =
      fun v ↦ (-1 / ((d : ℝ) * (m - 1 : ℕ))) *
        thirdWithinResidual f v := by
  unfold thirdWithinResidual
  exact thirdWithinMode_eigenmode D _ (thirdWithinResidual_sum_zero D f)

theorem operator_thirdPetalResidual (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    twoFiberOperator D (thirdPetalResidual D f) =
      fun v ↦ (1 / (d : ℝ)) * thirdPetalResidual D f v := by
  unfold thirdPetalResidual
  exact thirdPetalMode_eigenmode D _ (thirdPetalResidual_weighted_zero D f)

/-- Exactly the six nonstationary eigenvalue types in the `r(F)=2` row of
the table on page 15. -/
inductive TwoFiberListedEigenvalue (d m a b : ℕ) : ℝ → Prop
  | quotientOne : TwoFiberListedEigenvalue d m a b (1 / ((d : ℝ) + 1))
  | quotientTwo :
      TwoFiberListedEigenvalue d m a b (1 / ((d : ℝ) * ((d : ℝ) + 1)))
  | petal : TwoFiberListedEigenvalue d m a b (1 / (d : ℝ))
  | leftWithin : TwoFiberListedEigenvalue d m a b
      (-((a : ℝ) + 1) / (((d : ℝ) + 1) * ((m : ℝ) - a - 1)))
  | rightWithin : TwoFiberListedEigenvalue d m a b
      (-((b : ℝ) + 1) / (((d : ℝ) + 1) * ((m : ℝ) - b - 1)))
  | thirdWithin : TwoFiberListedEigenvalue d m a b
      (-1 / ((d : ℝ) * ((m : ℝ) - 1)))

theorem twoFiberListedEigenvalue_isTable (D : TwoFiberData Z d m a b)
    {mu : ℝ} (hmu : TwoFiberListedEigenvalue d m a b mu) :
    TableEigenvalue d m mu := by
  have hdReal : (3 : ℝ) ≤ d := by exact_mod_cast D.hd
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have haBound : (a : ℝ) ≤ (d : ℝ) - 2 := by
    have h := D.a_le_d_sub_two
    have hdTwo : 2 ≤ d := D.hd.trans' (by omega)
    exact_mod_cast h
  have hbBound : (b : ℝ) ≤ (d : ℝ) - 2 := by
    have h := D.b_le_d_sub_two
    have hdTwo : 2 ≤ d := D.hd.trans' (by omega)
    exact_mod_cast h
  cases hmu with
  | quotientOne => exact TableEigenvalue.twoFiberQuotientOne
  | quotientTwo => exact TableEigenvalue.twoFiberQuotientTwo
  | petal => exact TableEigenvalue.twoFiberAcrossThird
  | leftWithin =>
      exact TableEigenvalue.twoFiberOccupiedWithin (d := d) (m := m)
        (a : ℝ) ha0 haBound
  | rightWithin =>
      exact TableEigenvalue.twoFiberOccupiedWithin (d := d) (m := m)
        (b : ℝ) hb0 hbBound
  | thirdWithin => exact TableEigenvalue.twoFiberThirdWithin

/-- Every nonstationary value supplied by the complete two-fiber block
decomposition has absolute value at most `1/d`. -/
theorem twoFiberListedEigenvalue_bound (D : TwoFiberData Z d m a b)
    {mu : ℝ} (hmu : TwoFiberListedEigenvalue d m a b mu) :
    |mu| ≤ 1 / (d : ℝ) :=
  tableEigenvalue_bound D.hd D.hm (twoFiberListedEigenvalue_isTable D hmu)

/-! ## Transport from a concrete conditioned link -/

/-- A concrete codimension-two link with two occupied fibers is identified
with the canonical model by this data.  The actual edge weights may have a
common positive normalization factor; the certificate records it explicitly
so that `WeightedGraph.walk` and the spectral estimate transport without any
ad-hoc relabeling definitions. -/
structure TwoFiberLinkCertificate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (Z : Type u) [Fintype Z] [DecidableEq Z]
    (d m a b : ℕ) where
  data : TwoFiberData Z d m a b
  enumerate : V ≃ TwoFiberVertex Z m a b
  commonScale : ℝ
  commonScale_pos : 0 < commonScale
  relabel_eq :
    G = ((twoFiberGraph data).scale commonScale commonScale_pos.le).relabel
      enumerate.symm

/-- Positive global normalization and enumeration of the vertices do not
affect a two-sided bound.  Thus an actual weighted-lift link is reduced to
the canonical two-fiber calculation by a `TwoFiberLinkCertificate`. -/
theorem TwoFiberLinkCertificate.twoSidedSpectralBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {Z : Type u} [Fintype Z] [DecidableEq Z]
    {d m a b : ℕ}
    (certificate : TwoFiberLinkCertificate G Z d m a b)
    {lambda : ℝ}
    (hmodel : (twoFiberGraph certificate.data).TwoSidedSpectralBound lambda) :
    G.TwoSidedSpectralBound lambda := by
  have hscaled := WeightedGraph.twoSidedSpectralBound_scale
    (twoFiberGraph certificate.data) certificate.commonScale
    certificate.commonScale_pos hmodel
  rw [certificate.relabel_eq]
  exact WeightedGraph.twoSidedSpectralBound_relabel _
    certificate.enumerate.symm hscaled

/-! ## Exhaustion of the mean-zero spectrum -/

theorem sum_sumExcept {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    (∑ i : Fin n, sumExcept i f) = (n - 1 : ℕ) * ∑ j : Fin n, f j := by
  simp_rw [sumExcept_eq_total_sub]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hone : 1 ≤ n := hn
  rw [Nat.cast_sub hone, Nat.cast_one]
  ring

theorem leftAverage_operator (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    leftAverage (twoFiberOperator D f) =
      ((a + 1 : ℕ) / (d + 1 : ℕ)) * leftAverage f +
        ((b : ℝ) / (d + 1 : ℕ)) * rightAverage f +
        (1 / (d + 1 : ℕ)) * thirdAverage D f := by
  have hnPos : 0 < m - a := Nat.sub_pos_of_lt D.a_lt_m
  have hnOnePos : 0 < m - a - 1 := Nat.sub_pos_of_lt D.one_lt_m_sub_a
  have hn0 : ((m - a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hnPos.ne'
  have hnOne0 : ((m - a - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hnOnePos.ne'
  unfold leftAverage
  simp only [twoFiberOperator]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  rw [sum_sumExcept hnPos]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  field_simp

theorem rightAverage_operator (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    rightAverage (twoFiberOperator D f) =
      ((a : ℝ) / (d + 1 : ℕ)) * leftAverage f +
        ((b + 1 : ℕ) / (d + 1 : ℕ)) * rightAverage f +
        (1 / (d + 1 : ℕ)) * thirdAverage D f := by
  have hnPos : 0 < m - b := Nat.sub_pos_of_lt D.b_lt_m
  have hnOnePos : 0 < m - b - 1 := Nat.sub_pos_of_lt D.one_lt_m_sub_b
  have hn0 : ((m - b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hnPos.ne'
  have hnOne0 : ((m - b - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hnOnePos.ne'
  unfold rightAverage
  simp only [twoFiberOperator]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  rw [sum_sumExcept hnPos]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  field_simp

theorem thirdFiberAverage_operator (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) (z : Z) :
    thirdFiberAverage (twoFiberOperator D f) z =
      ((a : ℝ) / d) * leftAverage f + ((b : ℝ) / d) * rightAverage f +
        (1 / (d : ℝ)) * thirdFiberAverage f z := by
  have hmPos : 0 < m := by
    have hmOne := D.one_lt_m
    omega
  have hmOnePos : 0 < m - 1 := Nat.sub_pos_of_lt D.one_lt_m
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hmPos.ne'
  have hmOne0 : ((m - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmOnePos.ne'
  unfold thirdFiberAverage
  simp only [twoFiberOperator]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  rw [sum_sumExcept hmPos]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  field_simp

theorem thirdAverage_operator (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    thirdAverage D (twoFiberOperator D f) =
      ((a : ℝ) / d) * leftAverage f + ((b : ℝ) / d) * rightAverage f +
        (1 / (d : ℝ)) * thirdAverage D f := by
  unfold thirdAverage
  simp_rw [thirdFiberAverage_operator D]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.sum_mul]
  rw [D.omega_sum]
  have hthird :
      (∑ x : Z, D.omega x * ((1 / (d : ℝ)) * thirdFiberAverage f x)) =
        (1 / (d : ℝ)) * ∑ x : Z, D.omega x * thirdFiberAverage f x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  rw [hthird]
  ring

/-! ## Stationary energy identities -/

/-- The stationary mean depends only on the three block averages.  The
normalization is particularly simple: the left, right, and third blocks have
total stationary masses `a(d+1)`, `b(d+1)`, and `d`, respectively. -/
theorem twoFiberGraph_weightedMean (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    (twoFiberGraph D).weightedMean f =
      (a : ℝ) * (d + 1 : ℕ) * leftAverage f +
        (b : ℝ) * (d + 1 : ℕ) * rightAverage f +
          (d : ℝ) * thirdAverage D f := by
  classical
  unfold WeightedGraph.weightedMean
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp_rw [twoFiberGraph_degree_left D, twoFiberGraph_degree_right D,
    twoFiberGraph_degree_third D]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hleft :
      (∑ i : Fin (m - a), f (Sum.inl i)) =
        (m - a : ℕ) * leftAverage f := by
    unfold leftAverage
    have hpos : 0 < m - a := Nat.sub_pos_of_lt D.a_lt_m
    field_simp
  have hright :
      (∑ i : Fin (m - b), f (Sum.inr (Sum.inl i))) =
        (m - b : ℕ) * rightAverage f := by
    unfold rightAverage
    have hpos : 0 < m - b := Nat.sub_pos_of_lt D.b_lt_m
    field_simp
  rw [hleft, hright]
  have hthird (z : Z) :
      (∑ i : Fin m, f (Sum.inr (Sum.inr (z, i)))) =
        (m : ℝ) * thirdFiberAverage f z := by
    unfold thirdFiberAverage
    have hpos : 0 < m := by
      have hm := D.one_lt_m
      omega
    field_simp
  simp_rw [← Finset.mul_sum, hthird]
  unfold thirdAverage
  have hma0 : ((m - a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt D.a_lt_m).ne'
  have hmb0 : ((m - b : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt D.b_lt_m).ne'
  have hm0 : (m : ℝ) ≠ 0 := by
    have hm := D.one_lt_m
    exact_mod_cast (by omega : 0 < m).ne'
  field_simp
  rw [Finset.mul_sum]
  ring

/-- The stationary squared norm is the sum of the three fiber energies. -/
theorem twoFiberGraph_sqNorm (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    (twoFiberGraph D).sqNorm f =
      ((a : ℝ) * (d + 1 : ℕ) / (m - a : ℕ)) *
        ∑ i : Fin (m - a), (f (Sum.inl i)) ^ 2 +
      ((b : ℝ) * (d + 1 : ℕ) / (m - b : ℕ)) *
        ∑ i : Fin (m - b), (f (Sum.inr (Sum.inl i))) ^ 2 +
      ∑ z : Z, ((d : ℝ) * D.omega z / m) *
        ∑ i : Fin m, (f (Sum.inr (Sum.inr (z, i)))) ^ 2 := by
  classical
  unfold WeightedGraph.sqNorm
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp_rw [twoFiberGraph_degree_left D, twoFiberGraph_degree_right D,
    twoFiberGraph_degree_third D]
  simp_rw [← Finset.mul_sum]
  ring

/-- On the stationary-mean-zero subspace the three block averages satisfy
the single weighted relation used by the quotient calculation. -/
theorem twoFiber_average_relation (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ)
    (hmean : (twoFiberGraph D).weightedMean f = 0) :
    (a : ℝ) * (d + 1 : ℕ) * leftAverage f +
      (b : ℝ) * (d + 1 : ℕ) * rightAverage f +
        (d : ℝ) * thirdAverage D f = 0 := by
  rw [twoFiberGraph_weightedMean D f] at hmean
  exact hmean

/-- The difference coordinate in the stationary-mean-zero quotient block. -/
noncomputable def twoFiberQuotientU (L R : ℝ) : ℝ :=
  (L - R) / ((d : ℝ) - 1)

/-- The radial coordinate in the stationary-mean-zero quotient block. -/
noncomputable def twoFiberQuotientV (T : ℝ) : ℝ :=
  -T / ((d : ℝ) ^ 2 - 1)

private theorem twoFiber_quotient_cast_sum (D : TwoFiberData Z d m a b) :
    (a : ℝ) + b = (d : ℝ) - 1 := by
  have hd1 : 1 ≤ d := D.hd.trans' (by omega)
  have h := congrArg (fun n : ℕ ↦ (n : ℝ)) D.occupancy_sum
  simpa only [Nat.cast_add, Nat.cast_sub hd1, Nat.cast_one] using h

/-- Reconstruction of the left quotient value from its two nonstationary
coordinates. -/
theorem twoFiber_quotient_reconstruct_left (D : TwoFiberData Z d m a b)
    (L R T : ℝ)
    (hmean : (a : ℝ) * (d + 1 : ℕ) * L +
      (b : ℝ) * (d + 1 : ℕ) * R + (d : ℝ) * T = 0) :
    L = (b : ℝ) * twoFiberQuotientU (d := d) L R +
      (d : ℝ) * twoFiberQuotientV (d := d) T := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast D.hd
  have hdm1 : (d : ℝ) - 1 ≠ 0 := by nlinarith
  have hdsq1 : (d : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hab := twoFiber_quotient_cast_sum D
  norm_num only [Nat.cast_add, Nat.cast_one] at hmean ⊢
  unfold twoFiberQuotientU twoFiberQuotientV
  field_simp
  rw [show (d : ℝ) ^ 2 - 1 = ((d : ℝ) - 1) * ((d : ℝ) + 1) by ring]
  linear_combination ((d : ℝ) - 1) * hmean -
    (((d : ℝ) ^ 2 - 1) * L) * hab

/-- Reconstruction of the right quotient value from its two nonstationary
coordinates. -/
theorem twoFiber_quotient_reconstruct_right (D : TwoFiberData Z d m a b)
    (L R T : ℝ)
    (hmean : (a : ℝ) * (d + 1 : ℕ) * L +
      (b : ℝ) * (d + 1 : ℕ) * R + (d : ℝ) * T = 0) :
    R = -(a : ℝ) * twoFiberQuotientU (d := d) L R +
      (d : ℝ) * twoFiberQuotientV (d := d) T := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast D.hd
  have hdm1 : (d : ℝ) - 1 ≠ 0 := by nlinarith
  have hdsq1 : (d : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hab := twoFiber_quotient_cast_sum D
  norm_num only [Nat.cast_add, Nat.cast_one] at hmean ⊢
  unfold twoFiberQuotientU twoFiberQuotientV
  field_simp
  rw [show (d : ℝ) ^ 2 - 1 = ((d : ℝ) - 1) * ((d : ℝ) + 1) by ring]
  linear_combination ((d : ℝ) - 1) * hmean -
    (((d : ℝ) ^ 2 - 1) * R) * hab

/-- Reconstruction of the third quotient value from its radial coordinate. -/
theorem twoFiber_quotient_reconstruct_third (D : TwoFiberData Z d m a b)
    (T : ℝ) :
    T = -((d : ℝ) ^ 2 - 1) * twoFiberQuotientV (d := d) T := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast D.hd
  have hdsq1 : (d : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  unfold twoFiberQuotientV
  field_simp

/-! ## The full weighted-energy estimate -/

/-- Stationary energy of a function which is constant on each of the three
aggregate blocks. -/
noncomputable def twoFiberQuotientEnergy (L R T : ℝ) : ℝ :=
  (a : ℝ) * (d + 1 : ℕ) * L ^ 2 +
    (b : ℝ) * (d + 1 : ℕ) * R ^ 2 + (d : ℝ) * T ^ 2

/-- Weighted Pythagorean (sum-of-squares) identity for the mean-zero
quotient plane.  The two summands are the mutually orthogonal difference
and radial quotient modes. -/
theorem twoFiber_quotient_energy_sos (D : TwoFiberData Z d m a b)
    (L R T : ℝ)
    (hmean : (a : ℝ) * (d + 1 : ℕ) * L +
      (b : ℝ) * (d + 1 : ℕ) * R + (d : ℝ) * T = 0) :
    twoFiberQuotientEnergy (d := d) (a := a) (b := b) L R T =
      (a : ℝ) * b * ((d : ℝ) ^ 2 - 1) *
          (twoFiberQuotientU (d := d) L R) ^ 2 +
        (d : ℝ) * ((d : ℝ) ^ 2 - 1) *
          ((d : ℝ) ^ 2 + d - 1) *
          (twoFiberQuotientV (d := d) T) ^ 2 := by
  let U := twoFiberQuotientU (d := d) L R
  let V := twoFiberQuotientV (d := d) T
  have hL : L = (b : ℝ) * U + (d : ℝ) * V := by
    simpa only [U, V] using twoFiber_quotient_reconstruct_left D L R T hmean
  have hR : R = -(a : ℝ) * U + (d : ℝ) * V := by
    simpa only [U, V] using twoFiber_quotient_reconstruct_right D L R T hmean
  have hT : T = -((d : ℝ) ^ 2 - 1) * V := by
    simpa only [V] using twoFiber_quotient_reconstruct_third D T
  change twoFiberQuotientEnergy (d := d) (a := a) (b := b) L R T =
    (a : ℝ) * b * ((d : ℝ) ^ 2 - 1) * U ^ 2 +
      (d : ℝ) * ((d : ℝ) ^ 2 - 1) * ((d : ℝ) ^ 2 + d - 1) * V ^ 2
  rw [hL, hR, hT]
  unfold twoFiberQuotientEnergy
  have hab := twoFiber_quotient_cast_sum D
  have hb : (b : ℝ) = (d : ℝ) - 1 - a := by linarith
  norm_num only [Nat.cast_add, Nat.cast_one]
  rw [hb]
  ring

/-- The quotient matrix, written as its three output coordinates. -/
noncomputable def twoFiberQuotientLeftStep (L R T : ℝ) : ℝ :=
  ((a + 1 : ℕ) / (d + 1 : ℕ)) * L +
    ((b : ℝ) / (d + 1 : ℕ)) * R + (1 / (d + 1 : ℕ)) * T

noncomputable def twoFiberQuotientRightStep (L R T : ℝ) : ℝ :=
  ((a : ℝ) / (d + 1 : ℕ)) * L +
    ((b + 1 : ℕ) / (d + 1 : ℕ)) * R + (1 / (d + 1 : ℕ)) * T

noncomputable def twoFiberQuotientThirdStep (L R T : ℝ) : ℝ :=
  ((a : ℝ) / d) * L + ((b : ℝ) / d) * R + (1 / (d : ℝ)) * T

theorem twoFiber_quotient_step_mean_zero (D : TwoFiberData Z d m a b)
    (L R T : ℝ)
    (hmean : (a : ℝ) * (d + 1 : ℕ) * L +
      (b : ℝ) * (d + 1 : ℕ) * R + (d : ℝ) * T = 0) :
    (a : ℝ) * (d + 1 : ℕ) *
        twoFiberQuotientLeftStep (d := d) (a := a) (b := b) L R T +
      (b : ℝ) * (d + 1 : ℕ) *
        twoFiberQuotientRightStep (d := d) (a := a) (b := b) L R T +
      (d : ℝ) *
        twoFiberQuotientThirdStep (d := d) (a := a) (b := b) L R T = 0 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast D.d_pos.ne'
  have hd10 : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hab := twoFiber_quotient_cast_sum D
  have hb : (b : ℝ) = (d : ℝ) - 1 - a := by linarith
  unfold twoFiberQuotientLeftStep twoFiberQuotientRightStep
    twoFiberQuotientThirdStep
  norm_num only [Nat.cast_add, Nat.cast_one] at hmean ⊢
  rw [hb] at hmean ⊢
  field_simp
  linear_combination hmean

theorem twoFiber_quotientU_step (D : TwoFiberData Z d m a b)
    (L R T : ℝ) :
    twoFiberQuotientU (d := d)
      (twoFiberQuotientLeftStep (d := d) (a := a) (b := b) L R T)
      (twoFiberQuotientRightStep (d := d) (a := a) (b := b) L R T) =
      (1 / (d + 1 : ℕ)) * twoFiberQuotientU (d := d) L R := by
  have hdm1 : (d : ℝ) - 1 ≠ 0 := by
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast D.hd
    nlinarith
  have hd10 : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold twoFiberQuotientU twoFiberQuotientLeftStep
    twoFiberQuotientRightStep
  norm_num only [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem twoFiber_quotientV_step (D : TwoFiberData Z d m a b)
    (L R T : ℝ)
    (hmean : (a : ℝ) * (d + 1 : ℕ) * L +
      (b : ℝ) * (d + 1 : ℕ) * R + (d : ℝ) * T = 0) :
    twoFiberQuotientV (d := d)
      (twoFiberQuotientThirdStep (d := d) (a := a) (b := b) L R T) =
      (1 / ((d : ℝ) * (d + 1 : ℕ))) *
        twoFiberQuotientV (d := d) T := by
  let U := twoFiberQuotientU (d := d) L R
  let V := twoFiberQuotientV (d := d) T
  have hL : L = (b : ℝ) * U + (d : ℝ) * V := by
    simpa only [U, V] using twoFiber_quotient_reconstruct_left D L R T hmean
  have hR : R = -(a : ℝ) * U + (d : ℝ) * V := by
    simpa only [U, V] using twoFiber_quotient_reconstruct_right D L R T hmean
  have hT : T = -((d : ℝ) ^ 2 - 1) * V := by
    simpa only [V] using twoFiber_quotient_reconstruct_third D T
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast D.d_pos.ne'
  have hd10 : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hdsq1 : (d : ℝ) ^ 2 - 1 ≠ 0 := by
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast D.hd
    nlinarith
  have hab := twoFiber_quotient_cast_sum D
  have hb : (b : ℝ) = (d : ℝ) - 1 - a := by linarith
  change twoFiberQuotientV (d := d)
      (twoFiberQuotientThirdStep (d := d) (a := a) (b := b) L R T) =
    (1 / ((d : ℝ) * (d + 1 : ℕ))) * V
  rw [hL, hR, hT, hb]
  unfold twoFiberQuotientV twoFiberQuotientThirdStep
  simp only [hb]
  norm_num only [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- The quotient output contracts in stationary energy by `1/d²`. -/
theorem twoFiber_quotient_energy_contracts (D : TwoFiberData Z d m a b)
    (L R T : ℝ)
    (hmean : (a : ℝ) * (d + 1 : ℕ) * L +
      (b : ℝ) * (d + 1 : ℕ) * R + (d : ℝ) * T = 0) :
    twoFiberQuotientEnergy (d := d) (a := a) (b := b)
        (twoFiberQuotientLeftStep (d := d) (a := a) (b := b) L R T)
        (twoFiberQuotientRightStep (d := d) (a := a) (b := b) L R T)
        (twoFiberQuotientThirdStep (d := d) (a := a) (b := b) L R T) ≤
      (1 / (d : ℝ)) ^ 2 *
        twoFiberQuotientEnergy (d := d) (a := a) (b := b) L R T := by
  rw [twoFiber_quotient_energy_sos D _ _ _
      (twoFiber_quotient_step_mean_zero D L R T hmean),
    twoFiber_quotient_energy_sos D L R T hmean,
    twoFiber_quotientU_step D L R T,
    twoFiber_quotientV_step D L R T hmean]
  have hq1 := twoFiberListedEigenvalue_bound D
    (TwoFiberListedEigenvalue.quotientOne (d := d) (m := m) (a := a) (b := b))
  have hq2 := twoFiberListedEigenvalue_bound D
    (TwoFiberListedEigenvalue.quotientTwo (d := d) (m := m) (a := a) (b := b))
  have htarget : 0 ≤ 1 / (d : ℝ) := by positivity
  have hq1sq : (1 / ((d : ℝ) + 1)) ^ 2 ≤ (1 / (d : ℝ)) ^ 2 := by
    calc
      (1 / ((d : ℝ) + 1)) ^ 2 = |1 / ((d : ℝ) + 1)| ^ 2 :=
        (sq_abs _).symm
      _ ≤ (1 / (d : ℝ)) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) htarget).2 (by simpa using hq1)
  have hq2sq : (1 / ((d : ℝ) * ((d : ℝ) + 1))) ^ 2 ≤
      (1 / (d : ℝ)) ^ 2 := by
    calc
      (1 / ((d : ℝ) * ((d : ℝ) + 1))) ^ 2 =
          |1 / ((d : ℝ) * ((d : ℝ) + 1))| ^ 2 := (sq_abs _).symm
      _ ≤ (1 / (d : ℝ)) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) htarget).2 hq2
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast D.hd
  have hdsq : 0 ≤ (d : ℝ) ^ 2 - 1 := by nlinarith
  have hA : 0 ≤ (a : ℝ) * b * ((d : ℝ) ^ 2 - 1) := by positivity
  have hB : 0 ≤ (d : ℝ) * ((d : ℝ) ^ 2 - 1) *
      ((d : ℝ) ^ 2 + d - 1) := by
    have hlast : 0 ≤ (d : ℝ) ^ 2 + d - 1 := by nlinarith
    positivity
  have hU : 0 ≤ (twoFiberQuotientU (d := d) L R) ^ 2 := sq_nonneg _
  have hV : 0 ≤ (twoFiberQuotientV (d := d) T) ^ 2 := sq_nonneg _
  calc
    _ ≤
        (a : ℝ) * b * ((d : ℝ) ^ 2 - 1) *
            ((1 / (d : ℝ)) ^ 2 * (twoFiberQuotientU (d := d) L R) ^ 2) +
          ((d : ℝ) * ((d : ℝ) ^ 2 - 1) *
            ((d : ℝ) ^ 2 + d - 1)) *
            ((1 / (d : ℝ)) ^ 2 * (twoFiberQuotientV (d := d) T) ^ 2) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ hA
        simpa [mul_pow] using mul_le_mul_of_nonneg_right hq1sq hU
      · apply mul_le_mul_of_nonneg_left _ hB
        simpa [mul_pow] using mul_le_mul_of_nonneg_right hq2sq hV
    _ = _ := by ring

theorem twoFiber_left_sum_sq (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    (∑ i : Fin (m - a), (f (Sum.inl i)) ^ 2) =
      (m - a : ℕ) * (leftAverage f) ^ 2 +
        ∑ i : Fin (m - a), (f (Sum.inl i) - leftAverage f) ^ 2 := by
  have hzero := leftResidual_sum_zero D f
  have hpoint (i : Fin (m - a)) :
      f (Sum.inl i) = leftAverage f + (f (Sum.inl i) - leftAverage f) := by ring
  calc
    _ = ∑ i : Fin (m - a),
        (leftAverage f + (f (Sum.inl i) - leftAverage f)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← hpoint i]
    _ = _ := by
      simp_rw [add_sq]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, hzero, mul_zero, add_zero]

theorem twoFiber_right_sum_sq (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    (∑ i : Fin (m - b), (f (Sum.inr (Sum.inl i))) ^ 2) =
      (m - b : ℕ) * (rightAverage f) ^ 2 +
        ∑ i : Fin (m - b),
          (f (Sum.inr (Sum.inl i)) - rightAverage f) ^ 2 := by
  have hzero := rightResidual_sum_zero D f
  have hpoint (i : Fin (m - b)) :
      f (Sum.inr (Sum.inl i)) =
        rightAverage f + (f (Sum.inr (Sum.inl i)) - rightAverage f) := by ring
  calc
    _ = ∑ i : Fin (m - b),
        (rightAverage f +
          (f (Sum.inr (Sum.inl i)) - rightAverage f)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← hpoint i]
    _ = _ := by
      simp_rw [add_sq]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, hzero, mul_zero, add_zero]

theorem twoFiber_thirdWithin_sum_sq (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) (z : Z) :
    (∑ i : Fin m, (f (Sum.inr (Sum.inr (z, i)))) ^ 2) =
      (m : ℝ) * (thirdFiberAverage f z) ^ 2 +
        ∑ i : Fin m,
          (f (Sum.inr (Sum.inr (z, i))) - thirdFiberAverage f z) ^ 2 := by
  have hzero := thirdWithinResidual_sum_zero D f z
  have hpoint (i : Fin m) :
      f (Sum.inr (Sum.inr (z, i))) = thirdFiberAverage f z +
        (f (Sum.inr (Sum.inr (z, i))) - thirdFiberAverage f z) := by ring
  calc
    _ = ∑ i : Fin m, (thirdFiberAverage f z +
        (f (Sum.inr (Sum.inr (z, i))) - thirdFiberAverage f z)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← hpoint i]
    _ = _ := by
      simp_rw [add_sq]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, hzero, mul_zero, add_zero]

theorem twoFiber_thirdPetal_sum_sq (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    (∑ z : Z, D.omega z * (thirdFiberAverage f z) ^ 2) =
      (thirdAverage D f) ^ 2 +
        ∑ z : Z, D.omega z *
          (thirdFiberAverage f z - thirdAverage D f) ^ 2 := by
  have hzero := thirdPetalResidual_weighted_zero D f
  calc
    _ = ∑ z : Z, D.omega z *
        (thirdAverage D f +
          (thirdFiberAverage f z - thirdAverage D f)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro z _hz
      congr 2
      ring
    _ = (∑ z : Z, D.omega z) * (thirdAverage D f) ^ 2 +
        2 * thirdAverage D f *
          (∑ z : Z, D.omega z *
            (thirdFiberAverage f z - thirdAverage D f)) +
        ∑ z : Z, D.omega z *
          (thirdFiberAverage f z - thirdAverage D f) ^ 2 := by
      calc
        _ = ∑ z : Z,
            (D.omega z * (thirdAverage D f) ^ 2 +
              2 * thirdAverage D f *
                (D.omega z * (thirdFiberAverage f z - thirdAverage D f)) +
              D.omega z *
                (thirdFiberAverage f z - thirdAverage D f) ^ 2) := by
          apply Finset.sum_congr rfl
          intro z _hz
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.sum_mul, Finset.mul_sum]
    _ = _ := by rw [D.omega_sum, hzero]; ring

/-- Full stationary-energy Pythagorean identity: quotient, the two occupied
fiber residuals, within-third-fiber residuals, and petal residuals. -/
theorem twoFiber_sqNorm_decomposition (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    (twoFiberGraph D).sqNorm f =
      twoFiberQuotientEnergy (d := d) (a := a) (b := b)
        (leftAverage f) (rightAverage f) (thirdAverage D f) +
      ((a : ℝ) * (d + 1 : ℕ) / (m - a : ℕ)) *
        ∑ i : Fin (m - a), (f (Sum.inl i) - leftAverage f) ^ 2 +
      ((b : ℝ) * (d + 1 : ℕ) / (m - b : ℕ)) *
        ∑ i : Fin (m - b),
          (f (Sum.inr (Sum.inl i)) - rightAverage f) ^ 2 +
      ∑ z : Z, ((d : ℝ) * D.omega z / m) *
        ∑ i : Fin m,
          (f (Sum.inr (Sum.inr (z, i))) - thirdFiberAverage f z) ^ 2 +
      (d : ℝ) * ∑ z : Z, D.omega z *
        (thirdFiberAverage f z - thirdAverage D f) ^ 2 := by
  rw [twoFiberGraph_sqNorm D f, twoFiber_left_sum_sq D f,
    twoFiber_right_sum_sq D f]
  simp_rw [twoFiber_thirdWithin_sum_sq D f]
  have hma0 : ((m - a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt D.a_lt_m).ne'
  have hmb0 : ((m - b : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt D.b_lt_m).ne'
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt D.one_lt_m).ne'
  rw [show (∑ z : Z, ((d : ℝ) * D.omega z / m) *
        ((m : ℝ) * (thirdFiberAverage f z) ^ 2 +
          ∑ i : Fin m,
            (f (Sum.inr (Sum.inr (z, i))) - thirdFiberAverage f z) ^ 2)) =
      (d : ℝ) * (∑ z : Z, D.omega z * (thirdFiberAverage f z) ^ 2) +
        ∑ z : Z, ((d : ℝ) * D.omega z / m) *
          ∑ i : Fin m,
            (f (Sum.inr (Sum.inr (z, i))) - thirdFiberAverage f z) ^ 2 by
      calc
        _ = ∑ z : Z,
            ((d : ℝ) * (D.omega z * (thirdFiberAverage f z) ^ 2) +
              ((d : ℝ) * D.omega z / m) *
                ∑ i : Fin m,
                  (f (Sum.inr (Sum.inr (z, i))) - thirdFiberAverage f z) ^ 2) := by
          apply Finset.sum_congr rfl
          intro z _hz
          field_simp
        _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]]
  rw [twoFiber_thirdPetal_sum_sq D f]
  unfold twoFiberQuotientEnergy
  field_simp
  ring

theorem twoFiber_leftCentered_operator (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) (i : Fin (m - a)) :
    twoFiberOperator D f (Sum.inl i) - leftAverage (twoFiberOperator D f) =
      (-(a + 1 : ℕ) / ((d + 1 : ℕ) * (m - a - 1 : ℕ))) *
        (f (Sum.inl i) - leftAverage f) := by
  have hsum : (∑ j : Fin (m - a), f (Sum.inl j)) =
      (m - a : ℕ) * leftAverage f := by
    unfold leftAverage
    have hpos : 0 < m - a := Nat.sub_pos_of_lt D.a_lt_m
    field_simp
  simp only [twoFiberOperator]
  rw [leftAverage_operator D f, sumExcept_eq_total_sub, hsum]
  have hma1 : ((m - a - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt D.one_lt_m_sub_a).ne'
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hcast : ((m - a - 1 : ℕ) : ℝ) = (m - a : ℕ) - 1 := by
    rw [Nat.cast_sub (Nat.le_of_lt D.one_lt_m_sub_a), Nat.cast_one]
  have hcast0 : ((m - a : ℕ) : ℝ) - 1 ≠ 0 := by
    rw [← hcast]
    exact hma1
  rw [hcast]
  field_simp [hcast0]
  ring

theorem twoFiber_rightCentered_operator (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) (i : Fin (m - b)) :
    twoFiberOperator D f (Sum.inr (Sum.inl i)) -
        rightAverage (twoFiberOperator D f) =
      (-(b + 1 : ℕ) / ((d + 1 : ℕ) * (m - b - 1 : ℕ))) *
        (f (Sum.inr (Sum.inl i)) - rightAverage f) := by
  have hsum : (∑ j : Fin (m - b), f (Sum.inr (Sum.inl j))) =
      (m - b : ℕ) * rightAverage f := by
    unfold rightAverage
    have hpos : 0 < m - b := Nat.sub_pos_of_lt D.b_lt_m
    field_simp
  simp only [twoFiberOperator]
  rw [rightAverage_operator D f, sumExcept_eq_total_sub, hsum]
  have hmb1 : ((m - b - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt D.one_lt_m_sub_b).ne'
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hcast : ((m - b - 1 : ℕ) : ℝ) = (m - b : ℕ) - 1 := by
    rw [Nat.cast_sub (Nat.le_of_lt D.one_lt_m_sub_b), Nat.cast_one]
  have hcast0 : ((m - b : ℕ) : ℝ) - 1 ≠ 0 := by
    rw [← hcast]
    exact hmb1
  rw [hcast]
  field_simp [hcast0]
  ring

theorem twoFiber_thirdWithinCentered_operator (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) (z : Z) (i : Fin m) :
    twoFiberOperator D f (Sum.inr (Sum.inr (z, i))) -
        thirdFiberAverage (twoFiberOperator D f) z =
      (-1 / ((d : ℝ) * (m - 1 : ℕ))) *
        (f (Sum.inr (Sum.inr (z, i))) - thirdFiberAverage f z) := by
  have hsum : (∑ j : Fin m, f (Sum.inr (Sum.inr (z, j)))) =
      (m : ℝ) * thirdFiberAverage f z := by
    unfold thirdFiberAverage
    have hm0 : (m : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.zero_lt_of_lt D.one_lt_m).ne'
    field_simp
  simp only [twoFiberOperator]
  rw [thirdFiberAverage_operator D f z, sumExcept_eq_total_sub, hsum]
  have hm1 : ((m - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt D.one_lt_m).ne'
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.le_of_lt D.one_lt_m), Nat.cast_one]
  have hcast0 : (m : ℝ) - 1 ≠ 0 := by rw [← hcast]; exact hm1
  rw [hcast]
  field_simp [hcast0]
  ring

theorem twoFiber_thirdPetalCentered_operator (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) (z : Z) :
    thirdFiberAverage (twoFiberOperator D f) z -
        thirdAverage D (twoFiberOperator D f) =
      (1 / (d : ℝ)) *
        (thirdFiberAverage f z - thirdAverage D f) := by
  rw [thirdFiberAverage_operator D f z, thirdAverage_operator D f]
  ring

/-- Exact orthogonal output energy for an arbitrary input. -/
theorem twoFiber_walk_sqNorm_decomposition (D : TwoFiberData Z d m a b)
    (f : TwoFiberVertex Z m a b → ℝ) :
    (twoFiberGraph D).sqNorm ((twoFiberGraph D).walk f) =
      twoFiberQuotientEnergy (d := d) (a := a) (b := b)
        (twoFiberQuotientLeftStep (d := d) (a := a) (b := b)
          (leftAverage f) (rightAverage f) (thirdAverage D f))
        (twoFiberQuotientRightStep (d := d) (a := a) (b := b)
          (leftAverage f) (rightAverage f) (thirdAverage D f))
        (twoFiberQuotientThirdStep (d := d) (a := a) (b := b)
          (leftAverage f) (rightAverage f) (thirdAverage D f)) +
      (-(a + 1 : ℕ) / ((d + 1 : ℕ) * (m - a - 1 : ℕ))) ^ 2 *
        (((a : ℝ) * (d + 1 : ℕ) / (m - a : ℕ)) *
          ∑ i : Fin (m - a), (f (Sum.inl i) - leftAverage f) ^ 2) +
      (-(b + 1 : ℕ) / ((d + 1 : ℕ) * (m - b - 1 : ℕ))) ^ 2 *
        (((b : ℝ) * (d + 1 : ℕ) / (m - b : ℕ)) *
          ∑ i : Fin (m - b),
            (f (Sum.inr (Sum.inl i)) - rightAverage f) ^ 2) +
      (-1 / ((d : ℝ) * (m - 1 : ℕ))) ^ 2 *
        (∑ z : Z, ((d : ℝ) * D.omega z / m) *
          ∑ i : Fin m,
            (f (Sum.inr (Sum.inr (z, i))) - thirdFiberAverage f z) ^ 2) +
      (1 / (d : ℝ)) ^ 2 *
        ((d : ℝ) * ∑ z : Z, D.omega z *
          (thirdFiberAverage f z - thirdAverage D f) ^ 2) := by
  rw [twoFiberGraph_walk_eq_operator D f,
    twoFiber_sqNorm_decomposition D (twoFiberOperator D f)]
  simp_rw [twoFiber_leftCentered_operator D f,
    twoFiber_rightCentered_operator D f,
    twoFiber_thirdWithinCentered_operator D f,
    twoFiber_thirdPetalCentered_operator D f]
  rw [leftAverage_operator D f, rightAverage_operator D f,
    thirdAverage_operator D f]
  unfold twoFiberQuotientLeftStep twoFiberQuotientRightStep
    twoFiberQuotientThirdStep
  simp_rw [mul_pow]
  simp_rw [Finset.mul_sum]
  ring_nf
  ac_rfl

/-- Complete canonical two-fiber estimate, proved directly on every
stationary-mean-zero function. -/
theorem twoFiberGraph_twoSidedSpectralBound (D : TwoFiberData Z d m a b) :
    (twoFiberGraph D).TwoSidedSpectralBound (1 / (d : ℝ)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast D.d_pos
  refine ⟨(one_div_pos.mpr hdpos).le, ?_⟩
  intro f hmean
  rw [twoFiber_walk_sqNorm_decomposition D f,
    twoFiber_sqNorm_decomposition D f]
  let r : ℝ := 1 / (d : ℝ)
  let Q : ℝ := twoFiberQuotientEnergy (d := d) (a := a) (b := b)
    (leftAverage f) (rightAverage f) (thirdAverage D f)
  let Q' : ℝ := twoFiberQuotientEnergy (d := d) (a := a) (b := b)
    (twoFiberQuotientLeftStep (d := d) (a := a) (b := b)
      (leftAverage f) (rightAverage f) (thirdAverage D f))
    (twoFiberQuotientRightStep (d := d) (a := a) (b := b)
      (leftAverage f) (rightAverage f) (thirdAverage D f))
    (twoFiberQuotientThirdStep (d := d) (a := a) (b := b)
      (leftAverage f) (rightAverage f) (thirdAverage D f))
  let EL : ℝ := ((a : ℝ) * (d + 1 : ℕ) / (m - a : ℕ)) *
    ∑ i : Fin (m - a), (f (Sum.inl i) - leftAverage f) ^ 2
  let ER : ℝ := ((b : ℝ) * (d + 1 : ℕ) / (m - b : ℕ)) *
    ∑ i : Fin (m - b),
      (f (Sum.inr (Sum.inl i)) - rightAverage f) ^ 2
  let EW : ℝ := ∑ z : Z, ((d : ℝ) * D.omega z / m) *
    ∑ i : Fin m,
      (f (Sum.inr (Sum.inr (z, i))) - thirdFiberAverage f z) ^ 2
  let EP : ℝ := (d : ℝ) * ∑ z : Z, D.omega z *
    (thirdFiberAverage f z - thirdAverage D f) ^ 2
  let eL : ℝ := -(a + 1 : ℕ) / ((d + 1 : ℕ) * (m - a - 1 : ℕ))
  let eR : ℝ := -(b + 1 : ℕ) / ((d + 1 : ℕ) * (m - b - 1 : ℕ))
  let eW : ℝ := -1 / ((d : ℝ) * (m - 1 : ℕ))
  have hQ : Q' ≤ r ^ 2 * Q := by
    dsimp only [Q', Q, r]
    exact twoFiber_quotient_energy_contracts D _ _ _
      (twoFiber_average_relation D f hmean)
  have hEL : 0 ≤ EL := by
    dsimp only [EL]
    positivity
  have hER : 0 ≤ ER := by
    dsimp only [ER]
    positivity
  have hEW : 0 ≤ EW := by
    dsimp only [EW]
    have hmnonneg : (0 : ℝ) ≤ m := by positivity
    apply Finset.sum_nonneg
    intro z _hz
    exact mul_nonneg
      (div_nonneg (mul_nonneg hdpos.le (D.omega_pos z).le) hmnonneg)
      (Finset.sum_nonneg fun i _hi ↦ sq_nonneg _)
  have hEP : 0 ≤ EP := by
    dsimp only [EP]
    exact mul_nonneg hdpos.le (Finset.sum_nonneg fun z _hz ↦
      mul_nonneg (D.omega_pos z).le (sq_nonneg _))
  have hsquare {x : ℝ} (hx : |x| ≤ r) : x ^ 2 ≤ r ^ 2 := by
    have hr : 0 ≤ r := by dsimp only [r]; positivity
    calc
      x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ r ^ 2 := (sq_le_sq₀ (abs_nonneg x) hr).2 hx
  have heL : eL ^ 2 ≤ r ^ 2 := by
    apply hsquare
    have hcast : ((m - a - 1 : ℕ) : ℝ) = (m : ℝ) - a - 1 := by
      rw [Nat.cast_sub (Nat.le_of_lt D.one_lt_m_sub_a),
        Nat.cast_sub (Nat.le_of_lt D.a_lt_m)]
      norm_num
    dsimp only [eL, r]
    simpa only [Nat.cast_add, Nat.cast_one, hcast] using
      twoFiberListedEigenvalue_bound D
        (TwoFiberListedEigenvalue.leftWithin
          (d := d) (m := m) (a := a) (b := b))
  have heR : eR ^ 2 ≤ r ^ 2 := by
    apply hsquare
    have hcast : ((m - b - 1 : ℕ) : ℝ) = (m : ℝ) - b - 1 := by
      rw [Nat.cast_sub (Nat.le_of_lt D.one_lt_m_sub_b),
        Nat.cast_sub (Nat.le_of_lt D.b_lt_m)]
      norm_num
    dsimp only [eR, r]
    simpa only [Nat.cast_add, Nat.cast_one, hcast] using
      twoFiberListedEigenvalue_bound D
        (TwoFiberListedEigenvalue.rightWithin
          (d := d) (m := m) (a := a) (b := b))
  have heW : eW ^ 2 ≤ r ^ 2 := by
    apply hsquare
    dsimp only [eW, r]
    simpa only [Nat.cast_sub (Nat.le_of_lt D.one_lt_m), Nat.cast_one] using
      twoFiberListedEigenvalue_bound D
        (TwoFiberListedEigenvalue.thirdWithin
          (d := d) (m := m) (a := a) (b := b))
  change Q' + eL ^ 2 * EL + eR ^ 2 * ER + eW ^ 2 * EW + r ^ 2 * EP ≤
    r ^ 2 * (Q + EL + ER + EW + EP)
  calc
    Q' + eL ^ 2 * EL + eR ^ 2 * ER + eW ^ 2 * EW + r ^ 2 * EP ≤
        r ^ 2 * Q + r ^ 2 * EL + r ^ 2 * ER + r ^ 2 * EW + r ^ 2 * EP := by
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · exact add_le_add hQ (mul_le_mul_of_nonneg_right heL hEL)
          · exact mul_le_mul_of_nonneg_right heR hER
        · exact mul_le_mul_of_nonneg_right heW hEW
      · rfl
    _ = r ^ 2 * (Q + EL + ER + EW + EP) := by ring

end Model

end WeightedLift

end HDXLean
