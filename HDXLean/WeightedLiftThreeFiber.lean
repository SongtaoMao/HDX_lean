import HDXLean.WeightedLiftLinks
import HDXLean.WeightedLiftSpectrum
import HDXLean.WeightedGraphScaling
import HDXLean.Relabeling
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The three-fiber conditioned link in the weighted dimension lift

This file supplies the full finite calculation omitted in the first case of
Theorem 5.1.  If a codimension-two face meets all three fibers of its unique
parent triangle, and the occupancies are `a i`, its link is (up to a common
positive scaling of all edge weights) the graph defined below.  Its vertices
in part `i` are the `n i` unused labels, where `a i + n i = m`.

The proof does not merely list eigenvalues.  It computes the degree and walk,
splits every function into its three fiber averages and within-fiber zero-sum
parts, proves that this is an orthogonal decomposition for the stationary
inner product, and establishes the claimed `1 / d` contraction.
-/

namespace HDXLean

open scoped BigOperators

namespace WeightedLift

/-- The canonical vertex set of a three-fiber conditioned link. -/
abbrev ThreeFiberVertex (n : Fin 3 → ℕ) := Σ i, Fin (n i)

/-- The sum of a function over one fiber of the canonical model. -/
noncomputable def threeFiberSum {n : Fin 3 → ℕ}
    (f : ThreeFiberVertex n → ℝ) (i : Fin 3) : ℝ :=
  ∑ x : Fin (n i), f ⟨i, x⟩

/-- The average of a function on one fiber. -/
noncomputable def threeFiberAverage {n : Fin 3 → ℕ}
    (f : ThreeFiberVertex n → ℝ) (i : Fin 3) : ℝ :=
  threeFiberSum f i / (n i : ℝ)

/-- Canonical edge weights in the all-three-fibers case.  They have been
divided by the common positive factor coming from the base triangle and the
three factors `g m (a i)`.  This does not alter the random walk. -/
noncomputable def threeFiberWeight (a n : Fin 3 → ℕ)
    (u v : ThreeFiberVertex n) : ℝ :=
  if u = v then 0
  else if h : u.1 = v.1 then
    (a u.1 : ℝ) * (a u.1 + 1 : ℕ) /
      ((n u.1 : ℝ) * (n u.1 - 1 : ℕ))
  else
    (a u.1 : ℝ) * (a v.1 : ℝ) /
      ((n u.1 : ℝ) * (n v.1 : ℝ))

theorem threeFiberWeight_symm (a n : Fin 3 → ℕ)
    (u v : ThreeFiberVertex n) :
    threeFiberWeight a n u v = threeFiberWeight a n v u := by
  classical
  by_cases huv : u = v
  · subst v
    simp [threeFiberWeight]
  · have hvu : v ≠ u := Ne.symm huv
    by_cases hij : u.1 = v.1
    · have hji : v.1 = u.1 := hij.symm
      unfold threeFiberWeight
      rw [if_neg huv, if_neg hvu, dif_pos hij, dif_pos hji]
      rw [hij]
    · have hji : v.1 ≠ u.1 := fun h ↦ hij h.symm
      unfold threeFiberWeight
      rw [if_neg huv, if_neg hvu, dif_neg hij, dif_neg hji]
      ring

theorem threeFiberWeight_nonneg (a n : Fin 3 → ℕ)
    (u v : ThreeFiberVertex n) : 0 ≤ threeFiberWeight a n u v := by
  classical
  unfold threeFiberWeight
  split_ifs
  · exact le_rfl
  · positivity
  · positivity

/-- The canonical reversible weighted graph for the three-fiber case. -/
noncomputable def threeFiberGraph (a n : Fin 3 → ℕ) :
    WeightedGraph (ThreeFiberVertex n) where
  weight := threeFiberWeight a n
  weight_symm := threeFiberWeight_symm a n
  weight_self u := by simp [threeFiberWeight]
  weight_nonneg := threeFiberWeight_nonneg a n

/-- The elementary identity `∑_{j ≠ i} a_j = d - 1 - a_i`, stated in the
form needed by the degree and walk computations. -/
theorem sum_fin_three_erase {a : Fin 3 → ℕ} {d : ℕ}
    (ha : ∑ i, a i = d - 1) (hd : 1 ≤ d) (i : Fin 3) :
    ∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)), a j = d - 1 - a i := by
  have hsplit :
      (∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)), a j) + a i =
        ∑ j : Fin 3, a j := by
    simpa using Finset.sum_erase_add
      (Finset.univ : Finset (Fin 3)) a (Finset.mem_univ i)
  omega

theorem threeFiberWeight_sum_same (a n : Fin 3 → ℕ)
    (hn : ∀ i, 2 ≤ n i) (i : Fin 3) (x : Fin (n i)) :
    ∑ y : Fin (n i),
        threeFiberWeight a n ⟨i, x⟩ ⟨i, y⟩ =
      (a i : ℝ) * (a i + 1 : ℕ) / (n i : ℝ) := by
  classical
  let c : ℝ :=
    (a i : ℝ) * (a i + 1 : ℕ) /
      ((n i : ℝ) * (n i - 1 : ℕ))
  have hpoint (y : Fin (n i)) :
      threeFiberWeight a n ⟨i, x⟩ ⟨i, y⟩ =
        if x = y then 0 else c := by
    by_cases hxy : x = y
    · subst y
      simp [threeFiberWeight]
    · simp [threeFiberWeight, hxy, c]
  simp_rw [hpoint]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, zero_add]
  have hcard :
      ((Finset.univ.filter fun y : Fin (n i) ↦ ¬x = y).card : ℝ) =
        (n i - 1 : ℕ) := by
    have herase :
        Finset.univ.filter (fun y : Fin (n i) ↦ ¬x = y) =
          Finset.univ.erase x := by
      ext y
      simp [eq_comm]
    rw [herase, Finset.card_erase_of_mem (Finset.mem_univ x)]
    simp
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hcard]
  dsimp [c]
  have hni := hn i
  have hnpos : (0 : ℝ) < n i := by exact_mod_cast (by omega : 0 < n i)
  have hnsubpos : (0 : ℝ) < (n i - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < n i - 1)
  field_simp

theorem threeFiberWeight_sum_cross (a n : Fin 3 → ℕ)
    (hn : ∀ i, 1 ≤ n i) {i j : Fin 3} (hij : i ≠ j)
    (x : Fin (n i)) :
    ∑ y : Fin (n j),
        threeFiberWeight a n ⟨i, x⟩ ⟨j, y⟩ =
      (a i : ℝ) * (a j : ℝ) / (n i : ℝ) := by
  classical
  have hpoint (y : Fin (n j)) :
      threeFiberWeight a n ⟨i, x⟩ ⟨j, y⟩ =
        (a i : ℝ) * (a j : ℝ) /
          ((n i : ℝ) * (n j : ℝ)) := by
    have hvertex : (⟨i, x⟩ : ThreeFiberVertex n) ≠ ⟨j, y⟩ := by
      intro h
      exact hij (congrArg Sigma.fst h)
    simp [threeFiberWeight, hvertex, hij]
  simp_rw [hpoint]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fin]
  have hnipos : (0 : ℝ) < n i := by exact_mod_cast hn i
  have hnjpos : (0 : ℝ) < n j := by exact_mod_cast hn j
  field_simp

/-- Exact stationary degree of every vertex in fiber `i`. -/
theorem threeFiberGraph_degree (a n : Fin 3 → ℕ) {d : ℕ}
    (ha : ∑ i, a i = d - 1) (hd : 1 ≤ d)
    (hn : ∀ i, 2 ≤ n i) (i : Fin 3) (x : Fin (n i)) :
    (threeFiberGraph a n).degree ⟨i, x⟩ =
      (d : ℝ) * (a i : ℝ) / (n i : ℝ) := by
  classical
  unfold WeightedGraph.degree threeFiberGraph
  rw [Fintype.sum_sigma]
  let S : Fin 3 → ℝ := fun j ↦
    ∑ y : Fin (n j), threeFiberWeight a n ⟨i, x⟩ ⟨j, y⟩
  have hsplit : (∑ j : Fin 3, S j) =
      S i + ∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)), S j := by
    have h := Finset.sum_erase_add
      (Finset.univ : Finset (Fin 3)) S (Finset.mem_univ i)
    rw [← h]
    ac_rfl
  change (∑ j : Fin 3, S j) = _
  rw [hsplit]
  have hsame : S i =
      (a i : ℝ) * (a i + 1 : ℕ) / (n i : ℝ) := by
    exact threeFiberWeight_sum_same a n hn i x
  rw [hsame]
  have hcross :
      (∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)), S j) =
        (a i : ℝ) / (n i : ℝ) *
          (∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)), (a j : ℝ)) := by
    calc
      (∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)), S j) =
          ∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)),
            (a i : ℝ) * (a j : ℝ) / (n i : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact threeFiberWeight_sum_cross a n (fun k ↦ (hn k).trans' (by omega))
          (Finset.ne_of_mem_erase hj).symm x
      _ = (a i : ℝ) / (n i : ℝ) *
          (∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)), (a j : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
  rw [hcross]
  have heraseNat := sum_fin_three_erase ha hd i
  have heraseReal :
      (∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)), (a j : ℝ)) =
        (d - 1 - a i : ℕ) := by
    exact_mod_cast heraseNat
  rw [heraseReal]
  have hai : a i ≤ d - 1 := by
    have hnonneg :
        a i ≤ ∑ j : Fin 3, a j := Finset.single_le_sum
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hcastSub : ((d - 1 - a i : ℕ) : ℝ) =
      (d : ℝ) - 1 - a i := by
    rw [Nat.cast_sub hai]
    rw [Nat.cast_sub hd]
    norm_num
  rw [hcastSub]
  have hnpos : (0 : ℝ) < n i := by
    have hni := hn i
    exact_mod_cast (by omega : 0 < n i)
  field_simp
  push_cast
  ring

/-- The weighted contribution from the other vertices of the same fiber. -/
theorem threeFiber_weighted_sum_same (a n : Fin 3 → ℕ)
    (i : Fin 3) (x : Fin (n i)) (f : ThreeFiberVertex n → ℝ) :
    ∑ y : Fin (n i),
        threeFiberWeight a n ⟨i, x⟩ ⟨i, y⟩ * f ⟨i, y⟩ =
      ((a i : ℝ) * (a i + 1 : ℕ) /
          ((n i : ℝ) * (n i - 1 : ℕ))) *
        (threeFiberSum f i - f ⟨i, x⟩) := by
  classical
  let c : ℝ :=
    (a i : ℝ) * (a i + 1 : ℕ) /
      ((n i : ℝ) * (n i - 1 : ℕ))
  have hpoint (y : Fin (n i)) :
      threeFiberWeight a n ⟨i, x⟩ ⟨i, y⟩ * f ⟨i, y⟩ =
        if x = y then 0 else c * f ⟨i, y⟩ := by
    by_cases hxy : x = y
    · subst y
      simp [threeFiberWeight]
    · simp [threeFiberWeight, hxy, c]
  simp_rw [hpoint]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, zero_add]
  have herase :
      Finset.univ.filter (fun y : Fin (n i) ↦ ¬x = y) =
        Finset.univ.erase x := by
    ext y
    simp [eq_comm]
  rw [herase, ← Finset.mul_sum]
  have hsumErase :
      (∑ y ∈ (Finset.univ.erase x : Finset (Fin (n i))), f ⟨i, y⟩) =
        threeFiberSum f i - f ⟨i, x⟩ := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin (n i)))
      (fun y ↦ f ⟨i, y⟩) (Finset.mem_univ x)
    unfold threeFiberSum
    linarith
  rw [hsumErase]

/-- The weighted contribution from a different fiber. -/
theorem threeFiber_weighted_sum_cross (a n : Fin 3 → ℕ)
    {i j : Fin 3} (hij : i ≠ j) (x : Fin (n i))
    (f : ThreeFiberVertex n → ℝ) :
    ∑ y : Fin (n j),
        threeFiberWeight a n ⟨i, x⟩ ⟨j, y⟩ * f ⟨j, y⟩ =
      ((a i : ℝ) * (a j : ℝ) /
          ((n i : ℝ) * (n j : ℝ))) * threeFiberSum f j := by
  classical
  have hpoint (y : Fin (n j)) :
      threeFiberWeight a n ⟨i, x⟩ ⟨j, y⟩ =
        (a i : ℝ) * (a j : ℝ) /
          ((n i : ℝ) * (n j : ℝ)) := by
    have hvertex : (⟨i, x⟩ : ThreeFiberVertex n) ≠ ⟨j, y⟩ := by
      intro h
      exact hij (congrArg Sigma.fst h)
    simp [threeFiberWeight, hvertex, hij]
  simp_rw [hpoint]
  rw [← Finset.mul_sum]
  rfl

/-- Exact random-walk formula in the all-three-fibers case. -/
theorem threeFiberGraph_walk (a n : Fin 3 → ℕ) {d : ℕ}
    (ha : ∑ i, a i = d - 1) (hd : 1 ≤ d)
    (hapos : ∀ i, 1 ≤ a i) (hn : ∀ i, 2 ≤ n i)
    (f : ThreeFiberVertex n → ℝ) (i : Fin 3) (x : Fin (n i)) :
    (threeFiberGraph a n).walk f ⟨i, x⟩ =
      (a i + 1 : ℕ) /
          ((d : ℝ) * (n i - 1 : ℕ)) *
          (threeFiberSum f i - f ⟨i, x⟩) +
        ∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)),
          (a j : ℝ) / ((d : ℝ) * (n j : ℝ)) *
            threeFiberSum f j := by
  classical
  unfold WeightedGraph.walk
  rw [threeFiberGraph_degree a n ha hd hn i x]
  rw [Fintype.sum_sigma]
  let S : Fin 3 → ℝ := fun j ↦
    ∑ y : Fin (n j),
      threeFiberWeight a n ⟨i, x⟩ ⟨j, y⟩ * f ⟨j, y⟩
  have hsplit : (∑ j : Fin 3, S j) =
      S i + ∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)), S j := by
    have h := Finset.sum_erase_add
      (Finset.univ : Finset (Fin 3)) S (Finset.mem_univ i)
    rw [← h]
    ac_rfl
  change (∑ j : Fin 3, S j) /
      ((d : ℝ) * (a i : ℝ) / (n i : ℝ)) = _
  rw [hsplit]
  have hsame : S i =
      ((a i : ℝ) * (a i + 1 : ℕ) /
        ((n i : ℝ) * (n i - 1 : ℕ))) *
          (threeFiberSum f i - f ⟨i, x⟩) :=
    threeFiber_weighted_sum_same a n i x f
  rw [hsame]
  have hcross :
      (∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)), S j) =
        ∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)),
          ((a i : ℝ) * (a j : ℝ) /
            ((n i : ℝ) * (n j : ℝ))) * threeFiberSum f j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact threeFiber_weighted_sum_cross a n
      (Finset.ne_of_mem_erase hj).symm x f
  rw [hcross]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have haipos : (0 : ℝ) < a i := by exact_mod_cast hapos i
  have hnipos : (0 : ℝ) < n i := by
    have hni := hn i
    exact_mod_cast (by omega : 0 < n i)
  have hnisubpos : (0 : ℝ) < (n i - 1 : ℕ) := by
    have hni := hn i
    exact_mod_cast (by omega : 0 < n i - 1)
  rw [add_div]
  congr 1
  · field_simp
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have hnjpos : (0 : ℝ) < n j := by
      have hnj := hn j
      exact_mod_cast (by omega : 0 < n j)
    field_simp

/-- The within-fiber, zero-sum part of a function. -/
noncomputable def threeFiberCentered {n : Fin 3 → ℕ}
    (f : ThreeFiberVertex n → ℝ) (i : Fin 3) (x : Fin (n i)) : ℝ :=
  f ⟨i, x⟩ - threeFiberAverage f i

theorem sum_threeFiberCentered {n : Fin 3 → ℕ}
    (hn : ∀ i, 1 ≤ n i) (f : ThreeFiberVertex n → ℝ) (i : Fin 3) :
    ∑ x : Fin (n i), threeFiberCentered f i x = 0 := by
  unfold threeFiberCentered threeFiberAverage threeFiberSum
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hnpos : (0 : ℝ) < n i := by exact_mod_cast hn i
  field_simp
  ring

/-- Orthogonal Pythagorean identity on one fiber. -/
theorem sum_sq_eq_average_add_centered {n : Fin 3 → ℕ}
    (hn : ∀ i, 1 ≤ n i) (f : ThreeFiberVertex n → ℝ) (i : Fin 3) :
    (∑ x : Fin (n i), (f ⟨i, x⟩) ^ 2) =
      (n i : ℝ) * (threeFiberAverage f i) ^ 2 +
        ∑ x : Fin (n i), (threeFiberCentered f i x) ^ 2 := by
  have hcenter := sum_threeFiberCentered hn f i
  have hpoint (x : Fin (n i)) :
      f ⟨i, x⟩ = threeFiberAverage f i + threeFiberCentered f i x := by
    simp [threeFiberCentered]
  simp_rw [hpoint, add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, hcenter, mul_zero, add_zero]

/-- The stationary weighted mean is `d` times the occupancy-weighted sum of
the three fiber averages. -/
theorem threeFiberGraph_weightedMean (a n : Fin 3 → ℕ) {d : ℕ}
    (ha : ∑ i, a i = d - 1) (hd : 1 ≤ d)
    (hn : ∀ i, 2 ≤ n i) (f : ThreeFiberVertex n → ℝ) :
    (threeFiberGraph a n).weightedMean f =
      (d : ℝ) * ∑ i : Fin 3, (a i : ℝ) * threeFiberAverage f i := by
  classical
  unfold WeightedGraph.weightedMean
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp_rw [threeFiberGraph_degree a n ha hd hn]
  rw [← Finset.mul_sum]
  unfold threeFiberAverage threeFiberSum
  have hnpos : (0 : ℝ) < n i := by
    have hni := hn i
    exact_mod_cast (by omega : 0 < n i)
  field_simp

/-- The stationary squared norm as a sum of the three fiber energies. -/
theorem threeFiberGraph_sqNorm (a n : Fin 3 → ℕ) {d : ℕ}
    (ha : ∑ i, a i = d - 1) (hd : 1 ≤ d)
    (hn : ∀ i, 2 ≤ n i) (f : ThreeFiberVertex n → ℝ) :
    (threeFiberGraph a n).sqNorm f =
      ∑ i : Fin 3, ((d : ℝ) * (a i : ℝ) / (n i : ℝ)) *
        ∑ x : Fin (n i), (f ⟨i, x⟩) ^ 2 := by
  classical
  unfold WeightedGraph.sqNorm
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _hi
  simp_rw [threeFiberGraph_degree a n ha hd hn]
  rw [← Finset.mul_sum]

/-- A mean-zero function has occupancy-weighted fiber averages summing to
zero. -/
theorem threeFiber_average_relation (a n : Fin 3 → ℕ) {d : ℕ}
    (ha : ∑ i, a i = d - 1) (hd : 1 ≤ d)
    (hn : ∀ i, 2 ≤ n i) (f : ThreeFiberVertex n → ℝ)
    (hmean : (threeFiberGraph a n).weightedMean f = 0) :
    ∑ i : Fin 3, (a i : ℝ) * threeFiberAverage f i = 0 := by
  rw [threeFiberGraph_weightedMean a n ha hd hn f] at hmean
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  exact (mul_eq_zero.mp hmean).resolve_left hdpos.ne'

/-- On the mean-zero space the quotient component has eigenvalue `1/d`,
while the centered part in fiber `i` has eigenvalue
`-(a i + 1)/(d(n i - 1))`.  This is the complete pointwise block
decomposition claimed in the first row of the table on page 15. -/
theorem threeFiberGraph_walk_of_meanZero (a n : Fin 3 → ℕ) {d : ℕ}
    (ha : ∑ i, a i = d - 1) (hd : 1 ≤ d)
    (hapos : ∀ i, 1 ≤ a i) (hn : ∀ i, 2 ≤ n i)
    (f : ThreeFiberVertex n → ℝ)
    (hmean : (threeFiberGraph a n).weightedMean f = 0)
    (i : Fin 3) (x : Fin (n i)) :
    (threeFiberGraph a n).walk f ⟨i, x⟩ =
      threeFiberAverage f i / (d : ℝ) -
        ((a i + 1 : ℕ) /
          ((d : ℝ) * (n i - 1 : ℕ))) * threeFiberCentered f i x := by
  classical
  rw [threeFiberGraph_walk a n ha hd hapos hn]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hni := hn i
  have hnipos : (0 : ℝ) < n i := by
    exact_mod_cast (by omega : 0 < n i)
  have hnisubpos : (0 : ℝ) < (n i - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < n i - 1)
  have hsum_i :
      threeFiberSum f i = (n i : ℝ) * threeFiberAverage f i := by
    unfold threeFiberAverage
    field_simp
  rw [hsum_i]
  have hcross :
      (∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)),
          (a j : ℝ) / ((d : ℝ) * (n j : ℝ)) * threeFiberSum f j) =
        (1 / (d : ℝ)) *
          ∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)),
            (a j : ℝ) * threeFiberAverage f j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    have hnj := hn j
    have hnjpos : (0 : ℝ) < n j := by
      exact_mod_cast (by omega : 0 < n j)
    unfold threeFiberAverage
    field_simp
  rw [hcross]
  have hrelation := threeFiber_average_relation a n ha hd hn f hmean
  have hsplit :
      (∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)),
          (a j : ℝ) * threeFiberAverage f j) =
        -((a i : ℝ) * threeFiberAverage f i) := by
    have hsumErase := Finset.sum_erase_add
      (Finset.univ : Finset (Fin 3))
      (fun j ↦ (a j : ℝ) * threeFiberAverage f j)
      (Finset.mem_univ i)
    rw [hrelation] at hsumErase
    linarith
  rw [hsplit]
  unfold threeFiberCentered
  have hcastn : ((n i - 1 : ℕ) : ℝ) = (n i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n i)]
    norm_num
  rw [hcastn]
  push_cast
  have hnreal : (2 : ℝ) ≤ n i := by exact_mod_cast hn i
  have hsubne : (n i : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hsubne, hdpos.ne']
  ring

/-- In the three-positive-occupancy case each occupancy is at most `d-3`:
the two other fibers each contain at least one conditioned vertex. -/
theorem threeFiber_occupancy_le {a : Fin 3 → ℕ} {d : ℕ}
    (ha : ∑ i, a i = d - 1) (hd : 1 ≤ d)
    (hapos : ∀ i, 1 ≤ a i) (i : Fin 3) :
    a i ≤ d - 3 := by
  have herase := sum_fin_three_erase ha hd i
  have hlower :
      2 ≤ ∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)), a j := by
    calc
      2 = (Finset.univ.erase i : Finset (Fin 3)).card := by simp
      _ = ∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)), 1 := by simp
      _ ≤ ∑ j ∈ (Finset.univ.erase i : Finset (Fin 3)), a j := by
        apply Finset.sum_le_sum
        intro j _hj
        exact hapos j
  omega

/-- Magnitude bound for every within-fiber block eigenvalue in the first row
of the page-15 table. -/
theorem threeFiber_within_eigenvalue_bound
    {a n : Fin 3 → ℕ} {d m : ℕ}
    (ha : ∑ i, a i = d - 1) (hd : 3 ≤ d)
    (hapos : ∀ i, 1 ≤ a i) (hm : 2 * d ≤ m)
    (hcapacity : ∀ i, a i + n i = m) (i : Fin 3) :
    |(-(a i + 1 : ℕ) : ℝ) /
        ((d : ℝ) * (n i - 1 : ℕ))| ≤ 1 / (d : ℝ) := by
  have hbound := lift_three_fiber_within_bound
    (d := (d : ℝ)) (m := (m : ℝ)) (a := (a i : ℝ))
    (by exact_mod_cast hd) (by exact_mod_cast hm)
    (by positivity) (by exact_mod_cast threeFiber_occupancy_le ha (by omega) hapos i)
  have hni : n i - 1 = m - a i - 1 := by
    have hc := hcapacity i
    omega
  rw [hni]
  have haiM : a i ≤ m := by
    have hc := hcapacity i
    omega
  have hone : 1 ≤ m - a i := by
    have hc := hcapacity i
    have hother := threeFiber_occupancy_le ha (by omega) hapos i
    omega
  have hcast : ((m - a i - 1 : ℕ) : ℝ) =
      (m : ℝ) - (a i : ℝ) - 1 := by
    rw [Nat.cast_sub hone, Nat.cast_sub haiM]
    norm_num
  rw [hcast]
  simpa only [Nat.cast_add, Nat.cast_one] using hbound

/-- Exact orthogonal energy decomposition after one walk step.  Together
with `sum_sq_eq_average_add_centered`, this also proves that the quotient and
all three within-fiber blocks span the whole function space. -/
theorem threeFiber_sum_sq_walk (a n : Fin 3 → ℕ) {d : ℕ}
    (ha : ∑ i, a i = d - 1) (hd : 1 ≤ d)
    (hapos : ∀ i, 1 ≤ a i) (hn : ∀ i, 2 ≤ n i)
    (f : ThreeFiberVertex n → ℝ)
    (hmean : (threeFiberGraph a n).weightedMean f = 0)
    (i : Fin 3) :
    (∑ x : Fin (n i),
        ((threeFiberGraph a n).walk f ⟨i, x⟩) ^ 2) =
      (n i : ℝ) * (threeFiberAverage f i / (d : ℝ)) ^ 2 +
        (((a i + 1 : ℕ) : ℝ) /
          ((d : ℝ) * (n i - 1 : ℕ))) ^ 2 *
          ∑ x : Fin (n i), (threeFiberCentered f i x) ^ 2 := by
  let mu : ℝ := threeFiberAverage f i
  let beta : ℝ := ((a i + 1 : ℕ) : ℝ) /
    ((d : ℝ) * (n i - 1 : ℕ))
  have hwalk (x : Fin (n i)) :
      (threeFiberGraph a n).walk f ⟨i, x⟩ =
        mu / (d : ℝ) - beta * threeFiberCentered f i x := by
    exact threeFiberGraph_walk_of_meanZero a n ha hd hapos hn f hmean i x
  simp_rw [hwalk]
  have hcenter := sum_threeFiberCentered
    (fun j ↦ (hn j).trans' (by omega)) f i
  calc
    (∑ x : Fin (n i),
        (mu / (d : ℝ) - beta * threeFiberCentered f i x) ^ 2) =
        ∑ x : Fin (n i),
          ((mu / (d : ℝ)) ^ 2 -
            (2 * (mu / (d : ℝ)) * beta) * threeFiberCentered f i x +
            beta ^ 2 * (threeFiberCentered f i x) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = (n i : ℝ) * (mu / (d : ℝ)) ^ 2 +
        beta ^ 2 * ∑ x : Fin (n i), (threeFiberCentered f i x) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, hcenter, mul_zero, sub_zero]
    _ = (n i : ℝ) * (threeFiberAverage f i / (d : ℝ)) ^ 2 +
        (((a i + 1 : ℕ) : ℝ) /
          ((d : ℝ) * (n i - 1 : ℕ))) ^ 2 *
          ∑ x : Fin (n i), (threeFiberCentered f i x) ^ 2 := rfl

/-- Fiber-by-fiber `1/d` energy contraction. -/
theorem threeFiber_fiber_energy_bound
    {a n : Fin 3 → ℕ} {d m : ℕ}
    (ha : ∑ i, a i = d - 1) (hd : 3 ≤ d)
    (hapos : ∀ i, 1 ≤ a i) (hm : 2 * d ≤ m)
    (hcapacity : ∀ i, a i + n i = m)
    (f : ThreeFiberVertex n → ℝ)
    (hmean : (threeFiberGraph a n).weightedMean f = 0)
    (i : Fin 3) :
    (∑ x : Fin (n i),
        ((threeFiberGraph a n).walk f ⟨i, x⟩) ^ 2) ≤
      (1 / (d : ℝ)) ^ 2 *
        ∑ x : Fin (n i), (f ⟨i, x⟩) ^ 2 := by
  have hn : ∀ j, 2 ≤ n j := by
    intro j
    have hc := hcapacity j
    have haj := threeFiber_occupancy_le ha (by omega) hapos j
    omega
  rw [threeFiber_sum_sq_walk a n ha (by omega) hapos hn f hmean i]
  rw [sum_sq_eq_average_add_centered
    (fun j ↦ (hn j).trans' (by omega)) f i]
  let beta : ℝ := ((a i + 1 : ℕ) : ℝ) /
    ((d : ℝ) * (n i - 1 : ℕ))
  let centeredEnergy : ℝ :=
    ∑ x : Fin (n i), (threeFiberCentered f i x) ^ 2
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by omega) hd)
  have htarget : 0 ≤ 1 / (d : ℝ) := (one_div_pos.mpr hdpos).le
  have habsNeg := threeFiber_within_eigenvalue_bound
    ha hd hapos hm hcapacity i
  have habsBeta : |beta| ≤ 1 / (d : ℝ) := by
    have hneg : |-beta| ≤ 1 / (d : ℝ) := by
      simpa only [beta, neg_div] using habsNeg
    simpa only [abs_neg] using hneg
  have hbetaSq : beta ^ 2 ≤ (1 / (d : ℝ)) ^ 2 := by
    calc
      beta ^ 2 = |beta| ^ 2 := (sq_abs beta).symm
      _ ≤ (1 / (d : ℝ)) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg beta) htarget).2 habsBeta
  have hcenteredNonneg : 0 ≤ centeredEnergy := by
    dsimp [centeredEnergy]
    exact Finset.sum_nonneg fun x _hx ↦ sq_nonneg _
  have hwithin : beta ^ 2 * centeredEnergy ≤
      (1 / (d : ℝ)) ^ 2 * centeredEnergy :=
    mul_le_mul_of_nonneg_right hbetaSq hcenteredNonneg
  change
    (n i : ℝ) * (threeFiberAverage f i / (d : ℝ)) ^ 2 +
        beta ^ 2 * centeredEnergy ≤
      (1 / (d : ℝ)) ^ 2 *
        ((n i : ℝ) * (threeFiberAverage f i) ^ 2 + centeredEnergy)
  calc
    (n i : ℝ) * (threeFiberAverage f i / (d : ℝ)) ^ 2 +
        beta ^ 2 * centeredEnergy ≤
      (n i : ℝ) * (threeFiberAverage f i / (d : ℝ)) ^ 2 +
        (1 / (d : ℝ)) ^ 2 * centeredEnergy :=
          add_le_add (le_refl _) hwithin
    _ = (1 / (d : ℝ)) ^ 2 *
        ((n i : ℝ) * (threeFiberAverage f i) ^ 2 + centeredEnergy) := by
      field_simp

/-- Complete two-sided spectral estimate for the canonical all-three-fibers
conditioned link.  No eigenvalue-completeness assumption is used: the proof
applies the exact orthogonal decomposition to an arbitrary mean-zero
function. -/
theorem threeFiberGraph_twoSidedSpectralBound
    {a n : Fin 3 → ℕ} {d m : ℕ}
    (ha : ∑ i, a i = d - 1) (hd : 3 ≤ d)
    (hapos : ∀ i, 1 ≤ a i) (hm : 2 * d ≤ m)
    (hcapacity : ∀ i, a i + n i = m) :
    (threeFiberGraph a n).TwoSidedSpectralBound (1 / (d : ℝ)) := by
  have hn : ∀ j, 2 ≤ n j := by
    intro j
    have hc := hcapacity j
    have haj := threeFiber_occupancy_le ha (by omega) hapos j
    omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by omega) hd)
  refine ⟨(one_div_pos.mpr hdpos).le, ?_⟩
  intro f hmean
  rw [threeFiberGraph_sqNorm a n ha (by omega) hn]
  rw [threeFiberGraph_sqNorm a n ha (by omega) hn]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _hi
  have hpart := threeFiber_fiber_energy_bound
    ha hd hapos hm hcapacity f hmean i
  have hcoefficient :
      0 ≤ (d : ℝ) * (a i : ℝ) / (n i : ℝ) := by positivity
  calc
    ((d : ℝ) * (a i : ℝ) / (n i : ℝ)) *
        ∑ x : Fin (n i), ((threeFiberGraph a n).walk f ⟨i, x⟩) ^ 2 ≤
      ((d : ℝ) * (a i : ℝ) / (n i : ℝ)) *
        ((1 / (d : ℝ)) ^ 2 *
          ∑ x : Fin (n i), (f ⟨i, x⟩) ^ 2) :=
            mul_le_mul_of_nonneg_left hpart hcoefficient
    _ = (1 / (d : ℝ)) ^ 2 *
        (((d : ℝ) * (a i : ℝ) / (n i : ℝ)) *
          ∑ x : Fin (n i), (f ⟨i, x⟩) ^ 2) := by ring

/-- A compact bridge interface for a concrete conditioned link.  To use the
calculation above, it is enough to enumerate the three sets of unused labels
and verify the exact edge-weight formula up to one common positive factor.
The latter factor accounts for the base-triangle mass, the three old `g`
factors, and the global normalizer. -/
structure ThreeFiberLinkCertificate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (d m : ℕ) where
  occupancy : Fin 3 → ℕ
  unused : Fin 3 → ℕ
  occupancy_sum : ∑ i, occupancy i = d - 1
  dimension_ge_three : 3 ≤ d
  occupancy_pos : ∀ i, 1 ≤ occupancy i
  fiber_capacity : ∀ i, occupancy i + unused i = m
  fiber_size : 2 * d ≤ m
  enumerate : V ≃ ThreeFiberVertex unused
  commonScale : ℝ
  commonScale_pos : 0 < commonScale
  relabel_eq :
    G = ((threeFiberGraph occupancy unused).scale commonScale commonScale_pos.le).relabel
      enumerate.symm

/-- Any concrete link satisfying the exact three-fiber edge certificate has
the required two-sided local spectral bound. -/
theorem ThreeFiberLinkCertificate.twoSidedSpectralBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {d m : ℕ}
    (certificate : ThreeFiberLinkCertificate G d m) :
    G.TwoSidedSpectralBound (1 / (d : ℝ)) := by
  have hmodel := threeFiberGraph_twoSidedSpectralBound
    certificate.occupancy_sum certificate.dimension_ge_three
    certificate.occupancy_pos certificate.fiber_size
    certificate.fiber_capacity
  have hscaled := WeightedGraph.twoSidedSpectralBound_scale
    (threeFiberGraph certificate.occupancy certificate.unused)
    certificate.commonScale certificate.commonScale_pos hmodel
  rw [certificate.relabel_eq]
  exact WeightedGraph.twoSidedSpectralBound_relabel _
    certificate.enumerate.symm hscaled


end WeightedLift

end HDXLean
