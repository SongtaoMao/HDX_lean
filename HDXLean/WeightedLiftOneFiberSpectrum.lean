import HDXLean.WeightedLiftSpectrum
import HDXLean.WeightedLiftLinks
import HDXLean.FiniteRegularSpectrum
import HDXLean.WeightedGraphScaling
import HDXLean.Relabeling
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The one-occupied-fiber link in the weighted dimension lift

This file formalizes the last row of the spectral table on page 15.  We first
give the reversible weighted graph whose normalized walk is the conditioned
walk when a codimension-two face is contained in one base fiber.  The model
allows a nonregular weighted base vertex-link: transitions out of the occupied
fiber use its stationary distribution.
-/

namespace HDXLean

open scoped BigOperators

namespace WeightedLift

universe u v w

/-- State space of a one-occupied-fiber link.  The left summand consists of
unused vertices in the occupied fiber; the right summand consists of a base
link vertex together with a fiber label. -/
abbrev OneFiberVertex (O : Type u) (B : Type v) (A : Type w) :=
  O ⊕ (B × A)

/-- Total weighted volume of a finite graph. -/
noncomputable def graphVolume {B : Type v} [Fintype B] [DecidableEq B]
    (G : WeightedGraph B) : ℝ :=
  ∑ b : B, G.degree b

/-- Stationary mean normalized to send the constant function to one. -/
noncomputable def stationaryAverage {B : Type v} [Fintype B] [DecidableEq B]
    (G : WeightedGraph B) (f : B → ℝ) : ℝ :=
  G.weightedMean f / graphVolume G

/-- Average of a function on a nonempty finite type. -/
noncomputable def uniformAverage {I : Type u} [Fintype I]
    (f : I → ℝ) : ℝ :=
  (∑ i : I, f i) / Fintype.card I

/-- Average over all points other than the current point. -/
noncomputable def excludeAverage {I : Type u} [Fintype I] [DecidableEq I]
    (f : I → ℝ) (i : I) : ℝ :=
  (∑ j ∈ (Finset.univ.erase i : Finset I), f j) /
    (Fintype.card I - 1 : ℝ)

/-- The reversible graph modelling a codimension-two lifted link whose
conditioned face occupies just one base fiber.  The harmless common scale is
chosen so that the right-fiber degree is `(d+1) * degree_G b`.

The cardinality hypotheses used to simplify its walk are stated by the
subsequent theorems rather than built into the definition. -/
noncomputable def oneFiberGraph
    {O : Type u} {B : Type v} {A : Type w}
    [Fintype O] [DecidableEq O]
    [Fintype B] [DecidableEq B]
    [Fintype A] [DecidableEq A]
    (d : ℕ) (hd : 1 ≤ d)
    (hO : 2 ≤ Fintype.card O) (hA : 2 ≤ Fintype.card A)
    (G : WeightedGraph B) :
    WeightedGraph (OneFiberVertex O B A) where
  weight p q :=
    match p, q with
    | Sum.inl i, Sum.inl j =>
        if i = j then 0 else
          (Fintype.card A : ℝ) * (d - 1 : ℝ) ^ 2 * graphVolume G /
            (2 * (Fintype.card O : ℝ) * (Fintype.card O - 1 : ℝ))
    | Sum.inl _, Sum.inr (b, _) =>
        (d - 1 : ℝ) * G.degree b / Fintype.card O
    | Sum.inr (b, _), Sum.inl _ =>
        (d - 1 : ℝ) * G.degree b / Fintype.card O
    | Sum.inr (b, a), Sum.inr (c, e) =>
        if b = c then
          if a = e then 0 else G.degree b / (Fintype.card A - 1 : ℝ)
        else G.weight b c / Fintype.card A
  weight_symm p q := by
    rcases p with i | ⟨b, a⟩ <;> rcases q with j | ⟨c, e⟩
    · by_cases h : i = j
      · subst j; simp
      · simp [h, Ne.symm h]
    · rfl
    · rfl
    · by_cases hbc : b = c
      · subst c
        by_cases hae : a = e
        · subst e; simp
        · simp [hae, Ne.symm hae]
      · simp [hbc, Ne.symm hbc, G.weight_symm]
  weight_self p := by
    rcases p with i | ⟨b, a⟩ <;> simp
  weight_nonneg p q := by
    have hdOne : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hdReal : (0 : ℝ) ≤ (d : ℝ) - 1 := by linarith
    have hOOne : (1 : ℝ) ≤ (Fintype.card O : ℝ) := by
      exact_mod_cast (show 1 ≤ Fintype.card O by omega)
    have hOReal : (0 : ℝ) ≤ (Fintype.card O : ℝ) - 1 := by
      linarith
    have hAOne : (1 : ℝ) ≤ (Fintype.card A : ℝ) := by
      exact_mod_cast (show 1 ≤ Fintype.card A by omega)
    have hAReal : (0 : ℝ) ≤ (Fintype.card A : ℝ) - 1 := by
      linarith
    have hvolume : 0 ≤ graphVolume G := by
      exact Finset.sum_nonneg fun b _ ↦ G.degree_nonneg b
    rcases p with i | ⟨b, a⟩ <;> rcases q with j | ⟨c, e⟩
    · dsimp
      split_ifs
      · exact le_rfl
      · apply div_nonneg
        · positivity
        · positivity
    · dsimp
      exact div_nonneg (mul_nonneg hdReal (G.degree_nonneg c)) (by positivity)
    · dsimp
      exact div_nonneg (mul_nonneg hdReal (G.degree_nonneg b)) (by positivity)
    · dsimp
      split_ifs
      · exact le_rfl
      · exact div_nonneg (G.degree_nonneg b) hAReal
      · exact div_nonneg (G.weight_nonneg b c) (by positivity)

/-- The model with the paper's cardinality assumptions.  The equation on
`O` says that it is exactly the set of unused labels after a face of size
`d-1` has been fixed in an `A`-fiber. -/
noncomputable def conditionedOneFiberGraph
    {O : Type u} {B : Type v} {A : Type w}
    [Fintype O] [DecidableEq O]
    [Fintype B] [DecidableEq B]
    [Fintype A] [DecidableEq A]
    (d : ℕ) (hd : 3 ≤ d) (hm : 2 * d ≤ Fintype.card A)
    (hOcard : Fintype.card O + d = Fintype.card A + 1)
    (G : WeightedGraph B) : WeightedGraph (OneFiberVertex O B A) :=
  oneFiberGraph d (by omega) (by omega) (by omega) G

section DegreeAndWalk

variable {O : Type u} {B : Type v} {A : Type w}
  [Fintype O] [DecidableEq O]
  [Fintype B] [DecidableEq B]
  [Fintype A] [DecidableEq A]

variable (d : ℕ) (hd : 3 ≤ d) (hm : 2 * d ≤ Fintype.card A)
  (hOcard : Fintype.card O + d = Fintype.card A + 1)
  (G : WeightedGraph B)

private theorem cardO_pos (hd : 3 ≤ d) (hm : 2 * d ≤ Fintype.card A)
    (hOcard : Fintype.card O + d = Fintype.card A + 1) :
    0 < Fintype.card O := by omega

private theorem cardO_sub_one_pos (hd : 3 ≤ d) (hm : 2 * d ≤ Fintype.card A)
    (hOcard : Fintype.card O + d = Fintype.card A + 1) :
    0 < Fintype.card O - 1 := by omega

private theorem cardA_pos (hd : 3 ≤ d) (hm : 2 * d ≤ Fintype.card A) :
    0 < Fintype.card A := by omega

private theorem cardA_sub_one_pos (hd : 3 ≤ d) (hm : 2 * d ≤ Fintype.card A) :
    0 < Fintype.card A - 1 := by omega

/-- Degree of a vertex in the occupied fiber. -/
theorem conditionedOneFiberGraph_degree_occupied (i : O) :
    (conditionedOneFiberGraph d hd hm hOcard G).degree (Sum.inl i) =
      (d + 1 : ℝ) * (Fintype.card A : ℝ) * (d - 1 : ℝ) *
        graphVolume G / (2 * (Fintype.card O : ℝ)) := by
  classical
  unfold WeightedGraph.degree
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [conditionedOneFiberGraph, oneFiberGraph]
  have hO0 : (Fintype.card O : ℝ) ≠ 0 := by
    exact_mod_cast (cardO_pos (A := A) d hd hm hOcard).ne'
  have hO10 : (Fintype.card O : ℝ) - 1 ≠ 0 := by
    have : (0 : ℝ) < (Fintype.card O : ℝ) - 1 := by
      have htwo : 2 ≤ Fintype.card O := by omega
      have htwoReal : (2 : ℝ) ≤ Fintype.card O := by exact_mod_cast htwo
      linarith
    exact this.ne'
  have hAcast : (Fintype.card A : ℝ) = Fintype.card O + d - 1 := by
    have hNat : Fintype.card A = Fintype.card O + d - 1 := by omega
    rw [show (Fintype.card O : ℝ) + d - 1 =
        ((Fintype.card O + d - 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card O + d)]
      norm_num]
    exact_mod_cast hNat
  rw [Finset.sum_ite]
  have hfilter : (Finset.univ.filter fun x : O ↦ ¬ i = x) =
      Finset.univ.erase i := by
    ext x
    simp [eq_comm]
  rw [hfilter]
  simp only [Finset.sum_const_zero, Finset.card_erase_of_mem,
    Finset.mem_univ, Finset.card_univ,
    Nat.cast_sub (by omega : 1 ≤ Fintype.card O), Nat.cast_one,
    nsmul_eq_mul, zero_add]
  simp_rw [Finset.sum_const, nsmul_eq_mul]
  simp only [Finset.card_univ]
  have hErase : ((Finset.univ.erase i).card : ℝ) =
      (Fintype.card O : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Nat.cast_sub (by omega : 1 ≤ Fintype.card O)]
    norm_num
  rw [hErase]
  have hdegreeSum :
      (∑ b : B, (d - 1 : ℝ) * G.degree b / Fintype.card O) =
        (d - 1 : ℝ) / Fintype.card O *
          ∑ b : B, G.degree b := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  rw [← Finset.mul_sum, hdegreeSum]
  simp only [graphVolume]
  field_simp
  rw [hAcast]
  ring

/-- Degree of a vertex in any of the other fibers. -/
theorem conditionedOneFiberGraph_degree_other (b : B) (a : A) :
    (conditionedOneFiberGraph d hd hm hOcard G).degree
        (Sum.inr (b, a)) =
      (d + 1 : ℝ) * G.degree b := by
  classical
  unfold WeightedGraph.degree
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [conditionedOneFiberGraph, oneFiberGraph]
  have hO0 : (Fintype.card O : ℝ) ≠ 0 := by
    exact_mod_cast (cardO_pos (A := A) d hd hm hOcard).ne'
  have hA0 : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (cardA_pos (d := d) hd hm).ne'
  have hA10 : (Fintype.card A : ℝ) - 1 ≠ 0 := by
    have htwo : 2 ≤ Fintype.card A := by omega
    have htwoReal : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast htwo
    linarith
  have hleft :
      (∑ _i : O, (d - 1 : ℝ) * G.degree b / Fintype.card O) =
        (d - 1 : ℝ) * G.degree b := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hinner (c : B) :
      (∑ e : A, if b = c then
          if a = e then 0 else G.degree b / (Fintype.card A - 1 : ℝ)
        else G.weight b c / Fintype.card A) =
        if b = c then G.degree b else G.weight b c := by
    by_cases hbc : b = c
    · subst c
      simp only [if_pos]
      rw [Finset.sum_ite]
      have hfilter : (Finset.univ.filter fun e : A ↦ ¬ a = e) =
          Finset.univ.erase a := by
        ext e
        simp [eq_comm]
      rw [hfilter]
      simp only [Finset.sum_const_zero, zero_add, Finset.sum_const,
        nsmul_eq_mul, if_pos]
      have hErase : ((Finset.univ.erase a).card : ℝ) =
          (Fintype.card A : ℝ) - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
          Nat.cast_sub (by omega : 1 ≤ Fintype.card A)]
        norm_num
      rw [hErase]
      field_simp
    · simp only [if_neg hbc]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
  have hright :
      (∑ c : B, ∑ e : A, if b = c then
          if a = e then 0 else G.degree b / (Fintype.card A - 1 : ℝ)
        else G.weight b c / Fintype.card A) =
        2 * G.degree b := by
    simp_rw [hinner]
    have hpoint (c : B) :
        (if b = c then G.degree b else G.weight b c) =
          (if b = c then G.degree b else 0) + G.weight b c := by
      by_cases hbc : b = c
      · subst c
        simp [G.weight_self]
      · simp [hbc]
    simp_rw [hpoint, Finset.sum_add_distrib]
    rw [Fintype.sum_ite_eq]
    simp only [WeightedGraph.degree]
    ring
  rw [hleft, hright]
  rw [WeightedGraph.degree]
  ring

/-- Mean of a function over one unoccupied fiber. -/
noncomputable def otherFiberAverage
    (f : OneFiberVertex O B A → ℝ) (b : B) : ℝ :=
  uniformAverage fun a : A ↦ f (Sum.inr (b, a))

/-- Stationary average of the unoccupied-fiber averages. -/
noncomputable def allOtherAverage
    (G : WeightedGraph B) (f : OneFiberVertex O B A → ℝ) : ℝ :=
  stationaryAverage G (otherFiberAverage f)

omit [DecidableEq O] [DecidableEq A] in
/-- Positive vertex degrees imply positive total graph volume. -/
theorem graphVolume_pos [Nonempty B] (hdegree : ∀ b, 0 < G.degree b) :
    0 < graphVolume G := by
  classical
  let b₀ : B := Classical.choice inferInstance
  unfold graphVolume
  apply Finset.sum_pos'
  · intro b _hb
    exact (hdegree b).le
  · exact ⟨b₀, Finset.mem_univ _, hdegree b₀⟩

/-- The exact first row of the conditioned operator: from an unused vertex in
the occupied fiber, the walk stays in that fiber with mass `(d-1)/(d+1)`
and otherwise samples the stationary base-link distribution and a uniform
fiber label. -/
theorem conditionedOneFiberGraph_walk_occupied [Nonempty B]
    (hdegree : ∀ b, 0 < G.degree b)
    (f : OneFiberVertex O B A → ℝ) (i : O) :
    (conditionedOneFiberGraph d hd hm hOcard G).walk f (Sum.inl i) =
      (d - 1 : ℝ) / (d + 1 : ℝ) *
          excludeAverage (fun j : O ↦ f (Sum.inl j)) i +
        2 / (d + 1 : ℝ) * allOtherAverage G f := by
  classical
  let H := conditionedOneFiberGraph d hd hm hOcard G
  have hO0 : (Fintype.card O : ℝ) ≠ 0 := by
    exact_mod_cast (cardO_pos (A := A) d hd hm hOcard).ne'
  have hO10 : (Fintype.card O : ℝ) - 1 ≠ 0 := by
    have htwo : 2 ≤ Fintype.card O := by omega
    have htwoReal : (2 : ℝ) ≤ Fintype.card O := by exact_mod_cast htwo
    linarith
  have hA0 : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (cardA_pos (d := d) hd hm).ne'
  have hd1 : (d + 1 : ℝ) ≠ 0 := by positivity
  have hdMinus : (d - 1 : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hvol0 : graphVolume G ≠ 0 :=
    (graphVolume_pos (G := G) hdegree).ne'
  have hdegH : H.degree (Sum.inl i) =
      (d + 1 : ℝ) * (Fintype.card A : ℝ) * (d - 1 : ℝ) *
        graphVolume G / (2 * (Fintype.card O : ℝ)) :=
    conditionedOneFiberGraph_degree_occupied d hd hm hOcard G i
  unfold WeightedGraph.walk
  rw [hdegH]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [H, conditionedOneFiberGraph, oneFiberGraph]
  have hleft :
      (∑ j : O, (if i = j then 0 else
        (Fintype.card A : ℝ) * (d - 1 : ℝ) ^ 2 * graphVolume G /
          (2 * (Fintype.card O : ℝ) * (Fintype.card O - 1 : ℝ))) *
          f (Sum.inl j)) =
        ((Fintype.card A : ℝ) * (d - 1 : ℝ) ^ 2 * graphVolume G /
          (2 * (Fintype.card O : ℝ) * (Fintype.card O - 1 : ℝ))) *
          ∑ j ∈ (Finset.univ.erase i : Finset O), f (Sum.inl j) := by
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite]
    have hfilter : (Finset.univ.filter fun j : O ↦ ¬ i = j) =
        Finset.univ.erase i := by
      ext j
      simp [eq_comm]
    rw [hfilter]
    simp only [Finset.sum_const_zero, zero_add, Finset.mul_sum]
  rw [hleft]
  have hright :
      (∑ b : B, ∑ a : A,
        ((d - 1 : ℝ) * G.degree b / Fintype.card O) *
          f (Sum.inr (b, a))) =
        (d - 1 : ℝ) * (Fintype.card A : ℝ) /
            Fintype.card O *
          G.weightedMean (otherFiberAverage f) := by
    unfold WeightedGraph.weightedMean otherFiberAverage uniformAverage
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _hb
    rw [← Finset.mul_sum]
    field_simp
  rw [hright]
  unfold excludeAverage allOtherAverage stationaryAverage
  field_simp

/-- The exact row in every other fiber.  Its three summands have masses
`(d-1)/(d+1)`, `1/(d+1)`, and `1/(d+1)` respectively; the last summand is
the base vertex-link walk applied to fiber averages. -/
theorem conditionedOneFiberGraph_walk_other [Nonempty B]
    (hdegree : ∀ b, 0 < G.degree b)
    (f : OneFiberVertex O B A → ℝ) (b : B) (a : A) :
    (conditionedOneFiberGraph d hd hm hOcard G).walk f
        (Sum.inr (b, a)) =
      (d - 1 : ℝ) / (d + 1 : ℝ) *
          uniformAverage (fun i : O ↦ f (Sum.inl i)) +
        1 / (d + 1 : ℝ) *
          excludeAverage (fun e : A ↦ f (Sum.inr (b, e))) a +
        1 / (d + 1 : ℝ) * G.walk (otherFiberAverage f) b := by
  classical
  let H := conditionedOneFiberGraph d hd hm hOcard G
  have hO0 : (Fintype.card O : ℝ) ≠ 0 := by
    exact_mod_cast (cardO_pos (A := A) d hd hm hOcard).ne'
  have hA0 : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (cardA_pos (d := d) hd hm).ne'
  have hA10 : (Fintype.card A : ℝ) - 1 ≠ 0 := by
    have htwo : 2 ≤ Fintype.card A := by omega
    have htwoReal : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast htwo
    linarith
  have hd1 : (d + 1 : ℝ) ≠ 0 := by positivity
  have hdeg0 : G.degree b ≠ 0 := (hdegree b).ne'
  have hdegH : H.degree (Sum.inr (b, a)) =
      (d + 1 : ℝ) * G.degree b :=
    conditionedOneFiberGraph_degree_other d hd hm hOcard G b a
  unfold WeightedGraph.walk
  rw [hdegH]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [H, conditionedOneFiberGraph, oneFiberGraph]
  have hleft :
      (∑ i : O, ((d - 1 : ℝ) * G.degree b / Fintype.card O) *
          f (Sum.inl i)) =
        (d - 1 : ℝ) * G.degree b *
          uniformAverage (fun i : O ↦ f (Sum.inl i)) := by
    unfold uniformAverage
    rw [← Finset.mul_sum]
    field_simp
  rw [hleft]
  have hsame :
      (∑ e : A, (if a = e then 0 else
          G.degree b / (Fintype.card A - 1 : ℝ)) *
          f (Sum.inr (b, e))) =
        G.degree b *
          excludeAverage (fun e : A ↦ f (Sum.inr (b, e))) a := by
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite]
    have hfilter : (Finset.univ.filter fun e : A ↦ ¬ a = e) =
        Finset.univ.erase a := by
      ext e
      simp [eq_comm]
    rw [hfilter]
    simp only [Finset.sum_const_zero, zero_add]
    unfold excludeAverage
    rw [← Finset.mul_sum]
    field_simp
  have hdiff (c : B) (hbc : b ≠ c) :
      (∑ e : A, (G.weight b c / Fintype.card A) *
          f (Sum.inr (c, e))) =
        G.weight b c * otherFiberAverage f c := by
    unfold otherFiberAverage uniformAverage
    rw [← Finset.mul_sum]
    field_simp
  have hright :
      (∑ c : B, ∑ e : A,
        (if b = c then
          if a = e then 0 else G.degree b / (Fintype.card A - 1 : ℝ)
        else G.weight b c / Fintype.card A) * f (Sum.inr (c, e))) =
        G.degree b *
          (excludeAverage (fun e : A ↦ f (Sum.inr (b, e))) a +
            G.walk (otherFiberAverage f) b) := by
    have hinner (c : B) :
        (∑ e : A,
          (if b = c then
            if a = e then 0 else G.degree b / (Fintype.card A - 1 : ℝ)
          else G.weight b c / Fintype.card A) * f (Sum.inr (c, e))) =
          if b = c then
            G.degree b *
              excludeAverage (fun e : A ↦ f (Sum.inr (b, e))) a
          else G.weight b c * otherFiberAverage f c := by
      by_cases hbc : b = c
      · subst c
        simp only [if_pos]
        exact hsame
      · simp only [if_neg hbc]
        exact hdiff c hbc
    simp_rw [hinner]
    have hpoint (c : B) :
        (if b = c then
            G.degree b *
              excludeAverage (fun e : A ↦ f (Sum.inr (b, e))) a
          else G.weight b c * otherFiberAverage f c) =
          (if b = c then
              G.degree b *
                excludeAverage (fun e : A ↦ f (Sum.inr (b, e))) a
            else 0) + G.weight b c * otherFiberAverage f c := by
      by_cases hbc : b = c
      · subst c
        simp [G.weight_self]
      · simp [hbc]
    simp_rw [hpoint, Finset.sum_add_distrib]
    rw [Fintype.sum_ite_eq]
    unfold WeightedGraph.walk
    field_simp
  rw [hright]
  unfold uniformAverage excludeAverage WeightedGraph.walk
  field_simp
  ring

/-! ## Complete invariant-subspace decomposition -/

/-- Mean on the occupied fiber. -/
noncomputable def occupiedAverage
    (f : OneFiberVertex O B A → ℝ) : ℝ :=
  uniformAverage fun i : O ↦ f (Sum.inl i)

/-- Zero-sum part inside the occupied fiber. -/
noncomputable def occupiedFluctuation
    (f : OneFiberVertex O B A → ℝ) (i : O) : ℝ :=
  f (Sum.inl i) - occupiedAverage f

/-- Zero-sum part inside an unoccupied fiber. -/
noncomputable def otherFluctuation
    (f : OneFiberVertex O B A → ℝ) (b : B) (a : A) : ℝ :=
  f (Sum.inr (b, a)) - otherFiberAverage f b

/-- Mean-zero base-link part of the unoccupied-fiber averages. -/
noncomputable def baseFluctuation
    (G : WeightedGraph B) (f : OneFiberVertex O B A → ℝ) (b : B) : ℝ :=
  otherFiberAverage f b - allOtherAverage G f

/-- The common quotient-coordinate produced by one application of the walk. -/
noncomputable def oneFiberQuotientValue
    (d : ℕ) (G : WeightedGraph B)
    (f : OneFiberVertex O B A → ℝ) : ℝ :=
  (d - 1 : ℝ) / (d + 1 : ℝ) * occupiedAverage f +
    2 / (d + 1 : ℝ) * allOtherAverage G f

/-- The occupied-fiber zero-sum eigenvalue in (5.4). -/
noncomputable def occupiedWithinEigenvalue (d m : ℕ) : ℝ :=
  -((d : ℝ) - 1) / (((d : ℝ) + 1) * ((m : ℝ) - d))

/-- The other-fiber zero-sum eigenvalue in (5.4). -/
noncomputable def otherWithinEigenvalue (d m : ℕ) : ℝ :=
  -1 / (((d : ℝ) + 1) * ((m : ℝ) - 1))

omit [DecidableEq O] [DecidableEq B] [DecidableEq A] in
theorem uniformAverage_const {I : Type u} [Fintype I]
    (hI : 0 < Fintype.card I) (c : ℝ) :
    uniformAverage (fun _ : I ↦ c) = c := by
  unfold uniformAverage
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hI0 : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
  field_simp

/-- Stationarity of the degree measure. -/
theorem weightedMean_walk (hdegree : ∀ b, 0 < G.degree b) (f : B → ℝ) :
    G.weightedMean (G.walk f) = G.weightedMean f := by
  classical
  unfold WeightedGraph.weightedMean WeightedGraph.walk
  have hpoint (b : B) :
      G.degree b * ((∑ c : B, G.weight b c * f c) / G.degree b) =
        ∑ c : B, G.weight b c * f c := by
    field_simp [(hdegree b).ne']
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [← Finset.sum_mul]
  congr 1
  unfold WeightedGraph.degree
  apply Finset.sum_congr rfl
  intro b _hb
  rw [G.weight_symm]

omit [DecidableEq O] [DecidableEq A] in
/-- The normalized stationary average is fixed by the base walk. -/
theorem stationaryAverage_walk (hdegree : ∀ b, 0 < G.degree b) (f : B → ℝ) :
    stationaryAverage G (G.walk f) = stationaryAverage G f := by
  exact congrArg (fun x ↦ x / graphVolume G)
    (weightedMean_walk G hdegree f)

/-- The base fluctuation has stationary mean zero. -/
theorem weightedMean_baseFluctuation [Nonempty B]
    (hdegree : ∀ b, 0 < G.degree b)
    (f : OneFiberVertex O B A → ℝ) :
    G.weightedMean (baseFluctuation G f) = 0 := by
  classical
  unfold baseFluctuation allOtherAverage stationaryAverage
  unfold WeightedGraph.weightedMean
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp only [graphVolume]
  have hvol0 : (∑ b : B, G.degree b) ≠ 0 :=
    (graphVolume_pos (G := G) hdegree).ne'
  let S := ∑ b : B, G.degree b * otherFiberAverage f b
  have hsecond :
      (∑ b : B, G.degree b * (S / ∑ c : B, G.degree c)) = S := by
    rw [← Finset.sum_mul]
    field_simp
  change S - (∑ b : B, G.degree b * (S / ∑ c : B, G.degree c)) = 0
  rw [hsecond]
  ring

/-- Adding a constant commutes with the base random walk. -/
theorem walk_add_const (hdegree : ∀ b, 0 < G.degree b)
    (f : B → ℝ) (c : ℝ) (b : B) :
    G.walk (fun x ↦ f x + c) b = G.walk f b + c := by
  classical
  unfold WeightedGraph.walk
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  unfold WeightedGraph.degree
  have hsum0 : (∑ x : B, G.weight b x) ≠ 0 := by
    change G.degree b ≠ 0
    exact (hdegree b).ne'
  field_simp [hsum0]

/-- Excluding one point subtracts exactly its fluctuation from the average. -/
theorem excludeAverage_eq_average_sub_fluctuation
    {I : Type u} [Fintype I] [DecidableEq I]
    (hI : 2 ≤ Fintype.card I) (f : I → ℝ) (i : I) :
    excludeAverage f i =
      uniformAverage f - (f i - uniformAverage f) /
        ((Fintype.card I : ℝ) - 1) := by
  classical
  have hI0 : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast (show 0 < Fintype.card I by omega).ne'
  have hI10 : (Fintype.card I : ℝ) - 1 ≠ 0 := by
    have hIR : (2 : ℝ) ≤ Fintype.card I := by exact_mod_cast hI
    linarith
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset I) f
    (Finset.mem_univ i)
  have hsum : ∑ x ∈ (Finset.univ.erase i : Finset I), f x =
      (∑ x : I, f x) - f i := by linarith
  unfold excludeAverage uniformAverage
  rw [hsum]
  field_simp
  ring

/-- Reconstruction in the occupied fiber. -/
theorem occupied_reconstruct (f : OneFiberVertex O B A → ℝ) (i : O) :
    f (Sum.inl i) = occupiedAverage f + occupiedFluctuation f i := by
  simp [occupiedFluctuation]

/-- Reconstruction in every other fiber. -/
theorem other_reconstruct (f : OneFiberVertex O B A → ℝ)
    (b : B) (a : A) :
    f (Sum.inr (b, a)) =
      allOtherAverage G f + baseFluctuation G f b +
        otherFluctuation f b a := by
  simp [baseFluctuation, otherFluctuation]

/-- Occupied-fiber fluctuations sum to zero. -/
theorem sum_occupiedFluctuation (hO : 0 < Fintype.card O)
    (f : OneFiberVertex O B A → ℝ) :
    ∑ i : O, occupiedFluctuation f i = 0 := by
  classical
  unfold occupiedFluctuation occupiedAverage uniformAverage
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hO0 : (Fintype.card O : ℝ) ≠ 0 := by
    exact_mod_cast hO.ne'
  field_simp
  ring

/-- Every other-fiber fluctuation sums to zero inside that fiber. -/
theorem sum_otherFluctuation (hA : 0 < Fintype.card A)
    (f : OneFiberVertex O B A → ℝ) (b : B) :
    ∑ a : A, otherFluctuation f b a = 0 := by
  classical
  unfold otherFluctuation otherFiberAverage uniformAverage
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hA0 : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast hA.ne'
  field_simp
  ring

/-- Exact action on the occupied-fiber zero-sum summand plus the two
dimensional quotient summand. -/
theorem walk_occupied_decomposition [Nonempty B]
    (hdegree : ∀ b, 0 < G.degree b)
    (f : OneFiberVertex O B A → ℝ) (i : O) :
    (conditionedOneFiberGraph d hd hm hOcard G).walk f (Sum.inl i) =
      oneFiberQuotientValue d G f +
        occupiedWithinEigenvalue d (Fintype.card A) *
          occupiedFluctuation f i := by
  rw [conditionedOneFiberGraph_walk_occupied d hd hm hOcard G hdegree]
  rw [excludeAverage_eq_average_sub_fluctuation
    (show 2 ≤ Fintype.card O by omega)]
  have hcardReal : (Fintype.card A : ℝ) - d =
      (Fintype.card O : ℝ) - 1 := by
    have hNat : Fintype.card A = Fintype.card O + d - 1 := by omega
    have hcast : (Fintype.card A : ℝ) = Fintype.card O + d - 1 := by
      rw [show (Fintype.card O : ℝ) + d - 1 =
          ((Fintype.card O + d - 1 : ℕ) : ℝ) by
        rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card O + d)]
        norm_num]
      exact_mod_cast hNat
    linarith
  unfold oneFiberQuotientValue occupiedWithinEigenvalue
  unfold occupiedFluctuation occupiedAverage
  rw [hcardReal]
  have hd10 : (d + 1 : ℝ) ≠ 0 := by positivity
  have hO10 : (Fintype.card O : ℝ) - 1 ≠ 0 := by
    have htwo : (2 : ℝ) ≤ Fintype.card O := by exact_mod_cast (show 2 ≤ Fintype.card O by omega)
    linarith
  field_simp
  ring

/-- Exact action on the base-link summand, every other-fiber zero-sum
summand, and the quotient summand. -/
theorem walk_other_decomposition [Nonempty B]
    (hdegree : ∀ b, 0 < G.degree b)
    (f : OneFiberVertex O B A → ℝ) (b : B) (a : A) :
    (conditionedOneFiberGraph d hd hm hOcard G).walk f
        (Sum.inr (b, a)) =
      oneFiberQuotientValue d G f +
        (baseFluctuation G f b + G.walk (baseFluctuation G f) b) /
          (d + 1 : ℝ) +
        otherWithinEigenvalue d (Fintype.card A) *
          otherFluctuation f b a := by
  rw [conditionedOneFiberGraph_walk_other d hd hm hOcard G hdegree]
  rw [excludeAverage_eq_average_sub_fluctuation
    (show 2 ≤ Fintype.card A by omega)]
  have hsplit : otherFiberAverage f =
      fun x ↦ baseFluctuation G f x + allOtherAverage G f := by
    funext x
    simp [baseFluctuation]
  rw [hsplit, walk_add_const G hdegree]
  unfold oneFiberQuotientValue otherWithinEigenvalue
  unfold occupiedAverage otherFluctuation baseFluctuation
  have hcomm :
      (fun x ↦ otherFiberAverage f x - allOtherAverage G f) =
        (fun x ↦ -allOtherAverage G f + otherFiberAverage f x) := by
    funext x
    ring
  rw [hcomm]
  simp only [otherFiberAverage]
  have hd10 : (d + 1 : ℝ) ≠ 0 := by positivity
  have hA10 : (Fintype.card A : ℝ) - 1 ≠ 0 := by
    have htwo : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast (show 2 ≤ Fintype.card A by omega)
    linarith
  field_simp
  ring

/-- Thus the displayed three families of subspaces span the entire function
space, and the normalized walk is block diagonal apart from the explicit
two-dimensional quotient coordinate. -/
theorem oneFiber_complete_pointwise_decomposition [Nonempty B]
    (hdegree : ∀ b, 0 < G.degree b)
    (f : OneFiberVertex O B A → ℝ) :
    (∀ i : O,
      (conditionedOneFiberGraph d hd hm hOcard G).walk f (Sum.inl i) =
        oneFiberQuotientValue d G f +
          occupiedWithinEigenvalue d (Fintype.card A) *
            occupiedFluctuation f i) ∧
    (∀ b : B, ∀ a : A,
      (conditionedOneFiberGraph d hd hm hOcard G).walk f
          (Sum.inr (b, a)) =
        oneFiberQuotientValue d G f +
          (baseFluctuation G f b + G.walk (baseFluctuation G f) b) /
            (d + 1 : ℝ) +
          otherWithinEigenvalue d (Fintype.card A) *
            otherFluctuation f b a) :=
  ⟨walk_occupied_decomposition d hd hm hOcard G hdegree f,
    walk_other_decomposition d hd hm hOcard G hdegree f⟩

/-- The stationary mean lives entirely in the two-dimensional quotient
summand.  This identity is the weighted orthogonality statement needed to
remove the stationary eigenvector. -/
theorem conditionedOneFiberGraph_weightedMean [Nonempty B]
    (hdegree : ∀ b, 0 < G.degree b)
    (f : OneFiberVertex O B A → ℝ) :
    (conditionedOneFiberGraph d hd hm hOcard G).weightedMean f =
      ((d + 1 : ℝ) ^ 2 * (Fintype.card A : ℝ) * graphVolume G / 2) *
        oneFiberQuotientValue d G f := by
  classical
  have hO0 : (Fintype.card O : ℝ) ≠ 0 := by
    exact_mod_cast (cardO_pos (A := A) d hd hm hOcard).ne'
  have hA0 : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (cardA_pos (d := d) hd hm).ne'
  have hvol0 : graphVolume G ≠ 0 :=
    (graphVolume_pos (G := G) hdegree).ne'
  have hsumO :
      (∑ i : O, f (Sum.inl i)) =
        (Fintype.card O : ℝ) * occupiedAverage f := by
    unfold occupiedAverage uniformAverage
    field_simp
  have hsumA (b : B) :
      (∑ a : A, f (Sum.inr (b, a))) =
        (Fintype.card A : ℝ) * otherFiberAverage f b := by
    unfold otherFiberAverage uniformAverage
    field_simp
  have hstationary :
      G.weightedMean (otherFiberAverage f) =
        graphVolume G * allOtherAverage G f := by
    unfold allOtherAverage stationaryAverage
    field_simp
  unfold WeightedGraph.weightedMean
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp_rw [conditionedOneFiberGraph_degree_occupied d hd hm hOcard G,
    conditionedOneFiberGraph_degree_other d hd hm hOcard G]
  rw [← Finset.mul_sum]
  rw [hsumO]
  have hright :
      (∑ b : B, ∑ a : A,
        ((d + 1 : ℝ) * G.degree b) * f (Sum.inr (b, a))) =
        (d + 1 : ℝ) * (Fintype.card A : ℝ) *
          G.weightedMean (otherFiberAverage f) := by
    unfold WeightedGraph.weightedMean
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _hb
    rw [← Finset.mul_sum, hsumA]
    ring
  rw [hright, hstationary]
  unfold oneFiberQuotientValue
  field_simp

/-- On the stationary-mean-zero subspace the quotient block is the zero
eigenspace from the page-15 table. -/
theorem quotientValue_eq_zero_of_weightedMean_zero [Nonempty B]
    (hdegree : ∀ b, 0 < G.degree b)
    (f : OneFiberVertex O B A → ℝ)
    (hmean : (conditionedOneFiberGraph d hd hm hOcard G).weightedMean f = 0) :
    oneFiberQuotientValue d G f = 0 := by
  rw [conditionedOneFiberGraph_weightedMean d hd hm hOcard G hdegree] at hmean
  have hfactor :
      ((d + 1 : ℝ) ^ 2 * (Fintype.card A : ℝ) * graphVolume G / 2) ≠ 0 := by
    have hA : (0 : ℝ) < Fintype.card A := by
      exact_mod_cast cardA_pos (d := d) hd hm
    have hvol := graphVolume_pos (G := G) hdegree
    positivity
  exact (mul_eq_zero.mp hmean).resolve_left hfactor

/-- The four nonstationary eigenvalue types in the one-fiber row of the
paper's table, now retaining the fact that `theta` really is a base-link
eigenvalue. -/
inductive OneFiberCandidate (d m : ℕ) (G : WeightedGraph B) : ℝ → Prop
  | quotientZero : OneFiberCandidate d m G 0
  | base (theta : ℝ)
      (htheta : AffineRelationSpectrum.IsMeanZeroEigenvalue G theta) :
      OneFiberCandidate d m G ((1 + theta) / (d + 1 : ℝ))
  | occupiedWithin :
      OneFiberCandidate d m G (occupiedWithinEigenvalue d m)
  | otherWithin :
      OneFiberCandidate d m G (otherWithinEigenvalue d m)

/-- The occupied fluctuation vanishes when the function is constant on that
fiber. -/
theorem occupiedFluctuation_eq_zero_of_constant
    (f : OneFiberVertex O B A → ℝ)
    (hOpos : 0 < Fintype.card O)
    (hconstant : ∀ i j : O, f (Sum.inl i) = f (Sum.inl j)) (i : O) :
    occupiedFluctuation f i = 0 := by
  have hfun : (fun j : O ↦ f (Sum.inl j)) = fun _ ↦ f (Sum.inl i) := by
    funext j
    exact hconstant j i
  unfold occupiedFluctuation occupiedAverage
  rw [hfun, uniformAverage_const hOpos]
  ring

/-- A within-fiber fluctuation vanishes when that fiber is constant. -/
theorem otherFluctuation_eq_zero_of_constant
    (f : OneFiberVertex O B A → ℝ) (b : B)
    (hApos : 0 < Fintype.card A)
    (hconstant : ∀ a e : A,
      f (Sum.inr (b, a)) = f (Sum.inr (b, e))) (a : A) :
    otherFluctuation f b a = 0 := by
  have hfun : (fun e : A ↦ f (Sum.inr (b, e))) =
      fun _ ↦ f (Sum.inr (b, a)) := by
    funext e
    exact hconstant e a
  unfold otherFluctuation otherFiberAverage
  rw [hfun, uniformAverage_const hApos]
  ring

/-- Completeness of the one-fiber spectral table.  This proof uses the
pointwise direct-sum formula above: a nonzero fluctuation in either kind of
fiber forces the corresponding scalar eigenvalue; otherwise the eigenvector
descends to a genuine eigenvector of the base vertex link. -/
theorem oneFiberCandidate_complete [Nonempty B]
    (hdegree : ∀ b, 0 < G.degree b) (mu : ℝ)
    (hmu : AffineRelationSpectrum.IsMeanZeroEigenvalue
      (conditionedOneFiberGraph d hd hm hOcard G) mu) :
    OneFiberCandidate d (Fintype.card A) G mu := by
  obtain ⟨f, hfne, hmean, heigen⟩ := hmu
  have hquotient : oneFiberQuotientValue d G f = 0 :=
    quotientValue_eq_zero_of_weightedMean_zero d hd hm hOcard G hdegree f hmean
  by_cases hmu0 : mu = 0
  · subst mu
    exact OneFiberCandidate.quotientZero
  by_cases hoccupied : ∃ i j : O, f (Sum.inl i) ≠ f (Sum.inl j)
  · obtain ⟨i, j, hij⟩ := hoccupied
    have hi := congrFun heigen (Sum.inl i)
    have hj := congrFun heigen (Sum.inl j)
    rw [walk_occupied_decomposition d hd hm hOcard G hdegree,
      hquotient, zero_add] at hi
    rw [walk_occupied_decomposition d hd hm hOcard G hdegree,
      hquotient, zero_add] at hj
    have hfluct : occupiedFluctuation f i - occupiedFluctuation f j =
        f (Sum.inl i) - f (Sum.inl j) := by
      simp [occupiedFluctuation]
    have hproduct :
        (mu - occupiedWithinEigenvalue d (Fintype.card A)) *
          (f (Sum.inl i) - f (Sum.inl j)) = 0 := by
      calc
        _ = mu * (f (Sum.inl i) - f (Sum.inl j)) -
            occupiedWithinEigenvalue d (Fintype.card A) *
              (occupiedFluctuation f i - occupiedFluctuation f j) := by
                rw [hfluct]
                ring
        _ = (mu * f (Sum.inl i) -
              occupiedWithinEigenvalue d (Fintype.card A) * occupiedFluctuation f i) -
            (mu * f (Sum.inl j) -
              occupiedWithinEigenvalue d (Fintype.card A) * occupiedFluctuation f j) := by
                ring
        _ = 0 := by rw [← hi, ← hj]; ring
    have heq : mu = occupiedWithinEigenvalue d (Fintype.card A) := by
      rcases mul_eq_zero.mp hproduct with h | h
      · linarith
      · exfalso
        apply hij
        linarith
    rw [heq]
    exact OneFiberCandidate.occupiedWithin
  push_neg at hoccupied
  by_cases hother : ∃ b : B, ∃ a e : A,
      f (Sum.inr (b, a)) ≠ f (Sum.inr (b, e))
  · obtain ⟨b, a, e, hae⟩ := hother
    have ha := congrFun heigen (Sum.inr (b, a))
    have he := congrFun heigen (Sum.inr (b, e))
    rw [walk_other_decomposition d hd hm hOcard G hdegree,
      hquotient, zero_add] at ha
    rw [walk_other_decomposition d hd hm hOcard G hdegree,
      hquotient, zero_add] at he
    have hfluct : otherFluctuation f b a - otherFluctuation f b e =
        f (Sum.inr (b, a)) - f (Sum.inr (b, e)) := by
      simp [otherFluctuation]
    have hproduct :
        (mu - otherWithinEigenvalue d (Fintype.card A)) *
          (f (Sum.inr (b, a)) - f (Sum.inr (b, e))) = 0 := by
      calc
        _ = mu * (f (Sum.inr (b, a)) - f (Sum.inr (b, e))) -
            otherWithinEigenvalue d (Fintype.card A) *
              (otherFluctuation f b a - otherFluctuation f b e) := by
                rw [hfluct]
                ring
        _ = (mu * f (Sum.inr (b, a)) -
              otherWithinEigenvalue d (Fintype.card A) * otherFluctuation f b a) -
            (mu * f (Sum.inr (b, e)) -
              otherWithinEigenvalue d (Fintype.card A) * otherFluctuation f b e) := by
                ring
        _ = 0 := by rw [← ha, ← he]; ring
    have heq : mu = otherWithinEigenvalue d (Fintype.card A) := by
      rcases mul_eq_zero.mp hproduct with h | h
      · linarith
      · exfalso
        apply hae
        linarith
    rw [heq]
    exact OneFiberCandidate.otherWithin
  push_neg at hother
  haveI : Nonempty O := Fintype.card_pos_iff.mp
    (cardO_pos (A := A) d hd hm hOcard)
  haveI : Nonempty A := Fintype.card_pos_iff.mp
    (cardA_pos (d := d) hd hm)
  let i₀ : O := Classical.choice inferInstance
  let a₀ : A := Classical.choice inferInstance
  have hoccZero (i : O) : occupiedFluctuation f i = 0 :=
    occupiedFluctuation_eq_zero_of_constant f
      (cardO_pos (A := A) d hd hm hOcard) hoccupied i
  have hotherZero (b : B) (a : A) : otherFluctuation f b a = 0 :=
    otherFluctuation_eq_zero_of_constant f b
      (cardA_pos (d := d) hd hm) (hother b) a
  have hi := congrFun heigen (Sum.inl i₀)
  rw [walk_occupied_decomposition d hd hm hOcard G hdegree,
    hquotient, hoccZero, mul_zero, zero_add] at hi
  have hfi₀ : f (Sum.inl i₀) = 0 := by
    exact (mul_eq_zero.mp hi.symm).resolve_left hmu0
  have hoccAverage : occupiedAverage f = 0 := by
    have hreconstruct := occupied_reconstruct f i₀
    rw [hoccZero, add_zero, hfi₀] at hreconstruct
    exact hreconstruct.symm
  have hotherAverage : allOtherAverage G f = 0 := by
    unfold oneFiberQuotientValue at hquotient
    rw [hoccAverage] at hquotient
    have hd1 : (d + 1 : ℝ) ≠ 0 := by positivity
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    field_simp at hquotient
    linarith
  let g : B → ℝ := baseFluctuation G f
  have hgMean : G.weightedMean g = 0 :=
    weightedMean_baseFluctuation G hdegree f
  have hfg (b : B) : f (Sum.inr (b, a₀)) = g b := by
    rw [other_reconstruct (G := G) f b a₀, hotherAverage,
      hotherZero]
    simp [g]
  have hgEigen : G.walk g = fun b ↦ ((d + 1 : ℝ) * mu - 1) * g b := by
    funext b
    have hb := congrFun heigen (Sum.inr (b, a₀))
    rw [walk_other_decomposition d hd hm hOcard G hdegree,
      hquotient, hotherZero, mul_zero, add_zero, zero_add, hfg] at hb
    change (g b + G.walk g b) / (d + 1 : ℝ) = mu * g b at hb
    have hd1 : (d + 1 : ℝ) ≠ 0 := by positivity
    field_simp at hb
    linarith
  have hgNe : g ≠ 0 := by
    intro hg
    apply hfne
    funext z
    rcases z with i | ⟨b, a⟩
    · have hreconstruct := occupied_reconstruct f i
      rw [hoccAverage, hoccZero] at hreconstruct
      simpa using hreconstruct
    · rw [other_reconstruct (G := G) f b a, hotherAverage,
        hotherZero]
      simpa [g] using congrFun hg b
  let theta : ℝ := (d + 1 : ℝ) * mu - 1
  have htheta : AffineRelationSpectrum.IsMeanZeroEigenvalue G theta :=
    ⟨g, hgNe, hgMean, hgEigen⟩
  have hmueq : mu = (1 + theta) / (d + 1 : ℝ) := by
    simp only [theta]
    have hd1 : (d + 1 : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hmueq]
  exact OneFiberCandidate.base theta htheta

omit [DecidableEq O] [Fintype O] [DecidableEq A] [Fintype A] in
/-- A nonzero function has positive stationary squared norm when every
weighted degree is positive. -/
theorem sqNorm_pos_of_degree_pos (hdegree : ∀ b, 0 < G.degree b)
    {f : B → ℝ} (hf : f ≠ 0) : 0 < G.sqNorm f := by
  classical
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hf
  have hfb : f b ≠ 0 := by simpa using hb
  unfold WeightedGraph.sqNorm
  apply Finset.sum_pos'
  · intro c _hc
    exact mul_nonneg (G.degree_nonneg c) (sq_nonneg (f c))
  · refine ⟨b, Finset.mem_univ _, ?_⟩
    exact mul_pos (hdegree b) (sq_pos_of_ne_zero hfb)

omit [DecidableEq O] [Fintype O] [DecidableEq A] [Fintype A] in
/-- The `L²` definition of a two-sided bound controls every genuine
stationary-mean-zero eigenvalue. -/
theorem abs_eigenvalue_le_of_twoSidedSpectralBound
    {lambda theta : ℝ} (hdegree : ∀ b, 0 < G.degree b)
    (hbound : G.TwoSidedSpectralBound lambda)
    (htheta : AffineRelationSpectrum.IsMeanZeroEigenvalue G theta) :
    |theta| ≤ lambda := by
  obtain ⟨f, hfne, hmean, heigen⟩ := htheta
  have hineq := hbound.2 f hmean
  rw [heigen] at hineq
  have hsquareNorm :
      G.sqNorm (fun v ↦ theta * f v) = theta ^ 2 * G.sqNorm f := by
    unfold WeightedGraph.sqNorm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    ring
  rw [hsquareNorm] at hineq
  have hnorm : 0 < G.sqNorm f := sqNorm_pos_of_degree_pos G hdegree hfne
  have hsquare : theta ^ 2 ≤ lambda ^ 2 :=
    le_of_mul_le_mul_right hineq hnorm
  apply (sq_le_sq₀ (abs_nonneg theta) hbound.1).mp
  simpa only [sq_abs] using hsquare

/-- Every complete one-fiber candidate is one of the numerical table entries
already bounded in `WeightedLiftSpectrum`. -/
theorem OneFiberCandidate.toTable [Nonempty B]
    (hdegree : ∀ b, 0 < G.degree b)
    (hbase : G.TwoSidedSpectralBound (1 / (d : ℝ)))
    {mu : ℝ} (hmu : OneFiberCandidate d (Fintype.card A) G mu) :
    TableEigenvalue d (Fintype.card A) mu := by
  cases hmu with
  | quotientZero => exact TableEigenvalue.oneFiberZero
  | base theta htheta =>
      exact TableEigenvalue.oneFiberBase theta
        (abs_eigenvalue_le_of_twoSidedSpectralBound G hdegree hbase htheta)
  | occupiedWithin =>
      simpa only [occupiedWithinEigenvalue] using
        (TableEigenvalue.oneFiberOccupiedWithin (d := d)
          (m := Fintype.card A))
  | otherWithin =>
      simpa only [otherWithinEigenvalue] using
        (TableEigenvalue.oneFiberOtherWithin (d := d)
          (m := Fintype.card A))

/-- Complete eigenvalue conclusion for the one-occupied-fiber conditioned
link: every nonstationary eigenvalue has absolute value at most `1/d`. -/
theorem oneFiber_meanZeroEigenvalue_bound [Nonempty B]
    (hdegree : ∀ b, 0 < G.degree b)
    (hbase : G.TwoSidedSpectralBound (1 / (d : ℝ)))
    (mu : ℝ)
    (hmu : AffineRelationSpectrum.IsMeanZeroEigenvalue
      (conditionedOneFiberGraph d hd hm hOcard G) mu) :
    |mu| ≤ 1 / (d : ℝ) := by
  apply tableEigenvalue_bound hd hm
  exact OneFiberCandidate.toTable (d := d) (A := A) (G := G)
    hdegree hbase
    (oneFiberCandidate_complete d hd hm hOcard G hdegree mu hmu)

/-! ## Direct weighted `L²` estimate -/

/-- Orthogonality of a constant and a zero-sum finite family, with an
additional scalar on the zero-sum part. -/
theorem sum_sq_const_add_scaled_of_sum_zero
    {I : Type u} [Fintype I]
    (w : I → ℝ) (hw : ∑ i : I, w i = 0) (c e : ℝ) :
    ∑ i : I, (c + e * w i) ^ 2 =
      (Fintype.card I : ℝ) * c ^ 2 + e ^ 2 * ∑ i : I, (w i) ^ 2 := by
  classical
  have hpoint (i : I) :
      (c + e * w i) ^ 2 = c ^ 2 + 2 * c * e * w i + e ^ 2 * (w i) ^ 2 := by
    ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  rw [hw]
  rw [← Finset.mul_sum]
  ring

/-- Pythagoras for the occupied-fiber mean and its zero-sum fluctuation. -/
theorem sum_sq_occupied_decomposition
    (hOpos : 0 < Fintype.card O)
    (f : OneFiberVertex O B A → ℝ) :
    ∑ i : O, (f (Sum.inl i)) ^ 2 =
      (Fintype.card O : ℝ) * (occupiedAverage f) ^ 2 +
        ∑ i : O, (occupiedFluctuation f i) ^ 2 := by
  have hsum := sum_occupiedFluctuation hOpos f
  have h := sum_sq_const_add_scaled_of_sum_zero
    (fun i : O ↦ occupiedFluctuation f i) hsum (occupiedAverage f) 1
  simp only [one_mul, one_pow] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← occupied_reconstruct f i]

/-- Pythagoras inside each other fiber. -/
theorem sum_sq_otherFiber_decomposition
    (hApos : 0 < Fintype.card A)
    (f : OneFiberVertex O B A → ℝ) (b : B) :
    ∑ a : A, (f (Sum.inr (b, a))) ^ 2 =
      (Fintype.card A : ℝ) *
          (allOtherAverage G f + baseFluctuation G f b) ^ 2 +
        ∑ a : A, (otherFluctuation f b a) ^ 2 := by
  have hsum := sum_otherFluctuation hApos f b
  have h := sum_sq_const_add_scaled_of_sum_zero
    (fun a : A ↦ otherFluctuation f b a) hsum
      (allOtherAverage G f + baseFluctuation G f b) 1
  simp only [one_mul, one_pow] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [← other_reconstruct (G := G) f b a]

/-- Pythagoras for the stationary mean and the base-link mean-zero part. -/
theorem weighted_sq_base_decomposition [Nonempty B]
    (hdegree : ∀ b, 0 < G.degree b)
    (f : OneFiberVertex O B A → ℝ) :
    ∑ b : B, G.degree b *
        (allOtherAverage G f + baseFluctuation G f b) ^ 2 =
      graphVolume G * (allOtherAverage G f) ^ 2 +
        G.sqNorm (baseFluctuation G f) := by
  classical
  let q := allOtherAverage G f
  let g := baseFluctuation G f
  have hg : G.weightedMean g = 0 :=
    weightedMean_baseFluctuation G hdegree f
  unfold WeightedGraph.weightedMean at hg
  unfold WeightedGraph.sqNorm
  change (∑ b : B, G.degree b * (q + g b) ^ 2) =
    graphVolume G * q ^ 2 + ∑ b : B, G.degree b * (g b) ^ 2
  have hpoint (b : B) :
      G.degree b * (q + g b) ^ 2 =
        G.degree b * q ^ 2 + 2 * q * (G.degree b * g b) +
          G.degree b * (g b) ^ 2 := by ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  rw [hg]
  simp only [mul_zero, zero_add]
  rw [← Finset.sum_mul]
  simp only [graphVolume, add_zero]

/-- Exact stationary squared norm of a function in terms of the four
orthogonal components. -/
theorem conditionedOneFiberGraph_sqNorm_decomposition [Nonempty B]
    (hdegree : ∀ b, 0 < G.degree b)
    (f : OneFiberVertex O B A → ℝ) :
    (conditionedOneFiberGraph d hd hm hOcard G).sqNorm f =
      ((d + 1 : ℝ) * (Fintype.card A : ℝ) * (d - 1 : ℝ) *
          graphVolume G / (2 * (Fintype.card O : ℝ))) *
        ((Fintype.card O : ℝ) * (occupiedAverage f) ^ 2 +
          ∑ i : O, (occupiedFluctuation f i) ^ 2) +
      (d + 1 : ℝ) *
        ((Fintype.card A : ℝ) *
            (graphVolume G * (allOtherAverage G f) ^ 2 +
              G.sqNorm (baseFluctuation G f)) +
          ∑ b : B, G.degree b *
            ∑ a : A, (otherFluctuation f b a) ^ 2) := by
  classical
  unfold WeightedGraph.sqNorm
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp_rw [conditionedOneFiberGraph_degree_occupied d hd hm hOcard G,
    conditionedOneFiberGraph_degree_other d hd hm hOcard G]
  rw [← Finset.mul_sum,
    sum_sq_occupied_decomposition
      (cardO_pos (A := A) d hd hm hOcard) f]
  have hright :
      (∑ b : B, ∑ a : A,
        ((d + 1 : ℝ) * G.degree b) * (f (Sum.inr (b, a))) ^ 2) =
        (d + 1 : ℝ) *
          ((Fintype.card A : ℝ) *
              (graphVolume G * (allOtherAverage G f) ^ 2 +
                G.sqNorm (baseFluctuation G f)) +
            ∑ b : B, G.degree b *
              ∑ a : A, (otherFluctuation f b a) ^ 2) := by
    calc
      _ = (d + 1 : ℝ) *
          (∑ b : B, G.degree b *
            ∑ a : A, (f (Sum.inr (b, a))) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _hb
            calc
              ∑ a : A, (d + 1 : ℝ) * G.degree b *
                    (f (Sum.inr (b, a))) ^ 2 =
                  ∑ a : A, (d + 1 : ℝ) *
                    (G.degree b * (f (Sum.inr (b, a))) ^ 2) := by
                      apply Finset.sum_congr rfl
                      intro a _ha
                      ring
              _ = (d + 1 : ℝ) *
                    ∑ a : A, G.degree b *
                      (f (Sum.inr (b, a))) ^ 2 :=
                    (Finset.mul_sum _ _ _).symm
              _ = (d + 1 : ℝ) *
                    (G.degree b *
                      ∑ a : A, (f (Sum.inr (b, a))) ^ 2) := by
                    apply congrArg ((d + 1 : ℝ) * ·)
                    exact (Finset.mul_sum _ _ _).symm
      _ = (d + 1 : ℝ) *
          ((Fintype.card A : ℝ) *
              (∑ b : B, G.degree b *
                (allOtherAverage G f + baseFluctuation G f b) ^ 2) +
            ∑ b : B, G.degree b *
              ∑ a : A, (otherFluctuation f b a) ^ 2) := by
            apply congrArg ((d + 1 : ℝ) * ·)
            simp_rw [sum_sq_otherFiber_decomposition G
              (cardA_pos (d := d) hd hm) f]
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro b _hb
            ring
      _ = _ := by
        rw [weighted_sq_base_decomposition G hdegree f]
  rw [hright]
  rfl

/-- A weighted Young inequality tuned to the constants in the lift. -/
theorem lift_sq_add_bound (hdposNat : 0 < d) (x y : ℝ) :
    (x + y) ^ 2 ≤
      (1 + 1 / (d : ℝ)) * x ^ 2 +
        (1 + (d : ℝ)) * y ^ 2 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hdposNat
  have hpoly :
      (d : ℝ) * (x + y) ^ 2 ≤
        ((d : ℝ) + 1) * x ^ 2 +
          (d : ℝ) * ((d : ℝ) + 1) * y ^ 2 := by
    nlinarith [sq_nonneg (x - (d : ℝ) * y)]
  calc
    (x + y) ^ 2 ≤
        (((d : ℝ) + 1) * x ^ 2 +
          (d : ℝ) * ((d : ℝ) + 1) * y ^ 2) / d :=
      (le_div_iff₀ hdpos).2 (by simpa [mul_comm] using hpoly)
    _ = (1 + 1 / (d : ℝ)) * x ^ 2 +
        (1 + (d : ℝ)) * y ^ 2 := by
      field_simp
      ring

/-- The base mean-zero component, transformed by `(I+P)/(d+1)`, has norm at
most `1/d`. -/
theorem baseFluctuation_transform_sqNorm_bound [Nonempty B]
    (hdBound : 3 ≤ d)
    (hdegree : ∀ b, 0 < G.degree b)
    (hbase : G.TwoSidedSpectralBound (1 / (d : ℝ)))
    (f : OneFiberVertex O B A → ℝ) :
    G.sqNorm (fun b ↦
        (baseFluctuation G f b + G.walk (baseFluctuation G f) b) /
          (d + 1 : ℝ)) ≤
      (1 / (d : ℝ)) ^ 2 * G.sqNorm (baseFluctuation G f) := by
  let g := baseFluctuation G f
  have hgmean : G.weightedMean g = 0 :=
    weightedMean_baseFluctuation G hdegree f
  have hwalk := hbase.2 g hgmean
  have hsum :
      G.sqNorm (fun b ↦ g b + G.walk g b) ≤
        (1 + 1 / (d : ℝ)) * G.sqNorm g +
          (1 + (d : ℝ)) * G.sqNorm (G.walk g) := by
    unfold WeightedGraph.sqNorm
    calc
      ∑ b : B, G.degree b * (g b + G.walk g b) ^ 2 ≤
          ∑ b : B, G.degree b *
            ((1 + 1 / (d : ℝ)) * (g b) ^ 2 +
              (1 + (d : ℝ)) * (G.walk g b) ^ 2) := by
            apply Finset.sum_le_sum
            intro b _hb
            exact mul_le_mul_of_nonneg_left
              (lift_sq_add_bound (d := d) (by omega) (g b) (G.walk g b))
              (G.degree_nonneg b)
      _ = (1 + 1 / (d : ℝ)) *
            ∑ b : B, G.degree b * (g b) ^ 2 +
          (1 + (d : ℝ)) *
            ∑ b : B, G.degree b * (G.walk g b) ^ 2 := by
              rw [Finset.mul_sum, Finset.mul_sum,
                ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro b _hb
              ring
  have hcombined :
      G.sqNorm (fun b ↦ g b + G.walk g b) ≤
        (((d : ℝ) + 1) ^ 2 / (d : ℝ) ^ 2) * G.sqNorm g := by
    calc
      _ ≤ (1 + 1 / (d : ℝ)) * G.sqNorm g +
          (1 + (d : ℝ)) * G.sqNorm (G.walk g) := hsum
      _ ≤ (1 + 1 / (d : ℝ)) * G.sqNorm g +
          (1 + (d : ℝ)) *
            ((1 / (d : ℝ)) ^ 2 * G.sqNorm g) := by
              have hcoef : 0 ≤ 1 + (d : ℝ) := by positivity
              exact add_le_add_right
                (mul_le_mul_of_nonneg_left hwalk hcoef) _
      _ = (((d : ℝ) + 1) ^ 2 / (d : ℝ) ^ 2) * G.sqNorm g := by
        have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
        field_simp
        ring
  have hscale :
      G.sqNorm (fun b ↦ (g b + G.walk g b) / (d + 1 : ℝ)) =
        (1 / (d + 1 : ℝ)) ^ 2 *
          G.sqNorm (fun b ↦ g b + G.walk g b) := by
    unfold WeightedGraph.sqNorm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  rw [hscale]
  calc
    _ ≤ (1 / (d + 1 : ℝ)) ^ 2 *
        ((((d : ℝ) + 1) ^ 2 / (d : ℝ) ^ 2) * G.sqNorm g) :=
      mul_le_mul_of_nonneg_left hcombined (sq_nonneg _)
    _ = (1 / (d : ℝ)) ^ 2 * G.sqNorm g := by
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
      have hd10 : (d + 1 : ℝ) ≠ 0 := by positivity
      field_simp

/-- The occupied-fiber scalar in the exact decomposition is bounded by the
target two-sided parameter. -/
theorem occupiedWithinEigenvalue_sq_le
    (hdBound : 3 ≤ d) (hmBound : 2 * d ≤ Fintype.card A) :
    (occupiedWithinEigenvalue d (Fintype.card A)) ^ 2 ≤
      (1 / (d : ℝ)) ^ 2 := by
  have habs : |occupiedWithinEigenvalue d (Fintype.card A)| ≤
      1 / (d : ℝ) := by
    apply tableEigenvalue_bound hdBound hmBound
    simpa only [occupiedWithinEigenvalue] using
      (TableEigenvalue.oneFiberOccupiedWithin
        (d := d) (m := Fintype.card A))
  have htarget : 0 ≤ 1 / (d : ℝ) := by positivity
  calc
    (occupiedWithinEigenvalue d (Fintype.card A)) ^ 2 =
        |occupiedWithinEigenvalue d (Fintype.card A)| ^ 2 :=
      (sq_abs _).symm
    _ ≤ (1 / (d : ℝ)) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) htarget).2 habs

/-- The other-fiber scalar in the exact decomposition is bounded by the
target two-sided parameter. -/
theorem otherWithinEigenvalue_sq_le
    (hdBound : 3 ≤ d) (hmBound : 2 * d ≤ Fintype.card A) :
    (otherWithinEigenvalue d (Fintype.card A)) ^ 2 ≤
      (1 / (d : ℝ)) ^ 2 := by
  have habs : |otherWithinEigenvalue d (Fintype.card A)| ≤
      1 / (d : ℝ) := by
    apply tableEigenvalue_bound hdBound hmBound
    simpa only [otherWithinEigenvalue] using
      (TableEigenvalue.oneFiberOtherWithin
        (d := d) (m := Fintype.card A))
  have htarget : 0 ≤ 1 / (d : ℝ) := by positivity
  calc
    (otherWithinEigenvalue d (Fintype.card A)) ^ 2 =
        |otherWithinEigenvalue d (Fintype.card A)| ^ 2 :=
      (sq_abs _).symm
    _ ≤ (1 / (d : ℝ)) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) htarget).2 habs

/-- Exact output energy after the stationary quotient coordinate has
vanished.  This is the weighted orthogonal direct-sum identity behind the
one-fiber row of the page-15 table. -/
theorem conditionedOneFiberGraph_walk_sqNorm_of_mean_zero [Nonempty B]
    (hdegree : ∀ b, 0 < G.degree b)
    (f : OneFiberVertex O B A → ℝ)
    (hmean : (conditionedOneFiberGraph d hd hm hOcard G).weightedMean f = 0) :
    (conditionedOneFiberGraph d hd hm hOcard G).sqNorm
        ((conditionedOneFiberGraph d hd hm hOcard G).walk f) =
      ((d + 1 : ℝ) * (Fintype.card A : ℝ) * (d - 1 : ℝ) *
          graphVolume G / (2 * (Fintype.card O : ℝ))) *
        ((occupiedWithinEigenvalue d (Fintype.card A)) ^ 2 *
          ∑ i : O, (occupiedFluctuation f i) ^ 2) +
      (d + 1 : ℝ) *
        ((Fintype.card A : ℝ) *
            G.sqNorm (fun b ↦
              (baseFluctuation G f b +
                G.walk (baseFluctuation G f) b) / (d + 1 : ℝ)) +
          (otherWithinEigenvalue d (Fintype.card A)) ^ 2 *
            ∑ b : B, G.degree b *
              ∑ a : A, (otherFluctuation f b a) ^ 2) := by
  classical
  let H := conditionedOneFiberGraph d hd hm hOcard G
  let eO := occupiedWithinEigenvalue d (Fintype.card A)
  let eA := otherWithinEigenvalue d (Fintype.card A)
  let k : B → ℝ := fun b ↦
    (baseFluctuation G f b + G.walk (baseFluctuation G f) b) /
      (d + 1 : ℝ)
  have hquotient : oneFiberQuotientValue d G f = 0 :=
    quotientValue_eq_zero_of_weightedMean_zero
      d hd hm hOcard G hdegree f hmean
  have hwalkO (i : O) : H.walk f (Sum.inl i) =
      eO * occupiedFluctuation f i := by
    dsimp only [H, eO]
    rw [walk_occupied_decomposition d hd hm hOcard G hdegree,
      hquotient, zero_add]
  have hwalkA (b : B) (a : A) : H.walk f (Sum.inr (b, a)) =
      k b + eA * otherFluctuation f b a := by
    dsimp only [H, k, eA]
    rw [walk_other_decomposition d hd hm hOcard G hdegree,
      hquotient, zero_add]
  have hsumO :
      (∑ i : O, (H.walk f (Sum.inl i)) ^ 2) =
        eO ^ 2 * ∑ i : O, (occupiedFluctuation f i) ^ 2 := by
    simp_rw [hwalkO]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hsumA (b : B) :
      (∑ a : A, (H.walk f (Sum.inr (b, a))) ^ 2) =
        (Fintype.card A : ℝ) * (k b) ^ 2 +
          eA ^ 2 * ∑ a : A, (otherFluctuation f b a) ^ 2 := by
    simp_rw [hwalkA]
    exact sum_sq_const_add_scaled_of_sum_zero
      (fun a : A ↦ otherFluctuation f b a)
      (sum_otherFluctuation (cardA_pos (d := d) hd hm) f b) (k b) eA
  unfold WeightedGraph.sqNorm
  change (∑ x : OneFiberVertex O B A, H.degree x * (H.walk f x) ^ 2) = _
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  dsimp only [H]
  simp_rw [conditionedOneFiberGraph_degree_occupied d hd hm hOcard G,
    conditionedOneFiberGraph_degree_other d hd hm hOcard G]
  rw [← Finset.mul_sum, hsumO]
  have hright :
      (∑ b : B, ∑ a : A,
        ((d + 1 : ℝ) * G.degree b) *
          (H.walk f (Sum.inr (b, a))) ^ 2) =
        (d + 1 : ℝ) *
          ((Fintype.card A : ℝ) * G.sqNorm k +
            eA ^ 2 * ∑ b : B, G.degree b *
              ∑ a : A, (otherFluctuation f b a) ^ 2) := by
    calc
      _ = (d + 1 : ℝ) *
          (∑ b : B, G.degree b *
            ∑ a : A, (H.walk f (Sum.inr (b, a))) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _hb
            calc
              ∑ a : A, (d + 1 : ℝ) * G.degree b *
                    (H.walk f (Sum.inr (b, a))) ^ 2 =
                  ∑ a : A, (d + 1 : ℝ) *
                    (G.degree b * (H.walk f (Sum.inr (b, a))) ^ 2) := by
                      apply Finset.sum_congr rfl
                      intro a _ha
                      ring
              _ = (d + 1 : ℝ) *
                    ∑ a : A, G.degree b *
                      (H.walk f (Sum.inr (b, a))) ^ 2 :=
                    (Finset.mul_sum _ _ _).symm
              _ = (d + 1 : ℝ) *
                    (G.degree b *
                      ∑ a : A, (H.walk f (Sum.inr (b, a))) ^ 2) := by
                    apply congrArg ((d + 1 : ℝ) * ·)
                    exact (Finset.mul_sum _ _ _).symm
      _ = (d + 1 : ℝ) *
          (∑ b : B, G.degree b *
            ((Fintype.card A : ℝ) * (k b) ^ 2 +
              eA ^ 2 * ∑ a : A, (otherFluctuation f b a) ^ 2)) := by
            simp_rw [hsumA]
      _ = (d + 1 : ℝ) *
          ((Fintype.card A : ℝ) * G.sqNorm k +
            eA ^ 2 * ∑ b : B, G.degree b *
              ∑ a : A, (otherFluctuation f b a) ^ 2) := by
            apply congrArg ((d + 1 : ℝ) * ·)
            unfold WeightedGraph.sqNorm
            rw [Finset.mul_sum, Finset.mul_sum,
              ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro b _hb
            ring
  rw [hright]
  rfl

/-- Dropping the two nonnegative quotient-coordinate energies gives the
component energy used to bound the output. -/
theorem oneFiber_componentEnergy_le_sqNorm [Nonempty B]
    (hdegree : ∀ b, 0 < G.degree b)
    (f : OneFiberVertex O B A → ℝ) :
    ((d + 1 : ℝ) * (Fintype.card A : ℝ) * (d - 1 : ℝ) *
        graphVolume G / (2 * (Fintype.card O : ℝ))) *
        (∑ i : O, (occupiedFluctuation f i) ^ 2) +
      (d + 1 : ℝ) *
        ((Fintype.card A : ℝ) * G.sqNorm (baseFluctuation G f) +
          ∑ b : B, G.degree b *
            ∑ a : A, (otherFluctuation f b a) ^ 2) ≤
      (conditionedOneFiberGraph d hd hm hOcard G).sqNorm f := by
  rw [conditionedOneFiberGraph_sqNorm_decomposition
    d hd hm hOcard G hdegree f]
  have hcoefficient :
      0 ≤ (d + 1 : ℝ) * (Fintype.card A : ℝ) * (d - 1 : ℝ) *
        graphVolume G / (2 * (Fintype.card O : ℝ)) := by
    have hvol : 0 ≤ graphVolume G :=
      Finset.sum_nonneg fun b _hb ↦ G.degree_nonneg b
    have hOreal : (0 : ℝ) < Fintype.card O := by
      exact_mod_cast (cardO_pos (A := A) d hd hm hOcard)
    have hdminus : (0 : ℝ) ≤ (d : ℝ) - 1 := by
      have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
      linarith
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) (by positivity)) hdminus) hvol)
      (by positivity)
  have houter : 0 ≤ (d + 1 : ℝ) := by positivity
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hcoefficient
    have hmeanSq :
        0 ≤ (Fintype.card O : ℝ) * (occupiedAverage f) ^ 2 := by
      positivity
    linarith
  · apply mul_le_mul_of_nonneg_left _ houter
    apply add_le_add_left
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hmeanSq :
        0 ≤ graphVolume G * (allOtherAverage G f) ^ 2 := by
      have hvol : 0 ≤ graphVolume G :=
        Finset.sum_nonneg fun b _hb ↦ G.degree_nonneg b
      positivity
    linarith

/-- Each orthogonal output component is contracted by `1/d`; hence their
sum is bounded by `1/d²` times the corresponding input component energy. -/
theorem oneFiber_walk_sqNorm_le_componentEnergy [Nonempty B]
    (hdegree : ∀ b, 0 < G.degree b)
    (hbase : G.TwoSidedSpectralBound (1 / (d : ℝ)))
    (f : OneFiberVertex O B A → ℝ)
    (hmean : (conditionedOneFiberGraph d hd hm hOcard G).weightedMean f = 0) :
    (conditionedOneFiberGraph d hd hm hOcard G).sqNorm
        ((conditionedOneFiberGraph d hd hm hOcard G).walk f) ≤
      (1 / (d : ℝ)) ^ 2 *
        (((d + 1 : ℝ) * (Fintype.card A : ℝ) * (d - 1 : ℝ) *
            graphVolume G / (2 * (Fintype.card O : ℝ))) *
            (∑ i : O, (occupiedFluctuation f i) ^ 2) +
          (d + 1 : ℝ) *
            ((Fintype.card A : ℝ) * G.sqNorm (baseFluctuation G f) +
              ∑ b : B, G.degree b *
                ∑ a : A, (otherFluctuation f b a) ^ 2)) := by
  rw [conditionedOneFiberGraph_walk_sqNorm_of_mean_zero
    d hd hm hOcard G hdegree f hmean]
  let r : ℝ := 1 / (d : ℝ)
  let D : ℝ :=
    (d + 1 : ℝ) * (Fintype.card A : ℝ) * (d - 1 : ℝ) *
      graphVolume G / (2 * (Fintype.card O : ℝ))
  let U : ℝ := ∑ i : O, (occupiedFluctuation f i) ^ 2
  let W : ℝ := ∑ b : B, G.degree b *
    ∑ a : A, (otherFluctuation f b a) ^ 2
  let g : B → ℝ := baseFluctuation G f
  let k : B → ℝ := fun b ↦
    (g b + G.walk g b) / (d + 1 : ℝ)
  let eO := occupiedWithinEigenvalue d (Fintype.card A)
  let eA := otherWithinEigenvalue d (Fintype.card A)
  have hD : 0 ≤ D := by
    dsimp only [D]
    have hvol : 0 ≤ graphVolume G :=
      Finset.sum_nonneg fun b _hb ↦ G.degree_nonneg b
    have hOreal : (0 : ℝ) < Fintype.card O := by
      exact_mod_cast (cardO_pos (A := A) d hd hm hOcard)
    have hdminus : (0 : ℝ) ≤ (d : ℝ) - 1 := by
      have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
      linarith
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) (by positivity)) hdminus) hvol)
      (by positivity)
  have hU : 0 ≤ U := by
    dsimp only [U]
    exact Finset.sum_nonneg fun i _hi ↦ sq_nonneg _
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact Finset.sum_nonneg fun b _hb ↦
      mul_nonneg (G.degree_nonneg b)
        (Finset.sum_nonneg fun a _ha ↦ sq_nonneg _)
  have heO : eO ^ 2 ≤ r ^ 2 := by
    dsimp only [eO, r]
    exact occupiedWithinEigenvalue_sq_le
      (d := d) (A := A) hd hm
  have heA : eA ^ 2 ≤ r ^ 2 := by
    dsimp only [eA, r]
    exact otherWithinEigenvalue_sq_le
      (d := d) (A := A) hd hm
  have hk : G.sqNorm k ≤ r ^ 2 * G.sqNorm g := by
    dsimp only [k, r, g]
    exact baseFluctuation_transform_sqNorm_bound
      (d := d) (G := G) hd hdegree hbase f
  change D * (eO ^ 2 * U) +
      (d + 1 : ℝ) *
        ((Fintype.card A : ℝ) * G.sqNorm k + eA ^ 2 * W) ≤
    r ^ 2 *
      (D * U + (d + 1 : ℝ) *
        ((Fintype.card A : ℝ) * G.sqNorm g + W))
  calc
    D * (eO ^ 2 * U) +
        (d + 1 : ℝ) *
          ((Fintype.card A : ℝ) * G.sqNorm k + eA ^ 2 * W) ≤
      D * (r ^ 2 * U) +
        (d + 1 : ℝ) *
          ((Fintype.card A : ℝ) * (r ^ 2 * G.sqNorm g) +
            r ^ 2 * W) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right heO hU) hD
              · apply mul_le_mul_of_nonneg_left _ (by positivity)
                apply add_le_add
                · exact mul_le_mul_of_nonneg_left hk (by positivity)
                · exact mul_le_mul_of_nonneg_right heA hW
    _ = r ^ 2 *
        (D * U + (d + 1 : ℝ) *
          ((Fintype.card A : ℝ) * G.sqNorm g + W)) := by ring

/-- Complete two-sided spectral estimate for the canonical conditioned link
whose fixed face occupies exactly one base fiber.  The proof applies the
orthogonal decomposition to an arbitrary mean-zero function, so it does not
rely on a diagonalizability or eigenbasis completeness assumption. -/
theorem conditionedOneFiberGraph_twoSidedSpectralBound [Nonempty B]
    (hdegree : ∀ b, 0 < G.degree b)
    (hbase : G.TwoSidedSpectralBound (1 / (d : ℝ))) :
    (conditionedOneFiberGraph d hd hm hOcard G).TwoSidedSpectralBound
      (1 / (d : ℝ)) := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  refine ⟨(one_div_pos.mpr hdreal).le, ?_⟩
  intro f hmean
  calc
    (conditionedOneFiberGraph d hd hm hOcard G).sqNorm
        ((conditionedOneFiberGraph d hd hm hOcard G).walk f) ≤
      (1 / (d : ℝ)) ^ 2 *
        (((d + 1 : ℝ) * (Fintype.card A : ℝ) * (d - 1 : ℝ) *
            graphVolume G / (2 * (Fintype.card O : ℝ))) *
            (∑ i : O, (occupiedFluctuation f i) ^ 2) +
          (d + 1 : ℝ) *
            ((Fintype.card A : ℝ) * G.sqNorm (baseFluctuation G f) +
              ∑ b : B, G.degree b *
                ∑ a : A, (otherFluctuation f b a) ^ 2)) :=
      oneFiber_walk_sqNorm_le_componentEnergy
        d hd hm hOcard G hdegree hbase f hmean
    _ ≤ (1 / (d : ℝ)) ^ 2 *
        (conditionedOneFiberGraph d hd hm hOcard G).sqNorm f :=
      mul_le_mul_of_nonneg_left
        (oneFiber_componentEnergy_le_sqNorm
          d hd hm hOcard G hdegree f) (sq_nonneg _)
end DegreeAndWalk

/-! ## Transport to a concrete conditioned link -/

/-- A compact certificate identifying an arbitrary finite weighted graph with
the canonical one-occupied-fiber model, up to a positive common edge scale
and a relabeling.  This is the interface used by the concrete link-weight
calculation. -/
structure OneFiberLinkCertificate
    {V : Type*} [Fintype V] [DecidableEq V]
    {O : Type*} [Fintype O] [DecidableEq O]
    {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    {A : Type*} [Fintype A] [DecidableEq A]
    (H : WeightedGraph V) (d : ℕ) (G : WeightedGraph B) where
  dimension_ge_three : 3 ≤ d
  fiber_size : 2 * d ≤ Fintype.card A
  occupied_card : Fintype.card O + d = Fintype.card A + 1
  enumerate : V ≃ OneFiberVertex O B A
  commonScale : ℝ
  commonScale_pos : 0 < commonScale
  relabel_eq :
    H = ((conditionedOneFiberGraph d dimension_ge_three fiber_size
      occupied_card G).scale commonScale commonScale_pos.le).relabel
        enumerate.symm

/-- The canonical direct `L²` estimate transports through any one-fiber
link certificate. -/
theorem OneFiberLinkCertificate.twoSidedSpectralBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {O : Type*} [Fintype O] [DecidableEq O]
    {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    {A : Type*} [Fintype A] [DecidableEq A]
    {H : WeightedGraph V} {d : ℕ} {G : WeightedGraph B}
    (certificate : OneFiberLinkCertificate
      (O := O) (B := B) (A := A) H d G)
    (hdegree : ∀ b, 0 < G.degree b)
    (hbase : G.TwoSidedSpectralBound (1 / (d : ℝ))) :
    H.TwoSidedSpectralBound (1 / (d : ℝ)) := by
  have hmodel := conditionedOneFiberGraph_twoSidedSpectralBound
    d certificate.dimension_ge_three certificate.fiber_size
    certificate.occupied_card G hdegree hbase
  have hscaled := WeightedGraph.twoSidedSpectralBound_scale
    (conditionedOneFiberGraph d certificate.dimension_ge_three
      certificate.fiber_size certificate.occupied_card G)
    certificate.commonScale certificate.commonScale_pos hmodel
  rw [certificate.relabel_eq]
  exact WeightedGraph.twoSidedSpectralBound_relabel _
    certificate.enumerate.symm hscaled

end WeightedLift

end HDXLean
