import HDXLean.WeightedLiftParentSums

/-!
# Occupancy under insertion of fresh lifted vertices

These elementary identities are the bookkeeping step behind the cancellation
`g_m(t+1)/g_m(t) = t/(m-t)` in every conditioned-link calculation.
-/

namespace HDXLean

namespace WeightedLift

variable {Gamma A : Type*}
  [Fintype Gamma] [DecidableEq Gamma]
  [Fintype A] [DecidableEq A]

/-- Adding one fresh lifted vertex increments exactly its base fiber's
occupancy. -/
theorem occupancy_insert_of_notMem
    (F : Finset (Gamma × A)) (z : Gamma × A) (hz : z ∉ F) (x : Gamma) :
    occupancy (insert z F) x = occupancy F x + if z.1 = x then 1 else 0 := by
  classical
  unfold occupancy
  by_cases hzx : z.1 = x
  · subst x
    have hfilter :
        Finset.univ.filter (fun a : A ↦ (z.1, a) ∈ insert z F) =
          insert z.2 (Finset.univ.filter fun a : A ↦ (z.1, a) ∈ F) := by
      ext a
      simp [Prod.ext_iff]
    rw [hfilter, Finset.card_insert_of_notMem]
    · simp
    · simpa using hz
  · have hfilter :
        Finset.univ.filter (fun a : A ↦ (x, a) ∈ insert z F) =
          Finset.univ.filter (fun a : A ↦ (x, a) ∈ F) := by
      ext a
      simp [Prod.ext_iff, hzx, Ne.symm hzx]
    rw [hfilter, if_neg hzx]
    simp

/-- Adding two fresh, distinct link vertices increments occupancy by the two
corresponding fiber indicators. -/
theorem occupancy_insert_insert
    (F : Finset (Gamma × A)) (u v : Gamma × A)
    (hu : u ∉ F) (hv : v ∉ F) (huv : u ≠ v) (x : Gamma) :
    occupancy (insert v (insert u F)) x =
      occupancy F x + (if u.1 = x then 1 else 0) +
        (if v.1 = x then 1 else 0) := by
  rw [occupancy_insert_of_notMem]
  · rw [occupancy_insert_of_notMem F u hu]
  · simp [hv, Ne.symm huv]

/-- A fresh label witnesses that its fiber was not full before insertion. -/
theorem occupancy_lt_card_of_notMem
    (F : Finset (Gamma × A)) (x : Gamma) (a : A) (ha : (x, a) ∉ F) :
    occupancy F x < Fintype.card A := by
  have hbound := occupancy_le_card (insert (x, a) F) x
  rw [occupancy_insert_of_notMem F (x, a) ha x] at hbound
  simp only [ite_true] at hbound
  omega

/-- Projection support commutes with insertion. -/
@[simp]
theorem projectionSupport_insert
    (F : Finset (Gamma × A)) (z : Gamma × A) :
    projectionSupport (insert z F) = insert z.1 (projectionSupport F) := by
  simp [projectionSupport]

/-- Inserting a vertex over an already occupied base point does not change
the projection support. -/
theorem projectionSupport_insert_eq
    (F : Finset (Gamma × A)) (z : Gamma × A)
    (hz : z.1 ∈ projectionSupport F) :
    projectionSupport (insert z F) = projectionSupport F := by
  ext x
  simp only [mem_projectionSupport]
  constructor
  · rintro ⟨a, ha⟩
    rcases Finset.mem_insert.mp ha with hza | ha
    · subst hza
      exact mem_projectionSupport.mp hz
    · exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Finset.mem_insert_of_mem ha⟩

/-- Inserting two vertices over already occupied base points leaves the
projection support unchanged. -/
theorem projectionSupport_insert_insert_eq
    (F : Finset (Gamma × A)) (u v : Gamma × A)
    (hu : u.1 ∈ projectionSupport F) (hv : v.1 ∈ projectionSupport F) :
    projectionSupport (insert v (insert u F)) = projectionSupport F := by
  have hv' : v.1 ∈ projectionSupport (insert u F) := by
    rw [projectionSupport_insert_eq F u hu]
    exact hv
  exact (projectionSupport_insert_eq (insert u F) v hv').trans
    (projectionSupport_insert_eq F u hu)

/-- One-step form of the `g_m` cancellation identity. -/
theorem g_succ_eq_mul_ratio {m t : ℕ} (ht : 0 < t) (htm : t < m) :
    g m (t + 1) = g m t * ((t : ℝ) / ((m : ℝ) - t)) := by
  have hg : g m t ≠ 0 := (g_pos ht htm.le).ne'
  have hratio := g_succ_div_g ht htm
  apply (div_left_inj' hg).mp
  rw [hratio]
  field_simp

/-- The first occupied label in a fiber contributes `1/m`. -/
theorem g_one (m : ℕ) : g m 1 = 1 / (m : ℝ) := by
  simp [g]

/-- Inserting the first vertex over a previously unused base point adds a
single `g_m(1)=1/m` factor and leaves all old factors unchanged. -/
theorem g_product_insert_new
    (F : Finset (Gamma × A)) (x : Gamma) (a : A)
    (ha : (x, a) ∉ F) (hx : x ∉ projectionSupport F) :
    (∏ y ∈ projectionSupport (insert (x, a) F),
        g (Fintype.card A) (occupancy (insert (x, a) F) y)) =
      (1 / (Fintype.card A : ℝ)) *
        ∏ y ∈ projectionSupport F,
          g (Fintype.card A) (occupancy F y) := by
  classical
  rw [projectionSupport_insert, Finset.prod_insert hx]
  have hmain : occupancy (insert (x, a) F) x = 1 := by
    rw [occupancy_insert_of_notMem F (x, a) ha x]
    simp only [ite_true]
    have hzero : occupancy F x = 0 := by
      unfold occupancy
      apply Finset.card_eq_zero.mpr
      exact (by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro b hb
        exact hx (mem_projectionSupport.mpr
          ⟨b, (Finset.mem_filter.mp hb).2⟩))
    omega
  rw [hmain, g_one]
  congr 1
  apply Finset.prod_congr rfl
  intro y hy
  have hyx : x ≠ y := by
    intro hxy
    subst y
    exact hx hy
  rw [occupancy_insert_of_notMem F (x, a) ha y]
  simp [hyx]

/-- The product of all occupied-fiber factors after inserting one unused
label into an already occupied fiber. -/
theorem g_product_insert_existing
    (F : Finset (Gamma × A)) (x : Gamma) (a : A)
    (ha : (x, a) ∉ F) (hx : x ∈ projectionSupport F) :
    (∏ y ∈ projectionSupport F,
        g (Fintype.card A) (occupancy (insert (x, a) F) y)) =
      ((occupancy F x : ℝ) /
          ((Fintype.card A : ℝ) - occupancy F x)) *
        ∏ y ∈ projectionSupport F,
          g (Fintype.card A) (occupancy F y) := by
  classical
  let S := projectionSupport F
  have hpos : 0 < occupancy F x :=
    (occupancy_pos_iff F x).mpr (mem_projectionSupport.mp hx)
  have hlt : occupancy F x < Fintype.card A :=
    occupancy_lt_card_of_notMem F x a ha
  have hmain : occupancy (insert (x, a) F) x = occupancy F x + 1 := by
    rw [occupancy_insert_of_notMem F (x, a) ha x]
    simp
  have hother : ∀ y ∈ S \ {x},
      occupancy (insert (x, a) F) y = occupancy F y := by
    intro y hy
    have hyx : y ≠ x := by
      have hnot : y ∉ ({x} : Finset Gamma) := (Finset.mem_sdiff.mp hy).2
      simpa using hnot
    rw [occupancy_insert_of_notMem F (x, a) ha y]
    simp [Ne.symm hyx]
  have hprod :
      (∏ y ∈ S \ {x},
          g (Fintype.card A) (occupancy (insert (x, a) F) y)) =
        ∏ y ∈ S \ {x}, g (Fintype.card A) (occupancy F y) := by
    apply Finset.prod_congr rfl
    intro y hy
    rw [hother y hy]
  change (∏ y ∈ S, g (Fintype.card A) (occupancy (insert (x, a) F) y)) = _
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hx,
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hx, hmain,
    g_succ_eq_mul_ratio hpos hlt, hprod]
  ring

/-- Two fresh insertions over occupied base points give the two successive
`g_m` cancellation ratios.  This statement deliberately keeps the second
occupancy in its sequential form, so it covers both equal and distinct base
fibers without a case split. -/
theorem g_product_insert_insert_existing
    (F : Finset (Gamma × A)) (u v : Gamma × A)
    (hu : u ∉ F) (hv : v ∉ F) (huv : u ≠ v)
    (huSupport : u.1 ∈ projectionSupport F)
    (hvSupport : v.1 ∈ projectionSupport F) :
    (∏ y ∈ projectionSupport F,
        g (Fintype.card A) (occupancy (insert v (insert u F)) y)) =
      ((occupancy (insert u F) v.1 : ℝ) /
          ((Fintype.card A : ℝ) - occupancy (insert u F) v.1)) *
        ((occupancy F u.1 : ℝ) /
          ((Fintype.card A : ℝ) - occupancy F u.1)) *
        ∏ y ∈ projectionSupport F,
          g (Fintype.card A) (occupancy F y) := by
  have hvFresh : v ∉ insert u F := by
    simp [hv, Ne.symm huv]
  have hsupportU :
      projectionSupport (insert u F) = projectionSupport F :=
    projectionSupport_insert_eq F u huSupport
  have hvSupport' : v.1 ∈ projectionSupport (insert u F) := by
    rw [hsupportU]
    exact hvSupport
  have hsecond := g_product_insert_existing (insert u F) v.1 v.2
    hvFresh hvSupport'
  rw [hsupportU] at hsecond
  rw [hsecond, g_product_insert_existing F u.1 u.2 hu huSupport]
  ring

/-- The sequential ratio in the preceding theorem is the familiar same-fiber
or cross-fiber expression.  Keeping denominators as real differences makes
this identity independent of any chosen enumeration of the fibers. -/
theorem sequential_occupancy_ratio_eq
    (F : Finset (Gamma × A)) (u v : Gamma × A)
    (hu : u ∉ F) :
    ((occupancy (insert u F) v.1 : ℝ) /
          ((Fintype.card A : ℝ) - occupancy (insert u F) v.1)) *
        ((occupancy F u.1 : ℝ) /
          ((Fintype.card A : ℝ) - occupancy F u.1)) =
      if u.1 = v.1 then
        ((occupancy F u.1 : ℝ) * (occupancy F u.1 + 1 : ℕ)) /
          (((Fintype.card A : ℝ) - occupancy F u.1) *
            ((Fintype.card A : ℝ) - occupancy F u.1 - 1))
      else
        ((occupancy F u.1 : ℝ) * (occupancy F v.1 : ℝ)) /
          (((Fintype.card A : ℝ) - occupancy F u.1) *
            ((Fintype.card A : ℝ) - occupancy F v.1)) := by
  rw [occupancy_insert_of_notMem F u hu v.1]
  by_cases hsame : u.1 = v.1
  · rw [if_pos hsame, if_pos hsame]
    rw [hsame]
    push_cast
    rw [div_mul_div_comm]
    congr 1 <;> ring
  · rw [if_neg hsame, if_neg hsame]
    push_cast
    rw [div_mul_div_comm]
    congr 1 <;> ring

/-- Rewrite a real-valued unused-label denominator from a fiber-capacity
identity. -/
theorem cast_card_sub_occupancy_eq {m a n : ℕ} (hcapacity : a + n = m) :
    (m : ℝ) - a = n := by
  have hreal : (a : ℝ) + (n : ℝ) = (m : ℝ) := by
    exact_mod_cast hcapacity
  linarith

/-- The corresponding denominator after one unused label has been chosen. -/
theorem cast_card_sub_occupancy_sub_one_eq {m a n : ℕ}
    (hcapacity : a + n = m) (hn : 1 ≤ n) :
    (m : ℝ) - a - 1 = (n - 1 : ℕ) := by
  rw [cast_card_sub_occupancy_eq hcapacity]
  have hnEq : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hreal : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast hnEq
  linarith

/-- Two insertions into the same occupied fiber give the product of the two
successive cancellation ratios. -/
theorem g_add_two_eq_mul_ratio {m t : ℕ}
    (ht : 0 < t) (htm : t + 1 < m) :
    g m (t + 2) = g m t *
      ((t : ℝ) * (t + 1 : ℕ) /
        (((m : ℝ) - t) * ((m : ℝ) - t - 1))) := by
  rw [show t + 2 = (t + 1) + 1 by omega,
    g_succ_eq_mul_ratio (by omega) htm,
    g_succ_eq_mul_ratio ht (by omega)]
  have htLe : t ≤ m := by omega
  have hcast : ((m - (t + 1) : ℕ) : ℝ) = (m : ℝ) - t - 1 := by
    rw [Nat.cast_sub (by omega : t + 1 ≤ m)]
    push_cast
    ring
  rw [show (m : ℝ) - (t + 1 : ℕ) = (m : ℝ) - t - 1 by
    push_cast
    ring]
  have hfirst : (m : ℝ) - t ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (by exact_mod_cast (by omega : t < m)))
  have hsecond : (m : ℝ) - t - 1 ≠ 0 := by
    have : (t : ℝ) + 1 < m := by exact_mod_cast htm
    linarith
  field_simp [hfirst, hsecond]
  <;> ring

end WeightedLift

end HDXLean
