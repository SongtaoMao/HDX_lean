import HDXLean.AffineRelation
import Mathlib.Tactic.LinearCombination

/-!
# Finite combinatorics of the affine relation matrix

This file proves the elementary uniqueness and cardinality assertions in
Lemma 3.5.  In particular, two distinct columns common to two relation rows
determine the row uniquely.  Consequently the rows are distinct and two
columns occur together in at most one row.
-/

namespace HDXLean

open scoped BigOperators

namespace AffineRelation

universe u v

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
  [CharP F 2] [Algebra F₂ F]
variable {t : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]

/-! ## Injectivity of the scaled projective-direction index -/

omit [Fintype F] [CharP F 2] [Algebra F₂ F] [DecidableEq ι] in
/-- The pair consisting of a projective direction and a nonzero scale is
recovered from its actual direction vector. -/
theorem directionVector_index_injective (D : DirectionSet F t ι) :
    Function.Injective
      (fun z : ι × Fˣ ↦ (z.2 : F) • D.representative z.1) := by
  rintro ⟨i, scale⟩ ⟨j, scale'⟩ hvector
  have hprojective :
      D.representative i =
        ((scale⁻¹ * scale' : Fˣ) : F) • D.representative j := by
    have hscaled := congrArg
      (fun a : CoordinateSpace F t ↦ ((scale⁻¹ : Fˣ) : F) • a)
      hvector
    simpa [smul_smul] using hscaled
  have hdirection : i = j :=
    D.projectivelyDistinct (Units.ne_zero (scale⁻¹ * scale')) hprojective
  subst j
  have hrepresentative : ∃ k, D.representative i k ≠ 0 := by
    by_contra h
    push Not at h
    exact D.representative_ne_zero i (funext h)
  obtain ⟨k, hk⟩ := hrepresentative
  have hcoordinate := congrFun hvector k
  have hscaleVal : (scale : F) = (scale' : F) := by
    exact mul_right_cancel₀ hk hcoordinate
  have hscale : scale = scale' := Units.ext hscaleVal
  exact Prod.ext rfl hscale

omit [CharP F 2] [Algebra F₂ F] in
/-- Row-level formulation of `directionVector_index_injective`. -/
theorem directionVector_eq_iff_index_eq (D : DirectionSet F t ι)
    (r s : RowIndex F t ι) :
    directionVector D r = directionVector D s ↔
      (r.direction, r.scale) = (s.direction, s.scale) := by
  constructor
  · intro h
    exact directionVector_index_injective D h
  · intro h
    simpa [directionVector] using congrArg
      (fun z : ι × Fˣ ↦ (z.2 : F) • D.representative z.1) h

/-! ## Membership and reconstruction -/

omit [Algebra F₂ F] in
theorem mem_rowEntries_iff (D : DirectionSet F t ι)
    (r : RowIndex F t ι) (c : Column F t) :
    c ∈ rowEntries D r ↔
      ∃ p : {z : F // z ∈ r.triple.1}, rowColumn D r p = c := by
  classical
  simp [rowEntries]

omit [Algebra F₂ F] in
/-- Two distinct columns common to two rows determine the row. -/
theorem row_eq_of_two_common_columns (D : DirectionSet F t ι)
    {r s : RowIndex F t ι} {c d : Column F t}
    (hcr : c ∈ rowEntries D r) (hdr : d ∈ rowEntries D r)
    (hcs : c ∈ rowEntries D s) (hds : d ∈ rowEntries D s)
    (hcd : c ≠ d) : r = s := by
  classical
  obtain ⟨p, hp⟩ := (mem_rowEntries_iff D r c).mp hcr
  obtain ⟨q, hq⟩ := (mem_rowEntries_iff D r d).mp hdr
  obtain ⟨p', hp'⟩ := (mem_rowEntries_iff D s c).mp hcs
  obtain ⟨q', hq'⟩ := (mem_rowEntries_iff D s d).mp hds
  have hpEq : rowColumn D r p = rowColumn D s p' := hp.trans hp'.symm
  have hqEq : rowColumn D r q = rowColumn D s q' := hq.trans hq'.symm
  have hpval : p.1 = p'.1 := by
    simpa [rowColumn] using congrArg
      (fun z : Column F t ↦ ((z.1 : Fˣ) : F)) hpEq
  have hqval : q.1 = q'.1 := by
    simpa [rowColumn] using congrArg
      (fun z : Column F t ↦ ((z.1 : Fˣ) : F)) hqEq
  have hpq : p.1 ≠ q.1 := by
    intro hpq
    apply hcd
    rw [← hp, ← hq]
    apply Prod.ext
    · apply Units.ext
      simpa [rowColumn] using hpq
    · simp only [rowColumn]
      rw [hpq]
  have hpSecond :
      r.base + p.1 • directionVector D r =
        s.base + p.1 • directionVector D s := by
    have h := congrArg Prod.snd hpEq
    simpa only [rowColumn, hpval] using h
  have hqSecond :
      r.base + q.1 • directionVector D r =
        s.base + q.1 • directionVector D s := by
    have h := congrArg Prod.snd hqEq
    simpa only [rowColumn, hqval] using h
  have hdirectionVector : directionVector D r = directionVector D s := by
    funext k
    have hpCoordinate := congrFun hpSecond k
    have hqCoordinate := congrFun hqSecond k
    have hcoefficient : p.1 - q.1 ≠ 0 := sub_ne_zero.mpr hpq
    apply mul_left_cancel₀ hcoefficient
    dsimp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hpCoordinate hqCoordinate ⊢
    linear_combination hpCoordinate - hqCoordinate
  have hindex : (r.direction, r.scale) = (s.direction, s.scale) :=
    (directionVector_eq_iff_index_eq D r s).mp hdirectionVector
  have hdirection : r.direction = s.direction := congrArg Prod.fst hindex
  have hscale : r.scale = s.scale := congrArg Prod.snd hindex
  have hpMemS : p.1 ∈ s.triple.1 := by
    rw [hpval]
    exact p'.2
  have hqMemS : q.1 ∈ s.triple.1 := by
    rw [hqval]
    exact q'.2
  have htripleVal : r.triple.1 = s.triple.1 := by
    calc
      r.triple.1 = CharTwoTriples.triple p.1 q.1 :=
        CharTwoTriples.family_eq_triple_of_pair r.triple.2 p.2 q.2 hpq
      _ = s.triple.1 :=
        (CharTwoTriples.family_eq_triple_of_pair
          s.triple.2 hpMemS hqMemS hpq).symm
  have htriple : r.triple = s.triple := Subtype.ext htripleVal
  have hbase : r.base = s.base := by
    rw [hdirectionVector] at hpSecond
    exact add_right_cancel hpSecond
  apply (rowIndexEquiv (F := F) (t := t) (ι := ι)).injective
  change (r.direction, r.scale, (r.base, r.triple)) =
    (s.direction, s.scale, (s.base, s.triple))
  rw [hdirection, hscale, hbase, htriple]

/-! ## Consequences for the incidence matrix -/

omit [Algebra F₂ F] in
/-- Distinct row indices give distinct binary incidence rows. -/
theorem rowsDistinct (D : DirectionSet F t ι) :
    RelationMatrix.RowsDistinct (matrix D) := by
  classical
  intro r s hrs
  obtain ⟨p, q, hp, hq, hpq, htriple⟩ :=
    CharTwoTriples.mem_family_iff.mp r.triple.2
  have hpMem : p ∈ r.triple.1 := by rw [← htriple]; simp
  have hqMem : q ∈ r.triple.1 := by rw [← htriple]; simp
  let p' : {z : F // z ∈ r.triple.1} := ⟨p, hpMem⟩
  let q' : {z : F // z ∈ r.triple.1} := ⟨q, hqMem⟩
  let c := rowColumn D r p'
  let d := rowColumn D r q'
  have hcr : c ∈ rowEntries D r :=
    (mem_rowEntries_iff D r c).mpr ⟨p', rfl⟩
  have hdr : d ∈ rowEntries D r :=
    (mem_rowEntries_iff D r d).mpr ⟨q', rfl⟩
  have hentries : rowEntries D r = rowEntries D s := by
    rw [← rowSupport_matrix, ← rowSupport_matrix]
    exact congrArg (fun f : Column F t → F₂ ↦
      Finset.univ.filter fun z ↦ f z ≠ 0) hrs
  have hcs : c ∈ rowEntries D s := hentries ▸ hcr
  have hds : d ∈ rowEntries D s := hentries ▸ hdr
  have hcd : c ≠ d := by
    intro h
    have hfirst := congrArg (fun z : Column F t ↦ ((z.1 : Fˣ) : F)) h
    exact hpq (by simpa [c, d, p', q', rowColumn] using hfirst)
  exact row_eq_of_two_common_columns D hcr hdr hcs hds hcd

omit [Algebra F₂ F] in
/-- No two distinct columns occur together in more than one relation row. -/
theorem pairMultiplicityAtMostOne (D : DirectionSet F t ι) :
    RelationMatrix.PairMultiplicityAtMostOne (matrix D) := by
  classical
  intro c d hcd
  rw [countingGram, Finset.card_le_one_iff]
  intro r s hr hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr hs
  exact row_eq_of_two_common_columns D
    ((matrix_apply_ne_zero_iff D r c).mp hr.1)
    ((matrix_apply_ne_zero_iff D r d).mp hr.2)
    ((matrix_apply_ne_zero_iff D s c).mp hs.1)
    ((matrix_apply_ne_zero_iff D s d).mp hs.2) hcd

/-! ## The triples through a fixed nonzero element -/

/-- Family triples containing a fixed nonzero field element. -/
def triplesContaining (p : Fˣ) : Finset (TripleIndex F) :=
  Finset.univ.filter fun ell ↦ (p : F) ∈ ell.1

/-- The possible partners of `p`: all nonzero field elements other than `p`. -/
def partners (p : Fˣ) : Finset F :=
  (Finset.univ.erase (0 : F)).erase (p : F)

/-- The family triple generated by `p` and one of its possible partners. -/
def partnerTriple (p : Fˣ) (r : F) (hr : r ∈ partners p) : TripleIndex F := by
  have hrp : r ≠ (p : F) := (Finset.mem_erase.mp hr).1
  have hrzero : r ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
  exact ⟨CharTwoTriples.triple (p : F) r,
    CharTwoTriples.triple_mem_family p.ne_zero hrzero hrp.symm⟩

omit [Algebra F₂ F] in
@[simp]
theorem partnerTriple_val (p : Fˣ) (r : F) (hr : r ∈ partners p) :
    (partnerTriple p r hr).1 = CharTwoTriples.triple (p : F) r :=
  rfl

/-- A triple through `p`, together with a choice of one of its other two
members. -/
def fixedIncidences (p : Fˣ) : Finset ((_ell : TripleIndex F) × F) :=
  (triplesContaining p).sigma fun ell ↦ ell.1.erase (p : F)

omit [Algebra F₂ F] in
/-- Each triple through `p` contributes exactly its other two members. -/
theorem card_fixedIncidences (p : Fˣ) :
    (fixedIncidences p).card = (triplesContaining p).card * 2 := by
  rw [fixedIncidences, Finset.card_sigma]
  apply Finset.sum_const_nat
  intro ell hell
  have hpell : (p : F) ∈ ell.1 := (Finset.mem_filter.mp hell).2
  rw [Finset.card_erase_of_mem hpell,
    CharTwoTriples.family_member_card ell.2]

omit [Algebra F₂ F] in
/-- The partners of `p` are in bijection with a triple through `p` plus a
choice of another member. -/
theorem card_partners_eq_card_fixedIncidences (p : Fˣ) :
    (partners p).card = (fixedIncidences p).card := by
  classical
  let forward : ∀ r ∈ partners p, ((_ell : TripleIndex F) × F) :=
    fun r hr ↦ ⟨partnerTriple p r hr, r⟩
  let backward : ∀ z ∈ fixedIncidences p, F := fun z _ ↦ z.2
  have hforward : ∀ r hr, forward r hr ∈ fixedIncidences p := by
    intro r hr
    dsimp only [forward]
    rw [fixedIncidences, Finset.mem_sigma]
    have hrp : r ≠ (p : F) := (Finset.mem_erase.mp hr).1
    exact ⟨by
      rw [triplesContaining, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simp [partnerTriple, CharTwoTriples.triple]⟩,
      Finset.mem_erase.mpr ⟨hrp, by simp [partnerTriple, CharTwoTriples.triple]⟩⟩
  have hbackward : ∀ z hz, backward z hz ∈ partners p := by
    intro z hz
    change z.2 ∈ (Finset.univ.erase (0 : F)).erase (p : F)
    have hzSigma := Finset.mem_sigma.mp (show z ∈ fixedIncidences p from hz)
    have hzOther := Finset.mem_erase.mp hzSigma.2
    have hzFamily : z.1.1 ∈ CharTwoTriples.family F := z.1.2
    have hznonzero : z.2 ≠ 0 := fun hzero ↦
      CharTwoTriples.family_member_zero_not_mem hzFamily (hzero ▸ hzOther.2)
    exact Finset.mem_erase.mpr
      ⟨hzOther.1, Finset.mem_erase.mpr ⟨hznonzero, Finset.mem_univ _⟩⟩
  have hleft : ∀ r hr,
      backward (forward r hr) (hforward r hr) = r := by
    intro r hr
    rfl
  have hright : ∀ z hz,
      forward (backward z hz) (hbackward z hz) = z := by
    intro z hz
    apply Sigma.ext
    · apply Subtype.ext
      have hzSigma := Finset.mem_sigma.mp (show z ∈ fixedIncidences p from hz)
      have hpz : (p : F) ∈ z.1.1 :=
        (Finset.mem_filter.mp hzSigma.1).2
      have hrz := (Finset.mem_erase.mp hzSigma.2).2
      have hpr : (p : F) ≠ z.2 := (Finset.mem_erase.mp hzSigma.2).1.symm
      exact (CharTwoTriples.family_eq_triple_of_pair
        z.1.2 hpz hrz hpr).symm
    · rfl
  exact Finset.card_bij' forward backward hforward hbackward hleft hright

omit [CharP F 2] [Algebra F₂ F] in
/-- There are exactly `q - 2` possible partners of a fixed nonzero element. -/
theorem card_partners (p : Fˣ) :
    (partners p).card = Fintype.card F - 2 := by
  have hpMem : (p : F) ∈ Finset.univ.erase (0 : F) := by
    simp [p.ne_zero]
  rw [partners, Finset.card_erase_of_mem hpMem,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : F)), Finset.card_univ]
  omega

omit [Algebra F₂ F] in
/-- Division-free count of the family triples containing a fixed nonzero
element.  This remains meaningful for `F = F₂`, when both sides are zero. -/
theorem triplesContaining_card_mul_two (p : Fˣ) :
    (triplesContaining p).card * 2 = Fintype.card F - 2 := by
  rw [← card_partners p, card_partners_eq_card_fixedIncidences,
    card_fixedIncidences]

omit [Algebra F₂ F] in
/-- Quotient form of the preceding exact count. -/
theorem triplesContaining_card (p : Fˣ) :
    (triplesContaining p).card = (Fintype.card F - 2) / 2 := by
  rw [← triplesContaining_card_mul_two p]
  omega

/-! ## Rows through a fixed column -/

/-- Parameters left after the base point of a row through `c` is uniquely
determined: a scaled projective direction and a triple containing `c.1`. -/
def columnParameters (c : Column F t) :
    Finset ((ι × Fˣ) × TripleIndex F) :=
  Finset.univ.product (triplesContaining c.1)

/-- Reconstruct the unique row with the prescribed direction/triple
parameters that contains `c`. -/
def rowAtColumn (D : DirectionSet F t ι) (c : Column F t)
    (z : (ι × Fˣ) × TripleIndex F) : RowIndex F t ι where
  direction := z.1.1
  scale := z.1.2
  base := c.2 - (c.1 : F) •
    ((z.1.2 : F) • D.representative z.1.1)
  triple := z.2

/-- Forget the uniquely determined base point of a row. -/
def rowParameters (r : RowIndex F t ι) :
    (ι × Fˣ) × TripleIndex F :=
  ((r.direction, r.scale), r.triple)

omit [Algebra F₂ F] in
theorem rowParameters_mem_columnParameters (D : DirectionSet F t ι)
    (c : Column F t) (r : RowIndex F t ι)
    (hc : c ∈ rowEntries D r) :
    rowParameters r ∈ columnParameters c := by
  classical
  obtain ⟨p, hp⟩ := (mem_rowEntries_iff D r c).mp hc
  have hpval : p.1 = (c.1 : F) := by
    simpa [rowColumn] using congrArg
      (fun z : Column F t ↦ ((z.1 : Fˣ) : F)) hp
  change ((r.direction, r.scale), r.triple) ∈
    ((Finset.univ : Finset (ι × Fˣ)) ×ˢ (triplesContaining c.1))
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [triplesContaining, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hpval ▸ p.2⟩

omit [Algebra F₂ F] in
theorem rowAtColumn_contains (D : DirectionSet F t ι)
    (c : Column F t) (z : (ι × Fˣ) × TripleIndex F)
    (hz : z ∈ columnParameters c) :
    c ∈ rowEntries D (rowAtColumn D c z) := by
  classical
  have hp : (c.1 : F) ∈ z.2.1 := by
    have hzTriple := (Finset.mem_product.mp
      (show z ∈ columnParameters c from hz)).2
    exact (Finset.mem_filter.mp hzTriple).2
  let p : {x : F // x ∈ (rowAtColumn D c z).triple.1} := ⟨(c.1 : F), hp⟩
  rw [mem_rowEntries_iff]
  refine ⟨p, ?_⟩
  apply Prod.ext
  · apply Units.ext
    rfl
  · dsimp only [p]
    simp [rowColumn, rowAtColumn, directionVector]

omit [Algebra F₂ F] in
theorem rowAtColumn_rowParameters (D : DirectionSet F t ι)
    (c : Column F t) (r : RowIndex F t ι)
    (hc : c ∈ rowEntries D r) :
    rowAtColumn D c (rowParameters r) = r := by
  classical
  obtain ⟨p, hp⟩ := (mem_rowEntries_iff D r c).mp hc
  have hpval : p.1 = (c.1 : F) := by
    simpa [rowColumn] using congrArg
      (fun z : Column F t ↦ ((z.1 : Fˣ) : F)) hp
  have hpSecond :
      r.base + p.1 • directionVector D r = c.2 := by
    simpa [rowColumn] using congrArg Prod.snd hp
  have hbase :
      c.2 - (c.1 : F) • directionVector D r = r.base := by
    rw [← hpval, ← hpSecond]
    exact add_sub_cancel_right _ _
  apply (rowIndexEquiv (F := F) (t := t) (ι := ι)).injective
  change (r.direction, r.scale,
      (c.2 - (c.1 : F) • directionVector D r, r.triple)) =
    (r.direction, r.scale, (r.base, r.triple))
  rw [hbase]

omit [CharP F 2] [Algebra F₂ F] in
@[simp]
theorem rowParameters_rowAtColumn (D : DirectionSet F t ι)
    (c : Column F t) (z : (ι × Fˣ) × TripleIndex F) :
    rowParameters (rowAtColumn D c z) = z := by
  rcases z with ⟨⟨i, scale⟩, ell⟩
  rfl

omit [Algebra F₂ F] in
/-- Rows containing a fixed column are in bijection with
`columnParameters`. -/
theorem columnWeight_eq_card_columnParameters
    (D : DirectionSet F t ι) (c : Column F t) :
    columnWeight (matrix D) c =
      (columnParameters (ι := ι) c).card := by
  classical
  let source := Finset.univ.filter fun r : RowIndex F t ι ↦ matrix D r c ≠ 0
  let forward : ∀ r ∈ source, ((ι × Fˣ) × TripleIndex F) :=
    fun r _ ↦ rowParameters r
  let backward : ∀ z ∈ columnParameters c, RowIndex F t ι :=
    fun z _ ↦ rowAtColumn D c z
  have hforward : ∀ r hr, forward r hr ∈ columnParameters c := by
    intro r hr
    apply rowParameters_mem_columnParameters D c r
    apply (matrix_apply_ne_zero_iff D r c).mp
    exact (Finset.mem_filter.mp hr).2
  have hbackward : ∀ z hz, backward z hz ∈ source := by
    intro z hz
    change rowAtColumn D c z ∈
      Finset.univ.filter fun r : RowIndex F t ι ↦ matrix D r c ≠ 0
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (matrix_apply_ne_zero_iff D _ c).mpr
      (rowAtColumn_contains D c z hz)⟩
  have hleft : ∀ r hr,
      backward (forward r hr) (hforward r hr) = r := by
    intro r hr
    apply rowAtColumn_rowParameters D c r
    apply (matrix_apply_ne_zero_iff D r c).mp
    exact (Finset.mem_filter.mp hr).2
  have hright : ∀ z hz,
      forward (backward z hz) (hbackward z hz) = z := by
    intro z hz
    exact rowParameters_rowAtColumn D c z
  change source.card = (columnParameters c).card
  exact Finset.card_bij' forward backward hforward hbackward hleft hright

omit [CharP F 2] [Algebra F₂ F] [DecidableEq ι] in
theorem card_columnParameters (c : Column F t) :
    (columnParameters (ι := ι) c).card =
      (Fintype.card ι * (Fintype.card F - 1)) *
        (triplesContaining c.1).card := by
  simp [columnParameters, Fintype.card_units]

omit [Algebra F₂ F] in
/-- Division-free form of the exact constant column-weight calculation in
Lemma 3.5. -/
theorem columnWeight_mul_two (D : DirectionSet F t ι)
    (c : Column F t) :
    2 * columnWeight (matrix D) c =
      (Fintype.card F - 2) *
        ((Fintype.card F - 1) * Fintype.card ι) := by
  rw [columnWeight_eq_card_columnParameters D c, card_columnParameters]
  calc
    2 * ((Fintype.card ι * (Fintype.card F - 1)) *
        (triplesContaining c.1).card) =
        (Fintype.card ι * (Fintype.card F - 1)) *
          ((triplesContaining c.1).card * 2) := by ac_rfl
    _ = (Fintype.card ι * (Fintype.card F - 1)) *
          (Fintype.card F - 2) := by
      rw [triplesContaining_card_mul_two]
    _ = (Fintype.card F - 2) *
          ((Fintype.card F - 1) * Fintype.card ι) := by ac_rfl

omit [Algebra F₂ F] in
/-- Exact column weight in the quotient notation used by the paper. -/
theorem columnWeight_eq (D : DirectionSet F t ι) (c : Column F t) :
    columnWeight (matrix D) c =
      ((Fintype.card F - 2) *
        ((Fintype.card F - 1) * Fintype.card ι)) / 2 := by
  have h := columnWeight_mul_two D c
  rw [← h]
  omega

/-- The common column weight. -/
def rho (F : Type u) [Field F] [Fintype F]
    (ι : Type v) [Fintype ι] : ℕ :=
  ((Fintype.card F - 2) *
    ((Fintype.card F - 1) * Fintype.card ι)) / 2

omit [Algebra F₂ F] in
/-- Exact division-free normalization identity.  No field-size assumption is
needed; in the degenerate field `F₂` both sides vanish. -/
theorem rho_mul_two (D : DirectionSet F t ι) :
    2 * rho F ι =
      (Fintype.card F - 2) *
        ((Fintype.card F - 1) * Fintype.card ι) := by
  let c : Column F t := (1, 0)
  calc
    2 * rho F ι = 2 * columnWeight (matrix D) c := by
      rw [columnWeight_eq D c]
      rfl
    _ = (Fintype.card F - 2) *
        ((Fintype.card F - 1) * Fintype.card ι) :=
      columnWeight_mul_two D c

omit [Algebra F₂ F] in
/-- Under the harmless nondegeneracy assumptions used in the paper (`q > 2`
and at least one direction), the exact count gives positive constant column
weight. -/
theorem constantColumnWeight (D : DirectionSet F t ι)
    (hF : 2 < Fintype.card F) (hι : Nonempty ι) :
    RelationMatrix.ConstantColumnWeight (matrix D) (rho F ι) := by
  constructor
  · unfold rho
    have hcardι : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr hι
    have hfirst : 1 ≤ Fintype.card F - 2 := by omega
    have hsecond : 2 ≤
        (Fintype.card F - 1) * Fintype.card ι := by
      have hq : 2 ≤ Fintype.card F - 1 := by omega
      calc
        2 = 2 * 1 := by omega
        _ ≤ (Fintype.card F - 1) * Fintype.card ι :=
          Nat.mul_le_mul hq hcardι
    apply Nat.div_pos
    · calc
        2 = 1 * 2 := by omega
        _ ≤ (Fintype.card F - 2) *
            ((Fintype.card F - 1) * Fintype.card ι) :=
          Nat.mul_le_mul hfirst hsecond
    · omega
  · intro c
    exact columnWeight_eq D c

/-! ## Exact cardinalities -/

omit [CharP F 2] [Algebra F₂ F] in
/-- Number of columns: `(q - 1) q^t`. -/
theorem card_column :
    Fintype.card (Column F t) =
      (Fintype.card F - 1) * Fintype.card F ^ t := by
  simp [Column, CoordinateSpace, Fintype.card_units]

omit [Algebra F₂ F] in
/-- Number of unordered characteristic-two triples. -/
theorem card_tripleIndex :
    Fintype.card (TripleIndex F) =
      ((Fintype.card F - 1) * (Fintype.card F - 2)) / 6 := by
  change Fintype.card {ell : Finset F // ell ∈ CharTwoTriples.family F} = _
  rw [Fintype.card_coe, CharTwoTriples.family_card]

omit [CharP F 2] [Algebra F₂ F] in
/-- Exact number of indexed relation rows. -/
theorem card_rowIndex_raw :
    Fintype.card (RowIndex F t ι) =
      Fintype.card ι * (Fintype.card F - 1) *
        (Fintype.card F ^ t * (CharTwoTriples.family F).card) := by
  rw [Fintype.card_congr (rowIndexEquiv (F := F) (t := t) (ι := ι))]
  simp only [Fintype.card_prod, Fintype.card_units]
  rw [show Fintype.card (CoordinateSpace F t) = Fintype.card F ^ t by
    simp [CoordinateSpace]]
  change _ * (_ * (_ * Fintype.card
    {ell : Finset F // ell ∈ CharTwoTriples.family F})) = _
  rw [Fintype.card_coe]
  ac_rfl

omit [Algebra F₂ F] in
/-- Exact number of indexed relation rows, with the triple count evaluated. -/
theorem card_rowIndex :
    Fintype.card (RowIndex F t ι) =
      Fintype.card ι * (Fintype.card F - 1) *
        (Fintype.card F ^ t *
          (((Fintype.card F - 1) * (Fintype.card F - 2)) / 6)) := by
  rw [Fintype.card_congr (rowIndexEquiv (F := F) (t := t) (ι := ι))]
  simp only [Fintype.card_prod, Fintype.card_units]
  rw [card_tripleIndex]
  rw [show Fintype.card (CoordinateSpace F t) = Fintype.card F ^ t by
    simp [CoordinateSpace]]
  ac_rfl

omit [Algebra F₂ F] in
/-- Division-free row/column incidence identity.  Its proof double-counts
the three incidences in every row and uses `rho_mul_two`; therefore no hidden
divisibility or field-size assumption is required. -/
theorem three_mul_card_rowIndex_eq_rho_mul_card_column
    (D : DirectionSet F t ι) :
    3 * Fintype.card (RowIndex F t ι) =
      rho F ι * Fintype.card (Column F t) := by
  apply Nat.mul_left_cancel (n := 2) (by omega)
  rw [card_rowIndex_raw, card_column]
  calc
    2 * (3 * (Fintype.card ι * (Fintype.card F - 1) *
        (Fintype.card F ^ t * (CharTwoTriples.family F).card))) =
        ((CharTwoTriples.family F).card * 6) *
          (Fintype.card ι * (Fintype.card F - 1) *
            Fintype.card F ^ t) := by ring
    _ = ((Fintype.card F - 1) * (Fintype.card F - 2)) *
          (Fintype.card ι * (Fintype.card F - 1) *
            Fintype.card F ^ t) := by
      rw [CharTwoTriples.family_card_mul_six]
    _ = (2 * rho F ι) *
          ((Fintype.card F - 1) * Fintype.card F ^ t) := by
      rw [rho_mul_two D]
      ac_rfl
    _ = 2 *
          (rho F ι *
            ((Fintype.card F - 1) * Fintype.card F ^ t)) := by ac_rfl

end AffineRelation

end HDXLean
