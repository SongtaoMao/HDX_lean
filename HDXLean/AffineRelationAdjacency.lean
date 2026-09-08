import HDXLean.AffineRelationCombinatorics
import HDXLean.AffineRelationSpectrum

/-!
# Adjacency formula for the affine relation graph

This file identifies the off-diagonal counting-Gram entries of the concrete
relation matrix.  Two columns with distinct field coordinates are adjacent
exactly when their secant vector is a nonzero scalar multiple of a chosen
projective direction.  The scalar and projective direction are unique.
-/

namespace HDXLean

namespace AffineRelation

universe u v

set_option linter.unusedSectionVars false

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
  [CharP F 2] [Algebra F₂ F]
variable {t : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- A vector lies on one of the selected punctured projective lines. -/
def IsScaledDirection (D : DirectionSet F t ι)
    (v : CoordinateSpace F t) : Prop :=
  ∃ i : ι, ∃ s : Fˣ, v = (s : F) • D.representative i

noncomputable instance isScaledDirectionDecidable
    (D : DirectionSet F t ι) (v : CoordinateSpace F t) :
    Decidable (IsScaledDirection D v) :=
  Classical.propDecidable _

/-- The secant direction determined by columns `(p,x)` and `(r,y)`.
It is used only when `p ≠ r`. -/
def secantDirection (p r : Fˣ) (x y : CoordinateSpace F t) :
    CoordinateSpace F t :=
  (((r : F) - (p : F))⁻¹) • (y - x)

omit [Fintype F] [CharP F 2] [Algebra F₂ F] [DecidableEq ι] in
theorem secantDirection_scaled_back {p r : Fˣ} (hpr : p ≠ r)
    (x y : CoordinateSpace F t) :
    ((r : F) - (p : F)) • secantDirection p r x y = y - x := by
  have hscalar : (r : F) - (p : F) ≠ 0 := by
    exact sub_ne_zero.mpr fun h ↦ hpr (Units.ext h.symm)
  simp [secantDirection, smul_smul, hscalar]

/-- Endpoint obtained by moving from `(p,x)` along a selected scaled
direction to the fibre indexed by `r`. -/
def neighborEndpoint (D : DirectionSet F t ι) (p r : Fˣ)
    (x : CoordinateSpace F t) (z : ι × Fˣ) : CoordinateSpace F t :=
  x + ((r : F) - (p : F)) •
    ((z.2 : F) • D.representative z.1)

omit [Fintype F] [CharP F 2] [Algebra F₂ F] [DecidableEq ι] in
/-- The secant vector to a parameterized endpoint is the selected scaled
direction itself. -/
theorem secantDirection_neighborEndpoint (D : DirectionSet F t ι)
    (p r : Fˣ) (x : CoordinateSpace F t) (z : ι × Fˣ)
    (hpr : p ≠ r) :
    secantDirection p r x (neighborEndpoint D p r x z) =
      (z.2 : F) • D.representative z.1 := by
  have hscalar : (r : F) - (p : F) ≠ 0 := by
    exact sub_ne_zero.mpr fun h ↦ hpr (Units.ext h.symm)
  simp [secantDirection, neighborEndpoint, smul_smul, hscalar]

omit [Fintype F] [CharP F 2] [Algebra F₂ F] in
/-- Distinct scaled projective directions give distinct endpoints in every
other field fibre. -/
theorem neighborEndpoint_injective (D : DirectionSet F t ι)
    (p r : Fˣ) (x : CoordinateSpace F t) (hpr : p ≠ r) :
    Function.Injective (neighborEndpoint D p r x) := by
  intro z w heq
  have hscalar : (r : F) - (p : F) ≠ 0 := by
    exact sub_ne_zero.mpr fun h ↦ hpr (Units.ext h.symm)
  have hsmul :
      ((r : F) - (p : F)) • ((z.2 : F) • D.representative z.1) =
      ((r : F) - (p : F)) • ((w.2 : F) • D.representative w.1) := by
    exact add_left_cancel heq
  have hvector : (z.2 : F) • D.representative z.1 =
      (w.2 : F) • D.representative w.1 := by
    have hinverse := congrArg
      (fun a : CoordinateSpace F t ↦
        (((r : F) - (p : F))⁻¹) • a) hsmul
    simpa [smul_smul, hscalar] using hinverse
  exact directionVector_index_injective D hvector

omit [Algebra F₂ F] in
/-- The scaled-secant predicate is precisely the range of the endpoint
parameterization. -/
theorem isScaledDirection_secant_iff_exists_endpoint
    (D : DirectionSet F t ι) (p r : Fˣ)
    (x y : CoordinateSpace F t) (hpr : p ≠ r) :
    IsScaledDirection D (secantDirection p r x y) ↔
      ∃ z : ι × Fˣ, neighborEndpoint D p r x z = y := by
  constructor
  · rintro ⟨i, s, hs⟩
    refine ⟨(i, s), ?_⟩
    have hback := secantDirection_scaled_back hpr x y
    rw [hs] at hback
    rw [neighborEndpoint, hback]
    simp [sub_eq_add_neg]
  · rintro ⟨z, hzy⟩
    refine ⟨z.1, z.2, ?_⟩
    rw [← hzy]
    exact secantDirection_neighborEndpoint D p r x z hpr

/-- The exact finite bijection underlying the adjacency/Fourier conversion. -/
noncomputable def neighborEndpointEquiv (D : DirectionSet F t ι)
    (p r : Fˣ) (x : CoordinateSpace F t) (hpr : p ≠ r) :
    (ι × Fˣ) ≃
      {y : CoordinateSpace F t //
        IsScaledDirection D (secantDirection p r x y)} :=
  Equiv.ofBijective
    (fun z ↦ ⟨neighborEndpoint D p r x z,
      ⟨z.1, z.2, secantDirection_neighborEndpoint D p r x z hpr⟩⟩)
    ⟨by
      intro z w h
      apply neighborEndpoint_injective D p r x hpr
      exact congrArg Subtype.val h,
    by
      intro y
      obtain ⟨z, hz⟩ :=
        (isScaledDirection_secant_iff_exists_endpoint D p r x y.1 hpr).mp y.2
      exact ⟨z, Subtype.ext hz⟩⟩

omit [Algebra F₂ F] in
/-- Summing over adjacent endpoints is exactly summing once over every
projective direction and every nonzero scalar representative. -/
theorem sum_scaled_secants_eq_sum_endpoints (D : DirectionSet F t ι)
    (p r : Fˣ) (x : CoordinateSpace F t) (hpr : p ≠ r)
    (f : CoordinateSpace F t → ℝ) :
    (∑ y : CoordinateSpace F t,
        if IsScaledDirection D (secantDirection p r x y) then f y else 0) =
      ∑ z : ι × Fˣ, f (neighborEndpoint D p r x z) := by
  classical
  calc
    (∑ y : CoordinateSpace F t,
        if IsScaledDirection D (secantDirection p r x y) then f y else 0) =
        ∑ y ∈ Finset.univ.filter
          (fun y ↦ IsScaledDirection D (secantDirection p r x y)), f y := by
            simpa using (Finset.sum_filter
              (s := (Finset.univ : Finset (CoordinateSpace F t)))
              (fun y ↦ IsScaledDirection D (secantDirection p r x y)) f).symm
    _ = ∑ y : {y : CoordinateSpace F t //
          IsScaledDirection D (secantDirection p r x y)}, f y.1 := by
      rw [← Finset.sum_subtype_eq_sum_filter]
      simp
    _ = ∑ z : ι × Fˣ, f (neighborEndpoint D p r x z) := by
      symm
      exact Fintype.sum_equiv (neighborEndpointEquiv D p r x hpr)
        (fun z ↦ f (neighborEndpoint D p r x z))
        (fun y ↦ f y.1) (fun _ ↦ rfl)

omit [Algebra F₂ F] in
/-- A row containing two columns with the same field coordinate contains the
same column twice, hence the columns are equal. -/
theorem eq_of_common_row_of_first_eq (D : DirectionSet F t ι)
    (row : RowIndex F t ι) (c d : Column F t)
    (hc : c ∈ rowEntries D row) (hd : d ∈ rowEntries D row)
    (hfirst : c.1 = d.1) : c = d := by
  classical
  obtain ⟨p, hp⟩ := (mem_rowEntries_iff D row c).mp hc
  obtain ⟨r, hr⟩ := (mem_rowEntries_iff D row d).mp hd
  have hval : p.1 = r.1 := by
    have hpunit : tripleMemberUnit row.triple p = c.1 :=
      congrArg Prod.fst hp
    have hrunit : tripleMemberUnit row.triple r = d.1 :=
      congrArg Prod.fst hr
    have hunits : tripleMemberUnit row.triple p =
        tripleMemberUnit row.triple r := hpunit.trans (hfirst.trans hrunit.symm)
    exact congrArg (fun z : Fˣ ↦ (z : F)) hunits
  have hsubtype : p = r := Subtype.ext hval
  rw [← hp, ← hr, hsubtype]

omit [Algebra F₂ F] in
/-- No relation row contains two distinct columns with the same first
coordinate. -/
theorem no_common_row_of_first_eq (D : DirectionSet F t ι)
    {c d : Column F t} (hfirst : c.1 = d.1) (hcd : c ≠ d) :
    ¬ ∃ row : RowIndex F t ι,
      c ∈ rowEntries D row ∧ d ∈ rowEntries D row := by
  rintro ⟨row, hc, hd⟩
  exact hcd (eq_of_common_row_of_first_eq D row c d hc hd hfirst)

omit [Algebra F₂ F] in
/-- A common relation row determines the secant vector. -/
theorem secantDirection_eq_directionVector (D : DirectionSet F t ι)
    (row : RowIndex F t ι) (p r : Fˣ)
    (x y : CoordinateSpace F t) (hpr : p ≠ r)
    (hc : (p, x) ∈ rowEntries D row)
    (hd : (r, y) ∈ rowEntries D row) :
    secantDirection p r x y = directionVector D row := by
  classical
  obtain ⟨p', hp'⟩ := (mem_rowEntries_iff D row (p, x)).mp hc
  obtain ⟨r', hr'⟩ := (mem_rowEntries_iff D row (r, y)).mp hd
  have hpval : p'.1 = (p : F) := by
    simpa [rowColumn] using congrArg
      (fun z : Column F t ↦ ((z.1 : Fˣ) : F)) hp'
  have hrval : r'.1 = (r : F) := by
    simpa [rowColumn] using congrArg
      (fun z : Column F t ↦ ((z.1 : Fˣ) : F)) hr'
  have hx : row.base + (p : F) • directionVector D row = x := by
    simpa only [rowColumn, hpval] using congrArg Prod.snd hp'
  have hy : row.base + (r : F) • directionVector D row = y := by
    simpa only [rowColumn, hrval] using congrArg Prod.snd hr'
  have hscalar : (r : F) - (p : F) ≠ 0 := by
    exact sub_ne_zero.mpr fun h ↦ hpr (Units.ext h.symm)
  have hdiff : y - x =
      ((r : F) - (p : F)) • directionVector D row := by
    rw [← hy, ← hx]
    ext k
    dsimp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [secantDirection, hdiff, smul_smul]
  simp [hscalar]

omit [Algebra F₂ F] in
/-- Conversely, a selected scaled secant direction constructs a relation row
containing the two columns. -/
theorem exists_common_row_of_scaled_secant (D : DirectionSet F t ι)
    (p r : Fˣ) (x y : CoordinateSpace F t) (hpr : p ≠ r)
    (hscaled : IsScaledDirection D (secantDirection p r x y)) :
    ∃ row : RowIndex F t ι,
      (p, x) ∈ rowEntries D row ∧ (r, y) ∈ rowEntries D row := by
  classical
  obtain ⟨i, s, hs⟩ := hscaled
  have hprval : (p : F) ≠ (r : F) := fun h ↦ hpr (Units.ext h)
  let ell : TripleIndex F :=
    ⟨CharTwoTriples.triple (p : F) (r : F),
      CharTwoTriples.triple_mem_family p.ne_zero r.ne_zero hprval⟩
  let z : ((ι × Fˣ) × TripleIndex F) := ((i, s), ell)
  let row : RowIndex F t ι := rowAtColumn D (p, x) z
  have hz : z ∈ columnParameters (ι := ι) (p, x) := by
    simp [columnParameters, z, triplesContaining, ell,
      CharTwoTriples.triple]
  refine ⟨row, rowAtColumn_contains D (p, x) z hz, ?_⟩
  rw [mem_rowEntries_iff]
  have hrmem : (r : F) ∈ row.triple.1 := by
    simp [row, z, ell, rowAtColumn, CharTwoTriples.triple]
  let r' : {a : F // a ∈ row.triple.1} := ⟨(r : F), hrmem⟩
  refine ⟨r', ?_⟩
  apply Prod.ext
  · apply Units.ext
    rfl
  · change x - (p : F) • ((s : F) • D.representative i) +
        (r : F) • ((s : F) • D.representative i) = y
    have hback := secantDirection_scaled_back hpr x y
    rw [hs] at hback
    ext k
    have hk := congrFun hback k
    dsimp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    linear_combination hk

omit [Algebra F₂ F] in
/-- Exact existence criterion for a common row when the first coordinates
are distinct. -/
theorem exists_common_row_iff_scaled_secant (D : DirectionSet F t ι)
    (p r : Fˣ) (x y : CoordinateSpace F t) (hpr : p ≠ r) :
    (∃ row : RowIndex F t ι,
      (p, x) ∈ rowEntries D row ∧ (r, y) ∈ rowEntries D row) ↔
      IsScaledDirection D (secantDirection p r x y) := by
  constructor
  · rintro ⟨row, hc, hd⟩
    refine ⟨row.direction, row.scale, ?_⟩
    exact (secantDirection_eq_directionVector D row p r x y hpr hc hd).trans rfl
  · exact exists_common_row_of_scaled_secant D p r x y hpr

omit [Algebra F₂ F] in
/-- A positive counting-Gram entry is the same thing as a common relation
row. -/
theorem countingGram_pos_iff_exists_common_row (D : DirectionSet F t ι)
    (c d : Column F t) :
    0 < countingGram (matrix D) c d ↔
      ∃ row : RowIndex F t ι,
        c ∈ rowEntries D row ∧ d ∈ rowEntries D row := by
  classical
  constructor
  · intro hpos
    have hnonempty :
        (Finset.univ.filter fun row : RowIndex F t ι ↦
          matrix D row c ≠ 0 ∧ matrix D row d ≠ 0).Nonempty := by
      exact Finset.card_pos.mp hpos
    obtain ⟨row, hrow⟩ := hnonempty
    have hboth := (Finset.mem_filter.mp hrow).2
    exact ⟨row, (matrix_apply_ne_zero_iff D row c).mp hboth.1,
      (matrix_apply_ne_zero_iff D row d).mp hboth.2⟩
  · rintro ⟨row, hc, hd⟩
    apply Finset.card_pos.mpr
    exact ⟨row, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (matrix_apply_ne_zero_iff D row c).mpr hc,
      (matrix_apply_ne_zero_iff D row d).mpr hd⟩⟩

omit [Algebra F₂ F] in
/-- Exact off-diagonal counting-Gram entry. -/
theorem countingGram_eq_indicator_of_first_ne (D : DirectionSet F t ι)
    (p r : Fˣ) (x y : CoordinateSpace F t) (hpr : p ≠ r) :
    countingGram (matrix D) (p, x) (r, y) =
      if IsScaledDirection D (secantDirection p r x y) then 1 else 0 := by
  classical
  have hcolumns : (p, x) ≠ (r, y) := fun h ↦ hpr (congrArg Prod.fst h)
  have hle := pairMultiplicityAtMostOne D (p, x) (r, y) hcolumns
  by_cases hscaled : IsScaledDirection D (secantDirection p r x y)
  · rw [if_pos hscaled]
    have hpos : 0 < countingGram (matrix D) (p, x) (r, y) :=
      (countingGram_pos_iff_exists_common_row D _ _).mpr
        ((exists_common_row_iff_scaled_secant D p r x y hpr).mpr hscaled)
    omega
  · rw [if_neg hscaled]
    apply Nat.eq_zero_of_not_pos
    intro hpos
    apply hscaled
    exact (exists_common_row_iff_scaled_secant D p r x y hpr).mp
      ((countingGram_pos_iff_exists_common_row D _ _).mp hpos)

omit [Algebra F₂ F] in
/-- If distinct columns have the same field coordinate, their counting-Gram
entry is zero. -/
theorem countingGram_eq_zero_of_first_eq (D : DirectionSet F t ι)
    (c d : Column F t) (hfirst : c.1 = d.1) (hcd : c ≠ d) :
    countingGram (matrix D) c d = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  exact no_common_row_of_first_eq D hfirst hcd
    ((countingGram_pos_iff_exists_common_row D c d).mp hpos)

omit [Algebra F₂ F] in
/-- Entrywise adjacency formula for the concrete counting-Gram graph.  This
also handles equal columns: the graph definition deletes the diagonal. -/
theorem gramGraph_weight_eq_indicator (D : DirectionSet F t ι)
    (p r : Fˣ) (x y : CoordinateSpace F t) :
    (gramGraph (matrix D)).weight (p, x) (r, y) =
      if p = r then 0
      else if IsScaledDirection D (secantDirection p r x y) then 1 else 0 := by
  classical
  by_cases hpr : p = r
  · rw [if_pos hpr]
    subst r
    by_cases hxy : x = y
    · subst y
      simp [gramGraph]
    · have hcolumns : (p, x) ≠ (p, y) := fun h ↦ hxy (congrArg Prod.snd h)
      simp only [gramGraph, hcolumns, if_false]
      rw [countingGram_eq_zero_of_first_eq D (p, x) (p, y) rfl hcolumns]
      norm_num
  · rw [if_neg hpr]
    have hcolumns : (p, x) ≠ (r, y) := fun h ↦ hpr (congrArg Prod.fst h)
    simp only [gramGraph, hcolumns, if_false]
    rw [countingGram_eq_indicator_of_first_ne D p r x y hpr]
    by_cases hscaled : IsScaledDirection D (secantDirection p r x y) <;>
      simp [hscaled]

omit [Algebra F₂ F] in
/-- Exact unnormalized adjacency-operator formula.  For every target field
coordinate distinct from `p`, the neighbours are parameterized without
repetition by a chosen projective direction and a nonzero scalar.  This is
the combinatorial change of variables used before Fourier transforming the
base-point coordinate in Lemma 3.7. -/
theorem gramGraph_neighborSum (D : DirectionSet F t ι)
    (p : Fˣ) (x : CoordinateSpace F t)
    (f : Column F t → ℝ) :
    (∑ c : Column F t, (gramGraph (matrix D)).weight (p, x) c * f c) =
      ∑ r : Fˣ, if p = r then 0 else
        ∑ z : ι × Fˣ, f (r, neighborEndpoint D p r x z) := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hpr : p = r
  · subst r
    simp_rw [gramGraph_weight_eq_indicator D p p x]
    simp
  · rw [if_neg hpr]
    have hsum := sum_scaled_secants_eq_sum_endpoints D p r x hpr
      (fun y ↦ f (r, y))
    simpa only [gramGraph_weight_eq_indicator, hpr, if_false,
      ite_mul, one_mul, zero_mul] using hsum

omit [Algebra F₂ F] in
/-- The endpoint formula with the pair parameter split into the two sums
displayed in the paper. -/
theorem gramGraph_neighborSum_split (D : DirectionSet F t ι)
    (p : Fˣ) (x : CoordinateSpace F t)
    (f : Column F t → ℝ) :
    (∑ c : Column F t, (gramGraph (matrix D)).weight (p, x) c * f c) =
      ∑ r : Fˣ, if p = r then 0 else
        ∑ i : ι, ∑ s : Fˣ,
          f (r, x + ((r : F) - (p : F)) •
            ((s : F) • D.representative i)) := by
  rw [gramGraph_neighborSum D p x f]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hpr : p = r
  · simp [hpr]
  · rw [if_neg hpr, if_neg hpr, Fintype.sum_prod_type]
    rfl

/-! ## The Fourier-mode action -/

/-- Additive character on the affine base-point coordinate associated to a
linear functional. -/
def baseCharacter (input : FiniteFieldTrace.LiteratureInput F)
    (functional : CoordinateSpace F t →ₗ[F] F)
    (x : CoordinateSpace F t) : ℝ :=
  FiniteFieldTrace.signCharacter F input.trace (functional x)

/-- A pure Fourier mode, with an arbitrary amplitude on `Fˣ`. -/
def fourierMode (input : FiniteFieldTrace.LiteratureInput F)
    (functional : CoordinateSpace F t →ₗ[F] F)
    (amplitude : Fˣ → ℝ) : Column F t → ℝ :=
  fun c ↦ baseCharacter input functional c.2 * amplitude c.1

omit [CharP F 2] [Algebra F₂ F] [DecidableEq ι] in
/-- A sum over field units is the erased nonzero-field sum used in the block
calculation. -/
theorem sum_units_eq_nonzeroSum (g : F → ℝ) :
    (∑ s : Fˣ, g (s : F)) =
      AffineRelationSpectrum.nonzeroSum (F := F) g := by
  classical
  calc
    (∑ s : Fˣ, g (s : F)) = ∑ a : {a : F // a ≠ 0}, g a.1 := by
      exact Fintype.sum_equiv unitsEquivNeZero
        (fun s : Fˣ ↦ g (s : F)) (fun a ↦ g a.1) (fun _ ↦ rfl)
    _ = ∑ a ∈ (Finset.univ.filter (fun a : F ↦ a ≠ 0)), g a := by
      rw [← Finset.sum_subtype_eq_sum_filter]
      simp
    _ = AffineRelationSpectrum.nonzeroSum (F := F) g := by
      rw [Finset.filter_ne']
      rfl

/-- The character at a parameterized endpoint factors into the base-point
character and the two diagonal phases from the paper. -/
theorem baseCharacter_neighborEndpoint
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F)
    (p r : Fˣ) (x : CoordinateSpace F t) (i : ι) (s : Fˣ) :
    baseCharacter input functional
        (neighborEndpoint D p r x (i, s)) =
      baseCharacter input functional x *
        (AffineRelationSpectrum.phase input D functional i (s : F) p *
          AffineRelationSpectrum.phase input D functional i (s : F) r) := by
  simp only [baseCharacter, neighborEndpoint, map_add, LinearMap.map_smul_of_tower,
    AffineRelationSpectrum.phase]
  rw [← AffineRelationSpectrum.signCharacter_add input]
  congr 1
  rw [AffineRelationSpectrum.signCharacter_add input]
  congr 1
  simp only [smul_eq_mul]
  rw [CharTwo.sub_eq_add]
  ring

/-- Summing the character over all endpoint parameters gives the concrete
Fourier block entry. -/
theorem sum_baseCharacter_endpoints_eq_fourierGramBlock
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F)
    (p r : Fˣ) (x : CoordinateSpace F t) :
    (∑ z : ι × Fˣ,
        baseCharacter input functional (neighborEndpoint D p r x z)) =
      baseCharacter input functional x *
        AffineRelationSpectrum.fourierGramBlock input D functional p r := by
  rw [Fintype.sum_prod_type]
  simp_rw [baseCharacter_neighborEndpoint input D functional p r x]
  simp only [AffineRelationSpectrum.fourierGramBlock]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [AffineRelationSpectrum.directionContribution]
  rw [← sum_units_eq_nonzeroSum]
  change (∑ s ∈ (Finset.univ : Finset Fˣ),
      baseCharacter input functional x *
        (AffineRelationSpectrum.phase input D functional i (s : F) p *
          AffineRelationSpectrum.phase input D functional i (s : F) r)) =
    baseCharacter input functional x *
      ∑ s ∈ (Finset.univ : Finset Fˣ),
        AffineRelationSpectrum.phase input D functional i (s : F) p *
          AffineRelationSpectrum.phase input D functional i (s : F) r
  rw [Finset.mul_sum]

/-- Off the diagonal, the previous sum is exactly the Fourier adjacency-block
entry rather than merely the Gram-block entry. -/
theorem sum_baseCharacter_endpoints_eq_fourierAdjacencyBlock
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F)
    (p r : Fˣ) (x : CoordinateSpace F t) (hpr : p ≠ r) :
    (∑ z : ι × Fˣ,
        baseCharacter input functional (neighborEndpoint D p r x z)) =
      baseCharacter input functional x *
        AffineRelationSpectrum.fourierAdjacencyBlock input D functional p r := by
  rw [sum_baseCharacter_endpoints_eq_fourierGramBlock]
  simp [AffineRelationSpectrum.fourierAdjacencyBlock, hpr]

/-- The concrete counting-Gram adjacency operator preserves every Fourier
mode, and its action on the amplitude is exactly the block computed in
`AffineRelationSpectrum`.  This closes the entrywise graph-to-Fourier bridge;
only the standard completeness/isometry theorem for finite Fourier transform
is separate from this identity. -/
theorem gramGraph_mul_fourierMode
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F)
    (amplitude : Fˣ → ℝ) (p : Fˣ) (x : CoordinateSpace F t) :
    (∑ c : Column F t,
        (gramGraph (matrix D)).weight (p, x) c *
          fourierMode input functional amplitude c) =
      baseCharacter input functional x *
        Matrix.mulVec
          (AffineRelationSpectrum.fourierAdjacencyBlock input D functional)
          amplitude p := by
  rw [gramGraph_neighborSum D p x (fourierMode input functional amplitude)]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hpr : p = r
  · subst r
    rw [if_pos rfl]
    have hdiag :
        AffineRelationSpectrum.fourierAdjacencyBlock input D functional p p = 0 := by
      rw [AffineRelationSpectrum.fourierAdjacencyBlock_eq]
      simp [AffineRelationSpectrum.jMinusI]
    rw [hdiag]
    simp
  · rw [if_neg hpr]
    simp only [fourierMode]
    rw [← Finset.sum_mul]
    rw [sum_baseCharacter_endpoints_eq_fourierAdjacencyBlock
      input D functional p r x hpr]
    ring

end AffineRelation

end HDXLean
