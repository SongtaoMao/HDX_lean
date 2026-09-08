import HDXLean.AffineRelation
import HDXLean.FiniteFieldTrace
import HDXLean.SpectralArithmetic

/-!
# Fourier blocks for the affine-restriction relation graph

This file formalizes the internal calculation in Lemma 3.7.  For a linear
functional `c`, Fourier transform in the affine base-point coordinate produces
a block on functions on `Fˣ`.  We compute that block entry-by-entry from the
cited additive-character orthogonality statement, prove its two exact
eigenvalues, and prove every endpoint inequality in (3.2).

The finite Fourier/linear-algebra bridge from the concrete counting-Gram graph
to these blocks is isolated in `FourierInterface`.  No conclusion is hidden in
an ambient assumption: a caller must supply this finite certificate.  In particular,
`complete` says that the displayed candidates exhaust the mean-zero spectrum,
and `one_of_disconnected` is the standard regular-graph fact used in the last
sentence of Lemma 3.7.
-/

namespace HDXLean

open scoped BigOperators

namespace AffineRelationSpectrum

universe u v

set_option linter.unusedSectionVars false

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
  [CharP F 2] [Algebra F₂ F]
variable {t : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]

/-! ## Elementary character identities -/

/-- The binary sign character turns addition into multiplication. -/
theorem signCharacter_add (input : FiniteFieldTrace.LiteratureInput F)
    (x y : F) :
    FiniteFieldTrace.signCharacter F input.trace x *
        FiniteFieldTrace.signCharacter F input.trace y =
      FiniteFieldTrace.signCharacter F input.trace (x + y) := by
  have hmap : input.trace (x + y) = input.trace x + input.trace y :=
    map_add input.trace x y
  by_cases hx : input.trace x = 0
  · by_cases hy : input.trace y = 0
    · simp [FiniteFieldTrace.signCharacter, hx, hy, hmap]
    · have hy_one : input.trace y = 1 := Fin.eq_one_of_ne_zero _ hy
      simp [FiniteFieldTrace.signCharacter, hx, hy_one, hmap]
  · have hx_one : input.trace x = 1 := Fin.eq_one_of_ne_zero _ hx
    by_cases hy : input.trace y = 0
    · simp [FiniteFieldTrace.signCharacter, hx_one, hy, hmap]
    · have hy_one : input.trace y = 1 := Fin.eq_one_of_ne_zero _ hy
      simp [FiniteFieldTrace.signCharacter, hx_one, hy_one, hmap]

/-- Every value of the sign character has square one. -/
theorem signCharacter_sq (input : FiniteFieldTrace.LiteratureInput F) (x : F) :
    FiniteFieldTrace.signCharacter F input.trace x *
        FiniteFieldTrace.signCharacter F input.trace x = 1 := by
  by_cases hx : input.trace x = 0 <;>
    simp [FiniteFieldTrace.signCharacter, hx]

/-- Sum a function over all nonzero field elements, represented as an erased
finite-field sum.  This is definitionally the sum over all scalar
representatives of a projective direction. -/
noncomputable def nonzeroSum (f : F → ℝ) : ℝ :=
  ∑ s ∈ (Finset.univ.erase 0 : Finset F), f s

private theorem nonzero_card_real :
    ((Finset.univ.erase (0 : F)).card : ℝ) =
      (Fintype.card F : ℝ) - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero)]
  norm_num

/-- Orthogonality on `F`, with the zero summand removed. -/
theorem nonzero_character_sum (input : FiniteFieldTrace.LiteratureInput F)
    (z : F) :
    nonzeroSum (F := F)
        (fun s ↦ FiniteFieldTrace.signCharacter F input.trace (s * z)) =
      if z = 0 then (Fintype.card F : ℝ) - 1 else -1 := by
  classical
  by_cases hz : z = 0
  · subst z
    simp only [nonzeroSum, mul_zero, FiniteFieldTrace.signCharacter_zero]
    calc
      ∑ _s ∈ (Finset.univ.erase 0 : Finset F), (1 : ℝ) =
          ((Finset.univ.erase (0 : F)).card : ℝ) := by simp
      _ = (Fintype.card F : ℝ) - 1 := nonzero_card_real
      _ = if True then (Fintype.card F : ℝ) - 1 else -1 := by simp
  · have hfull := input.character_orthogonality z
    rw [if_neg hz] at hfull
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset F)
      (fun s ↦ FiniteFieldTrace.signCharacter F input.trace (s * z))
      (Finset.mem_univ (0 : F))
    change nonzeroSum (F := F)
        (fun s ↦ FiniteFieldTrace.signCharacter F input.trace (s * z)) +
        FiniteFieldTrace.signCharacter F input.trace (0 * z) =
      ∑ s : F, FiniteFieldTrace.signCharacter F input.trace (s * z) at hsplit
    simp only [zero_mul, FiniteFieldTrace.signCharacter_zero] at hsplit
    rw [hfull] at hsplit
    simp [nonzeroSum, hz]
    linarith

/-! ## Exact entries of a Fourier block -/

/-- The real field size. -/
def fieldCard : ℝ := Fintype.card F

/-- The real number of chosen projective directions. -/
def directionCount : ℝ := Fintype.card ι

/-- The number `L = (|F|-1)|D|` of nonzero representative vectors. -/
def lineCount : ℝ := (fieldCard (F := F) - 1) * directionCount (ι := ι)

/-- The additive character appearing in the diagonal matrix `D_{b,c}`. -/
def phase (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F)
    (i : ι) (s : F) (p : Fˣ) : ℝ :=
  FiniteFieldTrace.signCharacter F input.trace
    ((p : F) * s * functional (D.representative i))

/-- Contribution of one projective direction to the `(p,r)` entry, after
summing over all its nonzero representatives. -/
noncomputable def directionContribution
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F)
    (i : ι) (p r : Fˣ) : ℝ :=
  nonzeroSum (F := F) (fun s ↦
    phase input D functional i s p * phase input D functional i s r)

private theorem units_add_ne_zero {p r : Fˣ} (hpr : p ≠ r) :
    (p : F) + (r : F) ≠ 0 := by
  intro hzero
  have heq : (p : F) = -(r : F) := eq_neg_of_add_eq_zero_left hzero
  rw [CharTwo.neg_eq] at heq
  exact hpr (Units.ext heq)

/-- Exact one-direction character sum. -/
theorem directionContribution_eq
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F)
    (i : ι) (p r : Fˣ) :
    directionContribution input D functional i p r =
      if p = r then fieldCard (F := F) - 1
      else if functional (D.representative i) = 0 then
        fieldCard (F := F) - 1 else -1 := by
  classical
  by_cases hpr : p = r
  · subst r
    simp only [directionContribution, nonzeroSum]
    have hterm : ∀ s : F,
        phase input D functional i s p * phase input D functional i s p = 1 :=
      fun s ↦ signCharacter_sq input _
    simp_rw [hterm]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [nonzero_card_real]
    simp [fieldCard]
  · have hsum := nonzero_character_sum input
        (((p : F) + (r : F)) * functional (D.representative i))
    have hterm : ∀ s : F,
        phase input D functional i s p * phase input D functional i s r =
          FiniteFieldTrace.signCharacter F input.trace
            (s * (((p : F) + (r : F)) *
              functional (D.representative i))) := by
      intro s
      simp only [phase]
      rw [signCharacter_add input]
      congr 1
      ring
    change nonzeroSum (F := F) (fun s ↦
      phase input D functional i s p * phase input D functional i s r) = _
    rw [show (fun s ↦ phase input D functional i s p *
        phase input D functional i s r) =
        (fun s ↦ FiniteFieldTrace.signCharacter F input.trace
          (s * (((p : F) + (r : F)) * functional (D.representative i)))) by
      funext s
      exact hterm s]
    rw [hsum]
    by_cases hz : functional (D.representative i) = 0
    · simp [hpr, hz, fieldCard]
    · have hnonzero :
          ((p : F) + (r : F)) * functional (D.representative i) ≠ 0 :=
        mul_ne_zero (units_add_ne_zero hpr) hz
      simp [hpr, hz, hnonzero]

/-- The raw Fourier block of `HᵀH`: sum of the rank-one signed all-ones
matrices over directions and nonzero representatives. -/
noncomputable def fourierGramBlock
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F) : Matrix Fˣ Fˣ ℝ :=
  fun p r ↦ ∑ i : ι, directionContribution input D functional i p r

/-- The natural direction weight, coerced to the reals. -/
noncomputable def realDirectionWeight (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F) : ℝ :=
  directionWeight F D functional

/-- Exact entry formula before removing the diagonal. -/
theorem fourierGramBlock_apply
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F)
    (p r : Fˣ) :
    fourierGramBlock input D functional p r =
      if p = r then lineCount (F := F) (ι := ι)
      else lineCount (F := F) (ι := ι) -
        fieldCard (F := F) * realDirectionWeight D functional := by
  classical
  by_cases hpr : p = r
  · simp only [fourierGramBlock, directionContribution_eq, hpr, if_pos]
    simp [lineCount, fieldCard, directionCount]
    ring
  · simp only [fourierGramBlock, directionContribution_eq, hpr, if_false]
    let S : Finset ι := Finset.univ.filter fun i ↦
      functional (D.representative i) ≠ 0
    have hsplit : (∑ i : ι,
        if functional (D.representative i) = 0 then
          fieldCard (F := F) - 1 else -1) =
        ∑ i : ι, ((fieldCard (F := F) - 1) -
          fieldCard (F := F) *
            (if i ∈ S then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hz : functional (D.representative i) = 0 <;> simp [hz]
    rw [hsplit, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    have hindicator : (∑ i : ι, if i ∈ S then (1 : ℝ) else 0) = S.card := by
      simp
    rw [hindicator]
    simp only [Finset.card_univ]
    change (Fintype.card ι : ℝ) * (fieldCard (F := F) - 1) -
        fieldCard (F := F) * (S.card : ℝ) = _
    have hweight : S.card = directionWeight F D functional := by
      simp [S, directionWeight]
    rw [hweight]
    simp only [realDirectionWeight]
    unfold lineCount directionCount
    ring

/-- The off-diagonal Fourier adjacency block `A_c`. -/
noncomputable def fourierAdjacencyBlock
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F) : Matrix Fˣ Fˣ ℝ :=
  fun p r ↦ fourierGramBlock input D functional p r -
    if p = r then lineCount (F := F) (ι := ι) else 0

/-- The matrix `J-I`, written without coercion ambiguities. -/
def jMinusI : Matrix Fˣ Fˣ ℝ :=
  fun p r ↦ if p = r then 0 else 1

/-- Equation (3.3) simplified to
`A_c = (L - |F| w(c)) (J-I)`. -/
theorem fourierAdjacencyBlock_eq
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F) :
    fourierAdjacencyBlock input D functional =
      (lineCount (F := F) (ι := ι) -
        fieldCard (F := F) * realDirectionWeight D functional) •
          (jMinusI : Matrix Fˣ Fˣ ℝ) := by
  funext p r
  rw [fourierAdjacencyBlock, fourierGramBlock_apply]
  by_cases hpr : p = r <;> simp [hpr, jMinusI]

/-! ## Normalization and exact eigenvalues -/

/-- The normalization denominator `(|F|-2)L`. -/
def normalization : ℝ :=
  (fieldCard (F := F) - 2) * lineCount (F := F) (ι := ι)

/-- The normalized Fourier block. -/
noncomputable def normalizedBlock
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F) : Matrix Fˣ Fˣ ℝ :=
  (normalization (F := F) (ι := ι))⁻¹ •
    fourierAdjacencyBlock input D functional

/-- Eigenvalue on the constant vector in the block. -/
noncomputable def lambdaConstant (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F) : ℝ :=
  1 - fieldCard (F := F) * realDirectionWeight D functional /
    lineCount (F := F) (ι := ι)

/-- Eigenvalue on the codimension-one zero-sum subspace in the block. -/
noncomputable def lambdaOrthogonal (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F) : ℝ :=
  (fieldCard (F := F) * realDirectionWeight D functional -
      lineCount (F := F) (ι := ι)) /
    normalization (F := F) (ι := ι)

theorem card_units_real : (Fintype.card Fˣ : ℝ) = fieldCard (F := F) - 1 := by
  rw [Fintype.card_units]
  simp only [fieldCard]
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero)]
  norm_num

/-- Multiplication by `J-I` is `sum - diagonal entry`. -/
theorem jMinusI_mulVec (f : Fˣ → ℝ) (p : Fˣ) :
    Matrix.mulVec (jMinusI : Matrix Fˣ Fˣ ℝ) f p =
      (∑ r : Fˣ, f r) - f p := by
  classical
  rw [Matrix.mulVec]
  simp only [dotProduct, jMinusI]
  simp_rw [ite_mul, zero_mul, one_mul]
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset Fˣ) f
    (Finset.mem_univ p)
  change (∑ r ∈ (Finset.univ.erase p : Finset Fˣ), f r) + f p =
    ∑ r : Fˣ, f r at hsplit
  have hoff : (∑ x : Fˣ, if p = x then 0 else f x) =
      ∑ x ∈ (Finset.univ.erase p : Finset Fˣ), f x := by
    rw [Finset.sum_ite]
    simp [Finset.filter_ne]
  rw [← hsplit]
  rw [hoff]
  ring

/-- Pointwise action formula for the normalized block. -/
theorem normalizedBlock_mulVec
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F)
    (f : Fˣ → ℝ) (p : Fˣ) :
    Matrix.mulVec (normalizedBlock input D functional) f p =
      ((lineCount (F := F) (ι := ι) -
          fieldCard (F := F) * realDirectionWeight D functional) /
        normalization (F := F) (ι := ι)) *
          ((∑ r : Fˣ, f r) - f p) := by
  rw [normalizedBlock, fourierAdjacencyBlock_eq]
  simp only [smul_smul, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
    jMinusI_mulVec]
  ring

/-- The constant vector has the first eigenvalue in (3.4). -/
theorem normalizedBlock_const_eigenvector
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F)
    (hfield : 2 < fieldCard (F := F))
    (hdirections : 0 < directionCount (ι := ι)) (a : ℝ) :
    Matrix.mulVec (normalizedBlock input D functional) (fun _ ↦ a) =
      fun _ ↦ lambdaConstant D functional * a := by
  funext p
  rw [normalizedBlock_mulVec]
  have hL : lineCount (F := F) (ι := ι) ≠ 0 := by
    apply ne_of_gt
    exact mul_pos (by linarith) hdirections
  have hQ : fieldCard (F := F) - 2 ≠ 0 := by linarith
  have hsum : (∑ _r : Fˣ, a) =
      (fieldCard (F := F) - 1) * a := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, card_units_real]
  simp only [lambdaConstant, normalization]
  rw [hsum]
  field_simp
  all_goals ring

/-- Every zero-sum vector has the second eigenvalue in (3.4). -/
theorem normalizedBlock_zeroSum_eigenvector
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F)
    (f : Fˣ → ℝ) (hf : ∑ p : Fˣ, f p = 0) :
    Matrix.mulVec (normalizedBlock input D functional) f =
      fun p ↦ lambdaOrthogonal D functional * f p := by
  funext p
  rw [normalizedBlock_mulVec, hf]
  simp only [zero_sub, lambdaOrthogonal]
  ring

/-! ## Arithmetic bounds for the two block eigenvalues -/

private theorem lambdaConstant_lower_arithmetic
    {q n w : ℝ} (hq : 2 < q) (hn : 0 < n) (hw : w ≤ n) :
    -1 / (q - 1) ≤ 1 - q * w / ((q - 1) * n) := by
  have hq₀ : 0 < q := by linarith
  have hq₁ : 0 < q - 1 := by linarith
  have hden : 0 < (q - 1) * n := mul_pos hq₁ hn
  rw [show 1 - q * w / ((q - 1) * n) =
      (((q - 1) * n) - q * w) / ((q - 1) * n) by
    field_simp]
  apply (div_le_div_iff₀ hq₁ hden).2
  have hnonneg : 0 ≤ q * (q - 1) * (n - w) :=
    mul_nonneg (mul_nonneg hq₀.le hq₁.le) (sub_nonneg.mpr hw)
  nlinarith

private theorem lambdaConstant_upper_arithmetic
    {q L w delta : ℝ} (hq : 0 ≤ q) (hL : 0 < L)
    (hdelta : delta ≤ w) :
    1 - q * w / L ≤ 1 - q * delta / L := by
  have hmul : q * delta ≤ q * w :=
    mul_le_mul_of_nonneg_left hdelta hq
  have hdiv : q * delta / L ≤ q * w / L :=
    div_le_div_of_nonneg_right hmul hL.le
  linarith

private theorem lambdaOrthogonal_lower_arithmetic
    {q L w : ℝ} (hq : 2 < q) (hL : 0 < L) (hw₀ : 0 ≤ w) :
    -1 / (q - 2) ≤ (q * w - L) / ((q - 2) * L) := by
  have hq₀ : 0 < q := by linarith
  have hq₂ : 0 < q - 2 := by linarith
  rw [show (q * w - L) / ((q - 2) * L) =
      (q * w / L - 1) / (q - 2) by
    field_simp]
  apply (div_le_div_iff_of_pos_right hq₂).2
  have hnonneg : 0 ≤ q * w / L :=
    div_nonneg (mul_nonneg hq₀.le hw₀) hL.le
  linarith

private theorem lambdaOrthogonal_upper_arithmetic
    {q n w : ℝ} (hq : 2 < q) (hn : 0 < n) (hw : w ≤ n) :
    (q * w - (q - 1) * n) / ((q - 2) * ((q - 1) * n)) ≤
      1 / ((q - 2) * (q - 1)) := by
  have hq₀ : 0 < q := by linarith
  have hq₁ : 0 < q - 1 := by linarith
  have hq₂ : 0 < q - 2 := by linarith
  have hL : 0 < (q - 1) * n := mul_pos hq₁ hn
  rw [show (q * w - (q - 1) * n) / ((q - 2) * ((q - 1) * n)) =
      (q * w / ((q - 1) * n) - 1) / (q - 2) by
    field_simp]
  rw [show 1 / ((q - 2) * (q - 1)) =
      (1 / (q - 1)) / (q - 2) by
    field_simp]
  apply (div_le_div_iff_of_pos_right hq₂).2
  rw [show q * w / ((q - 1) * n) - 1 =
      (q * w - (q - 1) * n) / ((q - 1) * n) by
    field_simp]
  apply (div_le_div_iff₀ hL hq₁).2
  have hnonneg : 0 ≤ q * (q - 1) * (n - w) :=
    mul_nonneg (mul_nonneg hq₀.le hq₁.le) (sub_nonneg.mpr hw)
  nlinarith

private theorem negative_endpoint_mono {q : ℝ} (hq : 2 < q) :
    -1 / (q - 2) ≤ -1 / (q - 1) := by
  have hq₂ : 0 < q - 2 := by linarith
  have hone : 1 / (q - 1) ≤ 1 / (q - 2) :=
    one_div_le_one_div_of_le hq₂ (by linarith)
  calc
    -1 / (q - 2) = -(1 / (q - 2)) := by ring
    _ ≤ -(1 / (q - 1)) := neg_le_neg hone
    _ = -1 / (q - 1) := by ring

/-- For a nonzero Fourier frequency, both exact eigenvalues satisfy the three
endpoint estimates in the proof of Lemma 3.7. -/
theorem nonzero_block_eigenvalue_bounds
    (D : DirectionSet F t ι)
    (functional : CoordinateSpace F t →ₗ[F] F)
    (hfunctional : functional ≠ 0) (minimumWeight : ℕ)
    (hlower : HasLowerDistance F D minimumWeight)
    (hfield : 2 < fieldCard (F := F))
    (hdirections : 0 < directionCount (ι := ι)) :
    (-1 / (fieldCard (F := F) - 1) ≤ lambdaConstant D functional ∧
      lambdaConstant D functional ≤
        1 - fieldCard (F := F) * (minimumWeight : ℝ) /
          lineCount (F := F) (ι := ι)) ∧
    (-1 / (fieldCard (F := F) - 2) ≤ lambdaOrthogonal D functional ∧
      lambdaOrthogonal D functional ≤
        1 / ((fieldCard (F := F) - 2) *
          (fieldCard (F := F) - 1))) := by
  have hwNatLower := hlower functional hfunctional
  have hwNatUpper := directionWeight_le_card F D functional
  have hw₀ : 0 ≤ realDirectionWeight D functional := by
    simp only [realDirectionWeight]
    positivity
  have hwLower : (minimumWeight : ℝ) ≤ realDirectionWeight D functional := by
    simp only [realDirectionWeight]
    exact_mod_cast hwNatLower
  have hwUpper : realDirectionWeight D functional ≤ directionCount (ι := ι) := by
    simp only [realDirectionWeight, directionCount]
    exact_mod_cast hwNatUpper
  have hL : 0 < lineCount (F := F) (ι := ι) :=
    mul_pos (by linarith) hdirections
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simpa only [lambdaConstant, lineCount] using
      lambdaConstant_lower_arithmetic hfield hdirections hwUpper
  · exact lambdaConstant_upper_arithmetic (by linarith) hL hwLower
  · simpa only [lambdaOrthogonal, normalization] using
      lambdaOrthogonal_lower_arithmetic hfield hL hw₀
  · simpa only [lambdaOrthogonal, normalization, lineCount] using
      lambdaOrthogonal_upper_arithmetic hfield hdirections hwUpper

/-- At zero frequency the two displayed eigenvalues are exactly `1` and the
negative endpoint `-1/(|F|-2)`. -/
theorem zero_block_eigenvalues
    (D : DirectionSet F t ι)
    (hfield : 2 < fieldCard (F := F))
    (hdirections : 0 < directionCount (ι := ι)) :
    lambdaConstant D (0 : CoordinateSpace F t →ₗ[F] F) = 1 ∧
    lambdaOrthogonal D (0 : CoordinateSpace F t →ₗ[F] F) =
      -1 / (fieldCard (F := F) - 2) := by
  have hL : lineCount (F := F) (ι := ι) ≠ 0 :=
    ne_of_gt (mul_pos (by linarith) hdirections)
  have hQ : fieldCard (F := F) - 2 ≠ 0 := by linarith
  have hw : realDirectionWeight D
      (0 : CoordinateSpace F t →ₗ[F] F) = 0 := by
    simp [realDirectionWeight, directionWeight]
  constructor
  · simp [lambdaConstant, hw]
  · rw [lambdaOrthogonal, normalization, hw]
    field_simp
    all_goals ring

/-! ## Spectrum interface and the connectedness deduction -/

/-- A real mean-zero eigenvalue of a weighted random-walk operator. -/
def IsMeanZeroEigenvalue {V : Type*} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (mu : ℝ) : Prop :=
  ∃ f : V → ℝ, f ≠ 0 ∧ G.weightedMean f = 0 ∧
    G.walk f = fun v ↦ mu * f v

/-- The concrete counting-Gram graph, normalized by the denominator in
Lemma 3.7.  Nonnegativity is automatic; the main theorem assumes strict
positivity. -/
noncomputable def relationGraph (D : DirectionSet F t ι) :
    WeightedGraph (AffineRelation.Column F t) :=
  (gramGraph (AffineRelation.matrix D)).scale
    (normalization (F := F) (ι := ι))⁻¹ (by
      have hcard : 2 ≤ Fintype.card F := by
        let e : Fin 2 → F := fun i ↦ if i = 0 then 0 else 1
        have he : Function.Injective e := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp [e] at hij ⊢
        simpa using Fintype.card_le_of_injective e he
      have hfieldReal : (2 : ℝ) ≤ fieldCard (F := F) := by
        simp only [fieldCard]
        exact_mod_cast hcard
      apply inv_nonneg.mpr
      apply mul_nonneg
      · linarith
      · exact mul_nonneg (by linarith)
          (Nat.cast_nonneg (Fintype.card ι)))

private theorem weightedGraph_eq_of_weight_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G H : WeightedGraph V) (hweight : G.weight = H.weight) : G = H := by
  cases G with
  | mk gw gs gl gn =>
    cases H with
    | mk hw hs hl hn =>
      simp only [WeightedGraph.mk.injEq]
      exact hweight

/-- The exact normalization identity needed to identify the graph above with
the compiler's normalized counting-Gram graph. -/
theorem relationGraph_eq_normalizedGramGraph
    (D : DirectionSet F t ι) (rho : ℕ) (hrho : 0 < rho)
    (hnormalization : normalization (F := F) (ι := ι) = 2 * (rho : ℝ)) :
    relationGraph D =
      RelationMatrix.normalizedGramGraph (AffineRelation.matrix D) rho hrho := by
  apply weightedGraph_eq_of_weight_eq
  funext u v
  simp only [relationGraph, RelationMatrix.normalizedGramGraph,
    WeightedGraph.scale]
  rw [hnormalization]

/-- A natural-number count of `2 rho = (|F|-2)L` implies the real
normalization identity used by `relationGraph_eq_normalizedGramGraph`. -/
theorem normalization_eq_two_rho_of_count
    (rho : ℕ) (hfield : 2 ≤ Fintype.card F)
    (hcount : 2 * rho =
      (Fintype.card F - 2) * ((Fintype.card F - 1) * Fintype.card ι)) :
    normalization (F := F) (ι := ι) = 2 * (rho : ℝ) := by
  have hone : 1 ≤ Fintype.card F := le_trans (by norm_num) hfield
  have hcountReal := congrArg (fun n : ℕ ↦ (n : ℝ)) hcount
  norm_num only [Nat.cast_mul] at hcountReal
  rw [Nat.cast_sub hfield, Nat.cast_sub hone] at hcountReal
  simp only [normalization, lineCount, fieldCard, directionCount]
  simpa using hcountReal.symm

/-- The three kinds of nonconstant block eigenvalues after deleting the
global constant vector. -/
def IsBlockCandidate (D : DirectionSet F t ι) (mu : ℝ) : Prop :=
  mu = lambdaOrthogonal D (0 : CoordinateSpace F t →ₗ[F] F) ∨
  ∃ functional : CoordinateSpace F t →ₗ[F] F, functional ≠ 0 ∧
    (mu = lambdaConstant D functional ∨
      mu = lambdaOrthogonal D functional)

/-- Explicit boundary for the finite Fourier diagonalization.  `complete` is
the only unformalized transform/completeness step: it identifies every
mean-zero graph eigenvalue with one of the blocks computed above.
`one_of_disconnected` records the elementary regular-graph multiplicity fact
used to infer connectedness. -/
structure FourierInterface
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) : Prop where
  complete : ∀ mu,
    IsMeanZeroEigenvalue (relationGraph D) mu → IsBlockCandidate D mu
  one_of_disconnected : ¬(relationGraph D).Connected →
    IsMeanZeroEigenvalue (relationGraph D) 1
  l2_bound_of_candidates : ∀ lambda : ℝ, 0 ≤ lambda →
    (∀ mu : ℝ, IsBlockCandidate D mu → |mu| ≤ lambda) →
      (relationGraph D).TwoSidedSpectralBound lambda

/-- Every block candidate lies in the interval (3.2). -/
theorem blockCandidate_bounds
    (D : DirectionSet F t ι) (minimumWeight : ℕ)
    (hlower : HasLowerDistance F D minimumWeight)
    (hfield : 2 < fieldCard (F := F))
    (hdirections : 0 < directionCount (ι := ι))
    {mu : ℝ} (hmu : IsBlockCandidate D mu) :
    -1 / (fieldCard (F := F) - 2) ≤ mu ∧
    mu ≤ max
      (1 - fieldCard (F := F) * (minimumWeight : ℝ) /
        lineCount (F := F) (ι := ι))
      (1 / ((fieldCard (F := F) - 2) *
        (fieldCard (F := F) - 1))) := by
  rcases hmu with hzero | ⟨functional, hfunctional, hconstant | horthogonal⟩
  · rw [hzero, (zero_block_eigenvalues D hfield hdirections).2]
    constructor
    · exact le_rfl
    · apply le_trans _ (le_max_right _ _)
      have hq₂ : 0 < fieldCard (F := F) - 2 := by linarith
      have hq₁ : 0 < fieldCard (F := F) - 1 := by linarith
      have hright : 0 < 1 / ((fieldCard (F := F) - 2) *
          (fieldCard (F := F) - 1)) := by positivity
      have hleft : -1 / (fieldCard (F := F) - 2) < 0 := by
        exact div_neg_of_neg_of_pos (by norm_num) hq₂
      linarith
  · rw [hconstant]
    obtain ⟨⟨hlow, hupp⟩, -⟩ :=
      nonzero_block_eigenvalue_bounds D functional hfunctional minimumWeight
        hlower hfield hdirections
    constructor
    · exact (negative_endpoint_mono hfield).trans hlow
    · exact hupp.trans (le_max_left _ _)
  · rw [horthogonal]
    obtain ⟨-, ⟨hlow, hupp⟩⟩ :=
      nonzero_block_eigenvalue_bounds D functional hfunctional minimumWeight
        hlower hfield hdirections
    exact ⟨hlow, hupp.trans (le_max_right _ _)⟩

/-- The explicit upper endpoint of (3.2) is strictly smaller than one as soon
as the direction distance is positive. -/
theorem blockUpper_lt_one
    (_D : DirectionSet F t ι) (minimumWeight : ℕ)
    (hminimum : 0 < minimumWeight)
    (hfield : 4 ≤ fieldCard (F := F))
    (hdirections : 0 < directionCount (ι := ι)) :
    max
      (1 - fieldCard (F := F) * (minimumWeight : ℝ) /
        lineCount (F := F) (ι := ι))
      (1 / ((fieldCard (F := F) - 2) *
        (fieldCard (F := F) - 1))) < 1 := by
  apply max_lt
  · have hQ : 0 < fieldCard (F := F) := by linarith
    have hDelta : 0 < (minimumWeight : ℝ) := by exact_mod_cast hminimum
    have hL : 0 < lineCount (F := F) (ι := ι) :=
      mul_pos (by linarith) hdirections
    have hratio : 0 < fieldCard (F := F) * (minimumWeight : ℝ) /
        lineCount (F := F) (ι := ι) := by positivity
    linarith
  · have hden : 1 < (fieldCard (F := F) - 2) *
        (fieldCard (F := F) - 1) := by nlinarith
    exact (div_lt_one (by nlinarith)).2 hden

/-- Conditional spectrum statement of Lemma 3.7.  All mathematical content
after the finite Fourier completeness certificate is proved in this file. -/
theorem spectrum_interval
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) (minimumWeight : ℕ)
    (hlower : HasLowerDistance F D minimumWeight)
    (hfield : 2 < fieldCard (F := F))
    (hdirections : 0 < directionCount (ι := ι))
    (fourier : FourierInterface input D)
    {mu : ℝ} (hmu : IsMeanZeroEigenvalue (relationGraph D) mu) :
    -1 / (fieldCard (F := F) - 2) ≤ mu ∧
    mu ≤ max
      (1 - fieldCard (F := F) * (minimumWeight : ℝ) /
        lineCount (F := F) (ι := ι))
      (1 / ((fieldCard (F := F) - 2) *
        (fieldCard (F := F) - 1))) :=
  blockCandidate_bounds D minimumWeight hlower hfield hdirections
    (fourier.complete mu hmu)

/-- A two-sided numerical bound for every Fourier candidate, obtained from the
interval (3.2). -/
theorem blockCandidate_abs_le
    (D : DirectionSet F t ι) (minimumWeight : ℕ)
    (hlower : HasLowerDistance F D minimumWeight)
    (hfield : 2 < fieldCard (F := F))
    (hdirections : 0 < directionCount (ι := ι))
    (lambda : ℝ)
    (hnegative : 1 / (fieldCard (F := F) - 2) ≤ lambda)
    (hupper : max
      (1 - fieldCard (F := F) * (minimumWeight : ℝ) /
        lineCount (F := F) (ι := ι))
      (1 / ((fieldCard (F := F) - 2) *
        (fieldCard (F := F) - 1))) ≤ lambda)
    {mu : ℝ} (hmu : IsBlockCandidate D mu) : |mu| ≤ lambda := by
  obtain ⟨hlow, hupp⟩ :=
    blockCandidate_bounds D minimumWeight hlower hfield hdirections hmu
  rw [abs_le]
  constructor
  · calc
      -lambda ≤ -(1 / (fieldCard (F := F) - 2)) := neg_le_neg hnegative
      _ = -1 / (fieldCard (F := F) - 2) := by ring
      _ ≤ mu := hlow
  · exact hupp.trans hupper

/-- The certified block decomposition yields the actual weighted `L²`
spectral inequality used by the relation compiler.  The transform-to-`L²`
step is precisely the `l2_bound_of_candidates` field of `FourierInterface`. -/
theorem relationGraph_twoSidedSpectralBound
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) (minimumWeight : ℕ)
    (hlower : HasLowerDistance F D minimumWeight)
    (hfield : 2 < fieldCard (F := F))
    (hdirections : 0 < directionCount (ι := ι))
    (fourier : FourierInterface input D)
    (lambda : ℝ)
    (hnegative : 1 / (fieldCard (F := F) - 2) ≤ lambda)
    (hupper : max
      (1 - fieldCard (F := F) * (minimumWeight : ℝ) /
        lineCount (F := F) (ι := ι))
      (1 / ((fieldCard (F := F) - 2) *
        (fieldCard (F := F) - 1))) ≤ lambda) :
    (relationGraph D).TwoSidedSpectralBound lambda := by
  have hreciprocal : 0 < 1 / (fieldCard (F := F) - 2) := by
    positivity
  have hlambda : 0 ≤ lambda :=
    le_trans hreciprocal.le hnegative
  apply fourier.l2_bound_of_candidates lambda hlambda
  intro mu hmu
  exact blockCandidate_abs_le D minimumWeight hlower hfield hdirections
    lambda hnegative hupper hmu

/-- Last sentence of Lemma 3.7: positive lower distance makes the spectral
upper endpoint strictly smaller than one, hence the relation graph is
connected. -/
theorem relationGraph_connected
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) (minimumWeight : ℕ)
    (hlower : HasLowerDistance F D minimumWeight)
    (hminimum : 0 < minimumWeight)
    (hfield : 4 ≤ fieldCard (F := F))
    (hdirections : 0 < directionCount (ι := ι))
    (fourier : FourierInterface input D) :
    (relationGraph D).Connected := by
  by_contra hconnected
  have hone := fourier.one_of_disconnected hconnected
  have hbounds := spectrum_interval input D minimumWeight hlower
    (by linarith) hdirections fourier hone
  have hupper := blockUpper_lt_one D minimumWeight hminimum hfield hdirections
  linarith [hbounds.2]

/-- Lemma 3.7 packaged in the exact form consumed by the relation compiler.
The combinatorial fields come from Lemmas 3.5 and 3.6; this theorem supplies
connectedness and the normalized two-sided spectral inequality. -/
theorem spectralCertificate
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) (minimumWeight : ℕ)
    (hlower : HasLowerDistance F D minimumWeight)
    (hminimum : 0 < minimumWeight)
    (hfield : 4 ≤ fieldCard (F := F))
    (hdirections : 0 < directionCount (ι := ι))
    (fourier : FourierInterface input D)
    (rho : ℕ)
    (compiler : RelationMatrix.CompilerHypotheses (AffineRelation.matrix D) rho)
    (pairMultiplicity :
      RelationMatrix.PairMultiplicityAtMostOne (AffineRelation.matrix D))
    (hnormalization : normalization (F := F) (ι := ι) = 2 * (rho : ℝ))
    (lambda : ℝ)
    (hnegative : 1 / (fieldCard (F := F) - 2) ≤ lambda)
    (hupper : max
      (1 - fieldCard (F := F) * (minimumWeight : ℝ) /
        lineCount (F := F) (ι := ι))
      (1 / ((fieldCard (F := F) - 2) *
        (fieldCard (F := F) - 1))) ≤ lambda) :
    RelationMatrix.SpectralCertificate (AffineRelation.matrix D) rho lambda := by
  have hgraph := relationGraph_eq_normalizedGramGraph D rho
    compiler.constantColumnWeight.1 hnormalization
  refine RelationMatrix.SpectralCertificate.mk compiler pairMultiplicity ?_ ?_
  · rw [← hgraph]
    exact relationGraph_connected input D minimumWeight hlower hminimum hfield
      hdirections fourier
  · rw [← hgraph]
    exact relationGraph_twoSidedSpectralBound input D minimumWeight hlower
      (by linarith) hdirections fourier lambda hnegative hupper

end AffineRelationSpectrum

end HDXLean
