import HDXLean.AffineRelationAdjacency
import HDXLean.FiniteRegularSpectrum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite Fourier basis on the affine coordinate space

This file proves the finite Fourier completeness statement left at the boundary
of the block computation in Lemma 3.7.  Frequencies are represented by vectors
in `Fin t → F`; the associated functional is the standard dot product.  The
binary trace character gives a real-valued orthogonal basis of all functions on
the coordinate space.
-/

namespace HDXLean

open scoped BigOperators

namespace FiniteFourierBasis

universe u v

set_option linter.unusedSectionVars false

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
  [CharP F 2] [Algebra F₂ F]
variable {t : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The linear functional represented by a coordinate frequency vector. -/
noncomputable def dotFunctional (frequency : CoordinateSpace F t) :
    CoordinateSpace F t →ₗ[F] F where
  toFun x := ∑ i, frequency i * x i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [RingHom.id_apply]
    ring

@[simp]
theorem dotFunctional_apply (frequency x : CoordinateSpace F t) :
    dotFunctional frequency x = ∑ i, frequency i * x i :=
  rfl

/-- Dot product is symmetric. -/
theorem dotFunctional_symm (a x : CoordinateSpace F t) :
    dotFunctional a x = dotFunctional x a := by
  change (∑ i, a i * x i) = ∑ i, x i * a i
  apply Finset.sum_congr rfl
  intro i _hi
  exact mul_comm _ _

/-- Every linear functional on the coordinate space is a dot-product
functional. -/
theorem dotFunctional_surjective :
    Function.Surjective
      (dotFunctional : CoordinateSpace F t →
        (CoordinateSpace F t →ₗ[F] F)) := by
  intro functional
  let frequency : CoordinateSpace F t := fun i ↦
    functional (Pi.single i 1)
  refine ⟨frequency, LinearMap.ext fun x ↦ ?_⟩
  have hx : (∑ i, x i • Pi.single i (1 : F)) = x := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single j]
    · simp
    · intro i hij
      simp [hij]
  calc
    dotFunctional frequency x =
        ∑ i, x i * functional (Pi.single i (1 : F)) := by
      change (∑ i, functional (Pi.single i 1) * x i) = _
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = ∑ i, functional (x i • Pi.single i (1 : F)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [map_smul]
      rfl
    _ = functional (∑ i, x i • Pi.single i (1 : F)) := by
      rw [map_sum]
    _ = functional x := by rw [hx]

/-- The coordinate-frequency parameterization of the dual is injective. -/
theorem dotFunctional_injective :
    Function.Injective
      (dotFunctional : CoordinateSpace F t →
        (CoordinateSpace F t →ₗ[F] F)) := by
  intro a b hab
  funext i
  have hi := LinearMap.congr_fun hab (Pi.single i 1)
  simp only [dotFunctional_apply] at hi
  simpa [Pi.single_apply] using hi

@[simp]
theorem dotFunctional_zero :
    dotFunctional (0 : CoordinateSpace F t) =
      (0 : CoordinateSpace F t →ₗ[F] F) := by
  ext x
  simp [dotFunctional]

/-- Frequencies and linear functionals are in explicit bijection. -/
noncomputable def frequencyEquivDual :
    CoordinateSpace F t ≃ (CoordinateSpace F t →ₗ[F] F) :=
  Equiv.ofBijective dotFunctional
    ⟨dotFunctional_injective, dotFunctional_surjective⟩

/-- The real trace character indexed by a coordinate frequency vector. -/
noncomputable def character (input : FiniteFieldTrace.LiteratureInput F)
    (frequency : CoordinateSpace F t) (x : CoordinateSpace F t) : ℝ :=
  AffineRelation.baseCharacter input (dotFunctional frequency) x

@[simp]
theorem character_zero_frequency
    (input : FiniteFieldTrace.LiteratureInput F)
    (x : CoordinateSpace F t) : character input 0 x = 1 := by
  simp [character, AffineRelation.baseCharacter,
    FiniteFieldTrace.signCharacter]

@[simp]
theorem character_zero_argument
    (input : FiniteFieldTrace.LiteratureInput F)
    (frequency : CoordinateSpace F t) : character input frequency 0 = 1 := by
  simp [character, AffineRelation.baseCharacter,
    FiniteFieldTrace.signCharacter]

/-- The character is multiplicative under addition of its argument. -/
theorem character_add_argument
    (input : FiniteFieldTrace.LiteratureInput F)
    (frequency x y : CoordinateSpace F t) :
    character input frequency x * character input frequency y =
      character input frequency (x + y) := by
  unfold character AffineRelation.baseCharacter
  rw [AffineRelationSpectrum.signCharacter_add input]
  congr 1
  exact ((dotFunctional frequency).map_add x y).symm

/-- The product of two frequency characters is the character at the sum of
the two frequencies. -/
theorem character_add_frequency
    (input : FiniteFieldTrace.LiteratureInput F)
    (a b x : CoordinateSpace F t) :
    character input a x * character input b x =
      character input (a + b) x := by
  unfold character AffineRelation.baseCharacter
  rw [AffineRelationSpectrum.signCharacter_add input]
  congr 1
  simp only [dotFunctional_apply, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

/-- Every binary trace character has square one. -/
theorem character_sq (input : FiniteFieldTrace.LiteratureInput F)
    (frequency x : CoordinateSpace F t) :
    character input frequency x * character input frequency x = 1 := by
  exact AffineRelationSpectrum.signCharacter_sq input _

/-- A nonzero frequency has zero total character sum. -/
theorem character_sum_eq_zero
    (input : FiniteFieldTrace.LiteratureInput F)
    (frequency : CoordinateSpace F t) (hfrequency : frequency ≠ 0) :
    (∑ x : CoordinateSpace F t, character input frequency x) = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, frequency i ≠ 0 := by
    by_contra h
    apply hfrequency
    funext i
    exact not_not.mp (not_exists.mp h i)
  obtain ⟨p, hp⟩ :=
    FiniteFieldTrace.exists_trace_mul_eq_one F input hi
  let z : CoordinateSpace F t := Pi.single i p
  have hdot : dotFunctional frequency z = p * frequency i := by
    rw [dotFunctional_apply, Fintype.sum_eq_single i]
    · simp [z, mul_comm]
    · intro j hji
      simp [z, hji]
  have hz : character input frequency z = -1 := by
    unfold character AffineRelation.baseCharacter
    rw [hdot]
    simp [FiniteFieldTrace.signCharacter, hp]
  have htranslate :
      (∑ x : CoordinateSpace F t, character input frequency x) =
        ∑ x : CoordinateSpace F t, character input frequency (x + z) := by
    exact (Equiv.sum_comp (Equiv.addRight z)
      (character input frequency)).symm
  have htranslate' :
      (∑ x : CoordinateSpace F t, character input frequency x) =
        -(∑ x : CoordinateSpace F t, character input frequency x) := by
    calc
      _ = ∑ x : CoordinateSpace F t,
          character input frequency (x + z) := htranslate
      _ = ∑ x : CoordinateSpace F t,
          character input frequency x * character input frequency z := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact (character_add_argument input frequency x z).symm
      _ = -(∑ x : CoordinateSpace F t,
          character input frequency x) := by
        rw [hz]
        simp
  linarith

/-- Exact orthogonality of the coordinate trace characters. -/
theorem character_orthogonality
    (input : FiniteFieldTrace.LiteratureInput F)
    (a b : CoordinateSpace F t) :
    (∑ x : CoordinateSpace F t,
        character input a x * character input b x) =
      if a = b then (Fintype.card (CoordinateSpace F t) : ℝ) else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    simp only [character_sq]
    simp
  · rw [if_neg hab]
    simp_rw [character_add_frequency input a b]
    apply character_sum_eq_zero input (a + b)
    intro hadd
    apply hab
    funext i
    have hi := congrFun hadd i
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    have : a i = -(b i) := eq_neg_of_add_eq_zero_left hi
    simpa only [CharTwo.neg_eq] using this

/-- Taking the inner product with one character extracts its coefficient from
a finite character synthesis, up to the common squared norm. -/
theorem character_inner_synthesis
    (input : FiniteFieldTrace.LiteratureInput F)
    (coefficients : CoordinateSpace F t → ℝ)
    (a : CoordinateSpace F t) :
    (∑ x : CoordinateSpace F t,
        character input a x *
          (∑ b, coefficients b * character input b x)) =
      coefficients a * (Fintype.card (CoordinateSpace F t) : ℝ) := by
  classical
  calc
    _ = ∑ x : CoordinateSpace F t, ∑ b,
        coefficients b *
          (character input a x * character input b x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    _ = ∑ b, ∑ x : CoordinateSpace F t,
        coefficients b *
          (character input a x * character input b x) :=
      Finset.sum_comm
    _ = ∑ b, coefficients b *
        (∑ x : CoordinateSpace F t,
          character input a x * character input b x) := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [Finset.mul_sum]
    _ = ∑ b, if a = b then
          coefficients b * (Fintype.card (CoordinateSpace F t) : ℝ)
        else 0 := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [character_orthogonality input a b]
      by_cases hab : a = b <;> simp [hab]
    _ = coefficients a *
        (Fintype.card (CoordinateSpace F t) : ℝ) := by simp

/-- The character family is linearly independent over the reals. -/
theorem character_linearIndependent
    (input : FiniteFieldTrace.LiteratureInput F) :
    LinearIndependent ℝ (character input :
      CoordinateSpace F t → CoordinateSpace F t → ℝ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coefficients hzero a
  have hpoint : ∀ x : CoordinateSpace F t,
      ∑ b, coefficients b * character input b x = 0 := by
    intro x
    have hx := congrFun hzero x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] using hx
  have hsum :
      (∑ x : CoordinateSpace F t,
          character input a x *
            (∑ b, coefficients b * character input b x)) = 0 := by
    simp_rw [hpoint]
    simp
  have hcollapse :
      (∑ x : CoordinateSpace F t,
          character input a x *
            (∑ b, coefficients b * character input b x)) =
        coefficients a * (Fintype.card (CoordinateSpace F t) : ℝ) := by
    exact character_inner_synthesis input coefficients a
  rw [hcollapse] at hsum
  exact (mul_eq_zero.mp hsum).resolve_right (by positivity)

/-- The trace characters form a basis of all real functions on the coordinate
space. -/
noncomputable def characterBasis
    (input : FiniteFieldTrace.LiteratureInput F) :
    Module.Basis (CoordinateSpace F t) ℝ (CoordinateSpace F t → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank
    (character_linearIndependent input) (by
      rw [Module.finrank_fintype_fun_eq_card])

@[simp]
theorem characterBasis_apply
    (input : FiniteFieldTrace.LiteratureInput F)
    (frequency : CoordinateSpace F t) :
    characterBasis input frequency = character input frequency := by
  rw [characterBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- Normalized Fourier coefficient of a real function. -/
noncomputable def coefficient
    (input : FiniteFieldTrace.LiteratureInput F)
    (f : CoordinateSpace F t → ℝ) (frequency : CoordinateSpace F t) : ℝ :=
  (Fintype.card (CoordinateSpace F t) : ℝ)⁻¹ *
    ∑ x, character input frequency x * f x

/-- A synthesized character sum has exactly the prescribed Fourier
coefficients. -/
theorem coefficient_synthesis
    (input : FiniteFieldTrace.LiteratureInput F)
    (values : CoordinateSpace F t → ℝ)
    (frequency : CoordinateSpace F t) :
    coefficient input
        (fun x ↦ ∑ a, values a * character input a x) frequency =
      values frequency := by
  rw [coefficient, character_inner_synthesis]
  have hcard : (Fintype.card (CoordinateSpace F t) : ℝ) ≠ 0 := by
    positivity
  field_simp

/-- The normalized coefficient is the coordinate supplied by the character
basis. -/
theorem coefficient_eq_repr
    (input : FiniteFieldTrace.LiteratureInput F)
    (f : CoordinateSpace F t → ℝ) (frequency : CoordinateSpace F t) :
    coefficient input f frequency =
      (characterBasis input).repr f frequency := by
  let values : CoordinateSpace F t → ℝ :=
    fun a ↦ (characterBasis input).repr f a
  have hexpansion : ∀ x : CoordinateSpace F t,
      (∑ a, values a * character input a x) = f x := by
    intro x
    have hrepr := congrFun ((characterBasis input).sum_repr f) x
    simpa only [values, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      characterBasis_apply] using hrepr
  calc
    coefficient input f frequency = coefficient input
        (fun x ↦ ∑ a, values a * character input a x) frequency := by
      congr 2
      funext x
      exact (hexpansion x).symm
    _ = values frequency := coefficient_synthesis input values frequency
    _ = (characterBasis input).repr f frequency := rfl

/-- Fourier inversion on the coordinate space. -/
theorem inversion
    (input : FiniteFieldTrace.LiteratureInput F)
    (f : CoordinateSpace F t → ℝ) (x : CoordinateSpace F t) :
    (∑ frequency,
        coefficient input f frequency * character input frequency x) = f x := by
  simp_rw [coefficient_eq_repr]
  have hrepr := congrFun ((characterBasis input).sum_repr f) x
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    characterBasis_apply] using hrepr

/-- Fourier coefficients commute with real scalar multiplication. -/
theorem coefficient_smul
    (input : FiniteFieldTrace.LiteratureInput F)
    (f : CoordinateSpace F t → ℝ) (c : ℝ)
    (frequency : CoordinateSpace F t) :
    coefficient input (fun x ↦ c * f x) frequency =
      c * coefficient input f frequency := by
  unfold coefficient
  have hsum :
      (∑ x, character input frequency x * (c * f x)) =
        c * ∑ x, character input frequency x * f x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  rw [hsum]
  ring

/-- Multiplying a normalized coefficient by the size of the coordinate space
recovers its unnormalized character inner product. -/
theorem card_mul_coefficient
    (input : FiniteFieldTrace.LiteratureInput F)
    (f : CoordinateSpace F t → ℝ) (frequency : CoordinateSpace F t) :
    (Fintype.card (CoordinateSpace F t) : ℝ) *
        coefficient input f frequency =
      ∑ x, character input frequency x * f x := by
  unfold coefficient
  have hcard : (Fintype.card (CoordinateSpace F t) : ℝ) ≠ 0 := by
    positivity
  field_simp

/-- Parseval's identity for the real trace-character transform. -/
theorem parseval
    (input : FiniteFieldTrace.LiteratureInput F)
    (f g : CoordinateSpace F t → ℝ) :
    (∑ x, f x * g x) =
      (Fintype.card (CoordinateSpace F t) : ℝ) *
        ∑ frequency,
          coefficient input f frequency * coefficient input g frequency := by
  classical
  symm
  calc
    _ = ∑ frequency : CoordinateSpace F t,
        (Fintype.card (CoordinateSpace F t) : ℝ) *
          (coefficient input f frequency * coefficient input g frequency) := by
      rw [Finset.mul_sum]
    _ = ∑ frequency : CoordinateSpace F t,
        (∑ x, character input frequency x * f x) *
          coefficient input g frequency := by
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      rw [← card_mul_coefficient input f frequency]
      ring
    _ = ∑ frequency : CoordinateSpace F t,
        ∑ x : CoordinateSpace F t,
          f x * (coefficient input g frequency *
            character input frequency x) := by
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = ∑ x : CoordinateSpace F t,
        ∑ frequency : CoordinateSpace F t,
          f x * (coefficient input g frequency *
            character input frequency x) :=
      Finset.sum_comm
    _ = ∑ x : CoordinateSpace F t,
        f x * (∑ frequency : CoordinateSpace F t,
          coefficient input g frequency *
            character input frequency x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
    _ = ∑ x, f x * g x := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [inversion input g x]

/-- Squared-norm form of Parseval: the normalized transform is an isometry. -/
theorem coefficient_sq_sum
    (input : FiniteFieldTrace.LiteratureInput F)
    (f : CoordinateSpace F t → ℝ) :
    (∑ frequency, (coefficient input f frequency) ^ 2) =
      (Fintype.card (CoordinateSpace F t) : ℝ)⁻¹ *
        ∑ x, (f x) ^ 2 := by
  have hparseval := parseval input f f
  have hcard : (Fintype.card (CoordinateSpace F t) : ℝ) ≠ 0 := by
    positivity
  simp only [pow_two] at hparseval ⊢
  rw [hparseval]
  field_simp

/-- Fourier coefficient on each `Fˣ` fibre of the relation graph. -/
noncomputable def fiberCoefficient
    (input : FiniteFieldTrace.LiteratureInput F)
    (f : AffineRelation.Column F t → ℝ)
    (frequency : CoordinateSpace F t) (p : Fˣ) : ℝ :=
  coefficient input (fun x ↦ f (p, x)) frequency

/-- Fibrewise Fourier inversion is exactly a sum of the pure modes used by
the affine adjacency calculation. -/
theorem column_inversion
    (input : FiniteFieldTrace.LiteratureInput F)
    (f : AffineRelation.Column F t → ℝ)
    (p : Fˣ) (x : CoordinateSpace F t) :
    (∑ frequency,
        AffineRelation.fourierMode input (dotFunctional frequency)
          (fiberCoefficient input f frequency) (p, x)) = f (p, x) := by
  simpa only [AffineRelation.fourierMode, character, fiberCoefficient,
    mul_comm] using inversion input (fun y ↦ f (p, y)) x

/-! ## Compatibility with the concrete affine-relation operator -/

/-- Expanding an arbitrary column function in characters turns the concrete
counting-Gram adjacency action into the direct sum of the blocks computed in
`AffineRelationSpectrum`. -/
theorem gramGraph_action_expansion
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (f : AffineRelation.Column F t → ℝ)
    (p : Fˣ) (x : CoordinateSpace F t) :
    (∑ c : AffineRelation.Column F t,
        (gramGraph (AffineRelation.matrix D)).weight (p, x) c * f c) =
      ∑ frequency : CoordinateSpace F t,
        character input frequency x *
          Matrix.mulVec
            (AffineRelationSpectrum.fourierAdjacencyBlock input D
              (dotFunctional frequency))
            (fiberCoefficient input f frequency) p := by
  classical
  calc
    _ = ∑ c : AffineRelation.Column F t,
        (gramGraph (AffineRelation.matrix D)).weight (p, x) c *
          (∑ frequency : CoordinateSpace F t,
            AffineRelation.fourierMode input (dotFunctional frequency)
              (fiberCoefficient input f frequency) c) := by
      apply Finset.sum_congr rfl
      intro c _hc
      rcases c with ⟨r, y⟩
      rw [column_inversion input f r y]
    _ = ∑ c : AffineRelation.Column F t,
        ∑ frequency : CoordinateSpace F t,
          (gramGraph (AffineRelation.matrix D)).weight (p, x) c *
            AffineRelation.fourierMode input (dotFunctional frequency)
              (fiberCoefficient input f frequency) c := by
      apply Finset.sum_congr rfl
      intro c _hc
      rw [Finset.mul_sum]
    _ = ∑ frequency : CoordinateSpace F t,
        ∑ c : AffineRelation.Column F t,
          (gramGraph (AffineRelation.matrix D)).weight (p, x) c *
            AffineRelation.fourierMode input (dotFunctional frequency)
              (fiberCoefficient input f frequency) c :=
      Finset.sum_comm
    _ = ∑ frequency : CoordinateSpace F t,
        character input frequency x *
          Matrix.mulVec
            (AffineRelationSpectrum.fourierAdjacencyBlock input D
              (dotFunctional frequency))
            (fiberCoefficient input f frequency) p := by
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      simpa only [character] using
        AffineRelation.gramGraph_mul_fourierMode input D
          (dotFunctional frequency)
          (fiberCoefficient input f frequency) p x

/-- The normalized relation walk is the direct sum of the normalized Fourier
blocks. -/
theorem relationGraph_walk_expansion
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (hfield : 2 < Fintype.card F) (hdirections : Nonempty ι)
    (f : AffineRelation.Column F t → ℝ)
    (p : Fˣ) (x : CoordinateSpace F t) :
    (AffineRelationSpectrum.relationGraph D).walk f (p, x) =
      ∑ frequency : CoordinateSpace F t,
        character input frequency x *
          Matrix.mulVec
            (AffineRelationSpectrum.normalizedBlock input D
              (dotFunctional frequency))
            (fiberCoefficient input f frequency) p := by
  classical
  have hregular :=
    AffineRelationSpectrum.relationGraph_isUnitRegular D hfield hdirections
  rw [WeightedGraph.walk, hregular (p, x), div_one]
  change (∑ c : AffineRelation.Column F t,
      (AffineRelationSpectrum.normalization (F := F) (ι := ι))⁻¹ *
        (gramGraph (AffineRelation.matrix D)).weight (p, x) c * f c) = _
  calc
    _ = (AffineRelationSpectrum.normalization (F := F) (ι := ι))⁻¹ *
        (∑ c : AffineRelation.Column F t,
          (gramGraph (AffineRelation.matrix D)).weight (p, x) c * f c) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _hc
      ring
    _ = (AffineRelationSpectrum.normalization (F := F) (ι := ι))⁻¹ *
        (∑ frequency : CoordinateSpace F t,
          character input frequency x *
            Matrix.mulVec
              (AffineRelationSpectrum.fourierAdjacencyBlock input D
                (dotFunctional frequency))
              (fiberCoefficient input f frequency) p) := by
      rw [gramGraph_action_expansion input D f p x]
    _ = ∑ frequency : CoordinateSpace F t,
        character input frequency x *
          ((AffineRelationSpectrum.normalization (F := F) (ι := ι))⁻¹ *
            Matrix.mulVec
              (AffineRelationSpectrum.fourierAdjacencyBlock input D
                (dotFunctional frequency))
              (fiberCoefficient input f frequency) p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      simp only [AffineRelationSpectrum.normalizedBlock,
        Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]

/-- Fourier transformation of the relation walk is precisely multiplication
by the corresponding normalized block. -/
theorem fiberCoefficient_walk
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (hfield : 2 < Fintype.card F) (hdirections : Nonempty ι)
    (f : AffineRelation.Column F t → ℝ)
    (frequency : CoordinateSpace F t) (p : Fˣ) :
    fiberCoefficient input
        ((AffineRelationSpectrum.relationGraph D).walk f) frequency p =
      Matrix.mulVec
        (AffineRelationSpectrum.normalizedBlock input D
          (dotFunctional frequency))
        (fiberCoefficient input f frequency) p := by
  unfold fiberCoefficient
  rw [show (fun x : CoordinateSpace F t ↦
      (AffineRelationSpectrum.relationGraph D).walk f (p, x)) =
      (fun x ↦ ∑ a : CoordinateSpace F t,
        (fun b ↦ Matrix.mulVec
          (AffineRelationSpectrum.normalizedBlock input D
            (dotFunctional b))
          (fiberCoefficient input f b) p) a * character input a x) by
    funext x
    rw [relationGraph_walk_expansion input D hfield hdirections f p x]
    apply Finset.sum_congr rfl
    intro a _ha
    ring]
  exact coefficient_synthesis input
    (fun b ↦ Matrix.mulVec
      (AffineRelationSpectrum.normalizedBlock input D (dotFunctional b))
      (fiberCoefficient input f b) p) frequency

/-- The sum of a normalized block action is the constant-block eigenvalue
times the sum of the input amplitude. -/
theorem sum_normalizedBlock_mulVec
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (hfield : 2 < Fintype.card F) (hdirections : Nonempty ι)
    (functional : CoordinateSpace F t →ₗ[F] F)
    (amplitude : Fˣ → ℝ) :
    (∑ p : Fˣ,
        Matrix.mulVec
          (AffineRelationSpectrum.normalizedBlock input D functional)
          amplitude p) =
      AffineRelationSpectrum.lambdaConstant D functional *
        ∑ p : Fˣ, amplitude p := by
  have hfieldReal :
      2 < AffineRelationSpectrum.fieldCard (F := F) := by
    unfold AffineRelationSpectrum.fieldCard
    exact_mod_cast hfield
  have hdirectionsReal :
      0 < AffineRelationSpectrum.directionCount (ι := ι) := by
    unfold AffineRelationSpectrum.directionCount
    exact_mod_cast (Fintype.card_pos_iff.mpr hdirections)
  have hL : 0 < AffineRelationSpectrum.lineCount (F := F) (ι := ι) :=
    mul_pos (by linarith) hdirectionsReal
  have hqTwo :
      AffineRelationSpectrum.fieldCard (F := F) - 2 ≠ 0 := by
    linarith
  simp_rw [AffineRelationSpectrum.normalizedBlock_mulVec]
  rw [← Finset.mul_sum]
  have hsum :
      (∑ p : Fˣ, ((∑ r : Fˣ, amplitude r) - amplitude p)) =
        (AffineRelationSpectrum.fieldCard (F := F) - 2) *
          ∑ r : Fˣ, amplitude r := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, AffineRelationSpectrum.card_units_real]
    ring
  rw [hsum]
  simp only [AffineRelationSpectrum.lambdaConstant,
    AffineRelationSpectrum.normalization]
  field_simp

/-! ## Completeness of the block candidates -/

/-- A random-walk eigen-equation descends to the same eigen-equation in every
Fourier block. -/
theorem fiberCoefficient_eigenvector
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (hfield : 2 < Fintype.card F) (hdirections : Nonempty ι)
    (f : AffineRelation.Column F t → ℝ) (mu : ℝ)
    (heigen : (AffineRelationSpectrum.relationGraph D).walk f =
      fun c ↦ mu * f c)
    (frequency : CoordinateSpace F t) :
    Matrix.mulVec
        (AffineRelationSpectrum.normalizedBlock input D
          (dotFunctional frequency))
        (fiberCoefficient input f frequency) =
      fun p ↦ mu * fiberCoefficient input f frequency p := by
  funext p
  calc
    Matrix.mulVec
        (AffineRelationSpectrum.normalizedBlock input D
          (dotFunctional frequency))
        (fiberCoefficient input f frequency) p =
      fiberCoefficient input
        ((AffineRelationSpectrum.relationGraph D).walk f) frequency p :=
          (fiberCoefficient_walk input D hfield hdirections f frequency p).symm
    _ = coefficient input (fun x ↦ mu * f (p, x)) frequency := by
      unfold fiberCoefficient
      congr 2
      funext x
      exact congrFun heigen (p, x)
    _ = mu * coefficient input (fun x ↦ f (p, x)) frequency :=
      coefficient_smul input (fun x ↦ f (p, x)) mu frequency
    _ = mu * fiberCoefficient input f frequency p := rfl

/-- A nonzero column function has a nonzero Fourier amplitude in at least one
frequency block. -/
theorem exists_nonzero_fiberCoefficient
    (input : FiniteFieldTrace.LiteratureInput F)
    (f : AffineRelation.Column F t → ℝ) (hf : f ≠ 0) :
    ∃ frequency : CoordinateSpace F t,
      fiberCoefficient input f frequency ≠ 0 := by
  classical
  by_contra hnone
  have hall : ∀ frequency : CoordinateSpace F t,
      fiberCoefficient input f frequency = 0 := by
    intro frequency
    exact not_not.mp (not_exists.mp hnone frequency)
  apply hf
  funext c
  rcases c with ⟨p, x⟩
  calc
    f (p, x) = ∑ frequency : CoordinateSpace F t,
        AffineRelation.fourierMode input (dotFunctional frequency)
          (fiberCoefficient input f frequency) (p, x) :=
      (column_inversion input f p x).symm
    _ = 0 := by
      simp [AffineRelation.fourierMode, hall]

/-- Mean zero of a unit-regular relation graph forces the zero-frequency
amplitude to have zero sum on `Fˣ`. -/
theorem zeroFrequency_sum_eq_zero
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (hfield : 2 < Fintype.card F) (hdirections : Nonempty ι)
    (f : AffineRelation.Column F t → ℝ)
    (hmean : (AffineRelationSpectrum.relationGraph D).weightedMean f = 0) :
    (∑ p : Fˣ,
      fiberCoefficient input f (0 : CoordinateSpace F t) p) = 0 := by
  have hregular :=
    AffineRelationSpectrum.relationGraph_isUnitRegular D hfield hdirections
  have hmean' :
      (∑ c : AffineRelation.Column F t, f c) = 0 := by
    unfold WeightedGraph.weightedMean at hmean
    change ∀ v,
      (AffineRelationSpectrum.relationGraph D).degree v = 1 at hregular
    simp_rw [hregular, one_mul] at hmean
    exact hmean
  rw [Fintype.sum_prod_type] at hmean'
  unfold fiberCoefficient coefficient
  simp only [character_zero_frequency, one_mul]
  rw [← Finset.mul_sum, hmean']
  simp

private theorem eigenvalue_unique_of_nonzero
    {J : Type*} [Fintype J]
    (amplitude : J → ℝ) (hamplitude : amplitude ≠ 0)
    (A : (J → ℝ) → (J → ℝ))
    {mu nu : ℝ}
    (hmu : A amplitude = fun j ↦ mu * amplitude j)
    (hnu : A amplitude = fun j ↦ nu * amplitude j) :
    mu = nu := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, amplitude j ≠ 0 := by
    by_contra hnone
    apply hamplitude
    funext j
    exact not_not.mp (not_exists.mp hnone j)
  apply mul_right_cancel₀ hj
  calc
    mu * amplitude j = A amplitude j := (congrFun hmu j).symm
    _ = nu * amplitude j := congrFun hnu j

/-- Every nonzero eigenvector of one normalized block has one of its two
displayed eigenvalues. -/
theorem normalizedBlock_eigenvalue
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (hfield : 2 < Fintype.card F) (hdirections : Nonempty ι)
    (functional : CoordinateSpace F t →ₗ[F] F)
    (amplitude : Fˣ → ℝ) (hamplitude : amplitude ≠ 0)
    (mu : ℝ)
    (heigen : Matrix.mulVec
        (AffineRelationSpectrum.normalizedBlock input D functional)
        amplitude = fun p ↦ mu * amplitude p) :
    mu = AffineRelationSpectrum.lambdaConstant D functional ∨
      mu = AffineRelationSpectrum.lambdaOrthogonal D functional := by
  classical
  by_cases hsum : ∑ p : Fˣ, amplitude p = 0
  · right
    exact eigenvalue_unique_of_nonzero amplitude hamplitude
      (Matrix.mulVec
        (AffineRelationSpectrum.normalizedBlock input D functional))
      heigen
      (AffineRelationSpectrum.normalizedBlock_zeroSum_eigenvector
        input D functional amplitude hsum)
  · left
    apply mul_right_cancel₀ hsum
    calc
      mu * (∑ p : Fˣ, amplitude p) =
          ∑ p : Fˣ, mu * amplitude p := by
        rw [Finset.mul_sum]
      _ = ∑ p : Fˣ,
          Matrix.mulVec
            (AffineRelationSpectrum.normalizedBlock input D functional)
            amplitude p := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact (congrFun heigen p).symm
      _ = AffineRelationSpectrum.lambdaConstant D functional *
          ∑ p : Fˣ, amplitude p :=
        sum_normalizedBlock_mulVec input D hfield hdirections
          functional amplitude

/-- The finite Fourier basis closes the `complete` field of the interface:
every mean-zero eigenvalue of the concrete relation graph is one of the block
candidates computed in Lemma 3.7. -/
theorem complete
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (hfield : 2 < Fintype.card F) (hdirections : Nonempty ι) :
    ∀ mu,
      AffineRelationSpectrum.IsMeanZeroEigenvalue
          (AffineRelationSpectrum.relationGraph D) mu →
        AffineRelationSpectrum.IsBlockCandidate D mu := by
  intro mu hmu
  rcases hmu with ⟨f, hf, hmean, heigen⟩
  obtain ⟨frequency, hfrequencyAmplitude⟩ :=
    exists_nonzero_fiberCoefficient input f hf
  let amplitude : Fˣ → ℝ := fiberCoefficient input f frequency
  have hblock : Matrix.mulVec
      (AffineRelationSpectrum.normalizedBlock input D
        (dotFunctional frequency)) amplitude =
      fun p ↦ mu * amplitude p :=
    fiberCoefficient_eigenvector input D hfield hdirections f mu heigen frequency
  by_cases hfrequency : frequency = 0
  · left
    subst frequency
    have hsum : ∑ p : Fˣ, amplitude p = 0 :=
      zeroFrequency_sum_eq_zero input D hfield hdirections f hmean
    have hzeroBlock : Matrix.mulVec
        (AffineRelationSpectrum.normalizedBlock input D
          (0 : CoordinateSpace F t →ₗ[F] F)) amplitude =
        fun p ↦ AffineRelationSpectrum.lambdaOrthogonal D
          (0 : CoordinateSpace F t →ₗ[F] F) * amplitude p :=
      AffineRelationSpectrum.normalizedBlock_zeroSum_eigenvector
        input D (0 : CoordinateSpace F t →ₗ[F] F) amplitude hsum
    apply eigenvalue_unique_of_nonzero amplitude hfrequencyAmplitude
      (Matrix.mulVec (AffineRelationSpectrum.normalizedBlock input D
        (0 : CoordinateSpace F t →ₗ[F] F)))
    · simpa only [dotFunctional_zero] using hblock
    · exact hzeroBlock
  · right
    have hfunctional : dotFunctional frequency ≠
        (0 : CoordinateSpace F t →ₗ[F] F) := by
      intro hzero
      apply hfrequency
      apply dotFunctional_injective
      simpa only [dotFunctional_zero] using hzero
    refine ⟨dotFunctional frequency, hfunctional, ?_⟩
    exact normalizedBlock_eigenvalue input D hfield hdirections
      (dotFunctional frequency) amplitude hfrequencyAmplitude mu hblock

/-- Fully assembled Fourier interface, using the general finite regular-graph
facts for its connectedness and `L²` fields. -/
theorem interface
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (hfield : 2 < Fintype.card F) (hdirections : Nonempty ι) :
    AffineRelationSpectrum.FourierInterface input D :=
  AffineRelationSpectrum.FourierInterface.ofComplete input D hfield hdirections
    (complete input D hfield hdirections)

end FiniteFourierBasis

end HDXLean
