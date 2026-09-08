import HDXLean.Asymptotics
import HDXLean.RevisedBinomial
import HDXLean.BooleanCube
import HDXLean.Directions
import Mathlib.Data.Nat.Choose.Central
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Algebraic-geometric direction sets

This file formalizes Section 4 of the paper at an explicit certificate boundary.
The Garcia--Stichtenoth tower, the Riemann--Roch/zero-divisor facts, and
Eisenbud's theorem are cited results in the paper, so they occur below as fields
of input structures rather than as untracked global assumptions.  The passage from those
inputs to the family asserted by Lemma 3.2, including the rank-one matrix
calculation, cardinal arithmetic, relative-distance calculation, and the
eventual central-binomial estimate, is proved here.

The generic certificate interfaces retained below are convenient adapters.
Their project-owned content is discharged concretely: rank-one determinant
affinity is proved here, Boolean-cube interpolation is proved in
`BooleanCube`, and the complete Cauchy--Binet coefficient expansion and its
concrete Section 4 assembly appear in `BooleanCubeMinorExpansion`,
`AlgebraicGeometryCauchyBinet`, and `AlgebraicGeometryConcrete`.  The outer
theorem uses that concrete path, leaving only results explicitly cited by the
paper at the literature boundary.
-/

namespace HDXLean

open scoped BigOperators

universe u v w

section Parameters

/-- The fixed square field `F = ᵓ_(q²)`, with `q = 2^h ≥ 8`. -/
structure SquareFieldParameters (F : Type u) [Field F] [Fintype F] where
  h : ℕ
  q : ℕ
  h_pos : 0 < h
  q_eq_two_pow : q = 2 ^ h
  q_ge_eight : 8 ≤ q
  card_field : Fintype.card F = q ^ 2

namespace SquareFieldParameters

variable {F : Type u} [Field F] [Fintype F]

theorem q_pos (P : SquareFieldParameters F) : 0 < P.q := by
  exact lt_of_lt_of_le (by norm_num) P.q_ge_eight

theorem seven_mul_h_pos (P : SquareFieldParameters F) : 0 < 7 * P.h := by
  exact Nat.mul_pos (by norm_num) P.h_pos

theorem q_sub_five_pos (P : SquareFieldParameters F) : 0 < P.q - 5 := by
  have := P.q_ge_eight
  omega

end SquareFieldParameters

end Parameters

section Tower

variable {F : Type u} [Field F] [Fintype F]

/-- Elementary epsilon formulation of convergence of the point/genus ratio. -/
def PointGenusRatioConverges (pointCount genus : ℕ → ℕ) (limit : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Eventually fun r ↦
    |(pointCount r : ℝ) / (genus r : ℝ) - limit| < ε

/--
The dependency supplied by Garcia--Stichtenoth [GS95], together with the
algorithmic result cited from [GX22].  `selectedPointCapacity` is the exact
eventual corollary of the ratio limit used by the construction: one point is
reserved for `P∞`, and `(q-2)g` further points are selected.
-/
structure GarciaStichtenothTowerInput (P : SquareFieldParameters F) where
  genus : ℕ → ℕ
  rationalPointCount : ℕ → ℕ
  genus_tendsToInfinity : TendsToInfinity genus
  point_genus_ratio :
    PointGenusRatioConverges rationalPointCount genus (P.q - 1 : ℕ)
  selectedPointCapacity : Eventually fun r ↦
    1 + (P.q - 2) * genus r ≤ rationalPointCount r
  explicitConstruction : Prop
  explicitConstruction_proof : explicitConstruction

/-- Faithful proof-relevant form of Lemma 4.1. -/
theorem lemma_4_1 {P : SquareFieldParameters F}
    (tower : GarciaStichtenothTowerInput P) :
    TendsToInfinity tower.genus ∧
      PointGenusRatioConverges tower.rationalPointCount tower.genus
        (P.q - 1 : ℕ) ∧
      tower.explicitConstruction := by
  exact ⟨tower.genus_tendsToInfinity, tower.point_genus_ratio,
    tower.explicitConstruction_proof⟩

end Tower

section RankOne

variable {F : Type u} [Field F]
variable {t : ℕ} {I : Type v} [Fintype I]
variable (D : DirectionSet F t I)

/-- The rank-one matrix `a bᵀ`. -/
def rankOneMatrix {R C : Type*} (a : R → F) (b : C → F) : Matrix R C F :=
  fun i j ↦ a i * b j

omit [Fintype I] in
/-- If at least two rows are selected from a rank-one matrix, the
corresponding term in the multilinear expansion of the determinant is zero. -/
theorem det_piecewise_rankOne_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n F) (a b : n → F) (scalar : F)
    (s : Finset n) (hs : 2 ≤ s.card) :
    (Matrix.detRowAlternating : (n → F) [⋀^n]→ₗ[F] F)
      (s.piecewise
        (Matrix.of.symm (scalar • rankOneMatrix a b))
        (Matrix.of.symm C)) = 0 := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
  let w : n → (n → F) := s.piecewise
    (Matrix.of.symm (scalar • rankOneMatrix a b)) (Matrix.of.symm C)
  have hwi : w i = (scalar * a i) • b := by
    funext k
    simp [w, hi, rankOneMatrix, mul_assoc]
  have hwj : (Function.update w i b) j = (scalar * a j) • b := by
    have hji : j ≠ i := Ne.symm hij
    funext k
    simp [w, Finset.piecewise, hj, hji, rankOneMatrix, mul_assoc]
  have hiUpdate : Function.update w i ((scalar * a i) • b) = w := by
    rw [← hwi, Function.update_eq_self]
  have hjUpdate :
      Function.update (Function.update w i b) j ((scalar * a j) • b) =
        Function.update w i b := by
    rw [← hwj, Function.update_eq_self]
  change (Matrix.detRowAlternating : (n → F) [⋀^n]→ₗ[F] F) w = 0
  rw [← hiUpdate, AlternatingMap.map_update_smul, ← hjUpdate,
    AlternatingMap.map_update_smul]
  have hequal :
      (Function.update (Function.update w i b) j b) i =
        (Function.update (Function.update w i b) j b) j := by
    simp [hij]
  rw [(Matrix.detRowAlternating : (n → F) [⋀^n]→ₗ[F] F).map_eq_zero_of_eq
    _ hequal hij]
  simp

omit [Fintype I] in
/-- The determinant is affine along every rank-one line.  This proves the
elementary determinant-update step used in Lemma 4.6 without assuming that
the starting matrix is invertible. -/
theorem det_add_smul_rankOne_affine
    {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n F) (a b : n → F) :
    ∃ slope : F, ∀ scalar : F,
      (C + scalar • rankOneMatrix a b).det = C.det + slope * scalar := by
  classical
  let R : Matrix n n F := rankOneMatrix a b
  let slope : F :=
    ∑ s ∈ (Finset.univ.erase (∅ : Finset n)),
      (Matrix.detRowAlternating : (n → F) [⋀^n]→ₗ[F] F)
        (s.piecewise (Matrix.of.symm R) (Matrix.of.symm C))
  refine ⟨slope, fun scalar ↦ ?_⟩
  let detAlt : (n → F) [⋀^n]→ₗ[F] F := Matrix.detRowAlternating
  change detAlt (Matrix.of.symm (C + scalar • R)) = C.det + slope * scalar
  have hrows : Matrix.of.symm (C + scalar • R) =
      Matrix.of.symm (scalar • R) + Matrix.of.symm C := by
    ext i j
    simp [add_comm]
  rw [hrows, detAlt.map_add_univ]
  rw [← Finset.sum_erase_add _ _
    (Finset.mem_univ (∅ : Finset n))]
  have hsum :
      (∑ s ∈ (Finset.univ.erase (∅ : Finset n)),
          detAlt (s.piecewise (Matrix.of.symm (scalar • R))
            (Matrix.of.symm C))) =
        scalar * slope := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hsMem
    have hsne : s ≠ ∅ := Finset.ne_of_mem_erase hsMem
    have hspos : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hsne)
    by_cases hsone : s.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hsone
      simp only [Finset.piecewise_singleton]
      change detAlt
          (Function.update (Matrix.of.symm C) i
            (scalar • (Matrix.of.symm R) i)) =
        scalar * detAlt
          (Function.update (Matrix.of.symm C) i (Matrix.of.symm R i))
      simpa only [smul_eq_mul] using
        detAlt.map_update_smul (Matrix.of.symm C) i scalar
          (Matrix.of.symm R i)
    · have hstwo : 2 ≤ s.card := by omega
      have hzeroScalar :
          detAlt (s.piecewise
            (Matrix.of.symm (scalar • rankOneMatrix a b))
            (Matrix.of.symm C)) = 0 :=
          det_piecewise_rankOne_eq_zero C a b scalar s hstwo
      have hzeroOne :
          detAlt (s.piecewise
            (Matrix.of.symm (rankOneMatrix a b))
            (Matrix.of.symm C)) = 0 :=
          by simpa using det_piecewise_rankOne_eq_zero C a b 1 s hstwo
      change detAlt (s.piecewise (Matrix.of.symm (scalar • R))
          (Matrix.of.symm C)) =
        scalar * detAlt (s.piecewise (Matrix.of.symm R) (Matrix.of.symm C))
      simpa [R] using hzeroScalar.trans (by rw [hzeroOne, mul_zero])
  rw [hsum]
  simp only [Finset.piecewise_empty]
  have hdetC : detAlt (Matrix.of.symm C) = C.det := rfl
  rw [hdetC]
  ring

/--
Multiplication-matrix entries as linear forms on `Wᵛ ≃ F^t`.
`entry_at_evaluation` is the multiplication/evaluation identity
`e_P(u_i z_j) = u_i(P) z_j(P)`.
-/
structure MultiplicationMatrixData where
  Row : Type
  Column : Type
  [rowFintype : Fintype Row]
  [columnFintype : Fintype Column]
  entry : Row → Column → CoordinateSpace F t →ₗ[F] F
  uEvaluation : I → Row → F
  zEvaluation : I → Column → F
  entry_at_evaluation : ∀ i row column,
    entry row column (D.representative i) =
      uEvaluation i row * zEvaluation i column

attribute [instance] MultiplicationMatrixData.rowFintype
  MultiplicationMatrixData.columnFintype

namespace MultiplicationMatrixData

/-- The matrix `M(x) = (x(u_i z_j))`. -/
def matrix (M : MultiplicationMatrixData D) (x : CoordinateSpace F t) :
    Matrix M.Row M.Column F :=
  fun row column ↦ M.entry row column x

/-- Equation (4.1): evaluation changes the multiplication matrix by rank one. -/
theorem lemma_4_6_rank_one_update (M : MultiplicationMatrixData D)
    (x : CoordinateSpace F t) (i : I) (scalar : F) :
    M.matrix D (x + scalar • D.representative i) =
      M.matrix D x + scalar •
        rankOneMatrix (M.uEvaluation i) (M.zEvaluation i) := by
  ext row column
  simp only [matrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    map_add, map_smul, rankOneMatrix]
  rw [M.entry_at_evaluation]

end MultiplicationMatrixData

/-- A maximal minor is specified by choosing, for every minor index, one
distinct column for each row.  This is data rather than a proof obligation. -/
structure MaximalMinorSelection
    (M : MultiplicationMatrixData D) (J : Type*) where
  column : J → M.Row → M.Column
  column_injective : ∀ j, Function.Injective (column j)

/-- The determinant of the square submatrix selected by `selection`. -/
noncomputable def selectedMaximalMinor
    (M : MultiplicationMatrixData D) {J : Type*}
    (selection : MaximalMinorSelection D M J) :
    J → CoordinateSpace F t → F := by
  classical
  exact fun j x ↦
    (Matrix.of fun row column ↦
      M.entry row (selection.column j column) x).det

/-- A selected maximal minor is affine on every rank-one direction.  This is
the concrete determinant calculation hidden in the paper's proof of Lemma
4.6. -/
theorem selectedMaximalMinor_update
    (M : MultiplicationMatrixData D) {J : Type*}
    (selection : MaximalMinorSelection D M J) (j : J)
    (x : CoordinateSpace F t) (i : I) :
    ∃ slope : F, ∀ scalar : F,
      selectedMaximalMinor D M selection j
          (x + scalar • D.representative i) =
        selectedMaximalMinor D M selection j x + slope * scalar := by
  classical
  let C : Matrix M.Row M.Row F := Matrix.of fun row column ↦
    M.entry row (selection.column j column) x
  let a : M.Row → F := M.uEvaluation i
  let b : M.Row → F := fun column ↦
    M.zEvaluation i (selection.column j column)
  obtain ⟨slope, hslope⟩ := det_add_smul_rankOne_affine C a b
  refine ⟨slope, fun scalar ↦ ?_⟩
  have hmatrix :
      Matrix.of (fun row column ↦
        M.entry row (selection.column j column)
          (x + scalar • D.representative i)) =
        C + scalar • rankOneMatrix a b := by
    ext row column
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, map_add, map_smul, C, a, b, rankOneMatrix]
    rw [M.entry_at_evaluation]
  unfold selectedMaximalMinor
  rw [hmatrix]
  exact hslope scalar

/--
An adapter expressing rank-one determinant affinity for a family of chosen
minors.  Literal selected minors obtain this certificate from the proved
constructor `RankOneDeterminantCertificate.ofSelection` below.
-/
structure RankOneDeterminantCertificate
    (M : MultiplicationMatrixData D) (J : Type*) where
  minor : J → CoordinateSpace F t → F
  minor_update : ∀ j x i, ∃ slope : F, ∀ scalar : F,
    minor j (x + scalar • D.representative i) =
      minor j x + slope * scalar

namespace RankOneDeterminantCertificate

/-- Construct the determinant certificate from literal selected maximal
minors.  No determinant identity remains as input. -/
noncomputable def ofSelection
    (M : MultiplicationMatrixData D) {J : Type*}
    (selection : MaximalMinorSelection D M J) :
    RankOneDeterminantCertificate D M J where
  minor := selectedMaximalMinor D M selection
  minor_update := fun j x i ↦
    selectedMaximalMinor_update D M selection j x i

end RankOneDeterminantCertificate

/-- Lemma 4.6: each certified maximal minor is affine on every selected line. -/
theorem lemma_4_6 (M : MultiplicationMatrixData D) {J : Type*}
    (certificate : RankOneDeterminantCertificate D M J) (j : J) :
    certificate.minor j ∈ affineFunctions F D := by
  rw [mem_affineFunctions_iff]
  intro i x
  obtain ⟨slope, hslope⟩ := certificate.minor_update j x i
  exact ⟨certificate.minor j x, slope, hslope⟩

end RankOne

section Independence

variable {F : Type u} [Field F]
variable {t : ℕ} {I : Type v} [Fintype I]
variable (D : DirectionSet F t I)

/--
The cited consequence of Eisenbud [Eis05] used in Proposition 4.7.  The type
`PolynomialModel` can be instantiated by the span of the maximal-minor
polynomials.  The premise `oneGeneric` records the hypothesis established from
geometric integrality in the paper.
-/
structure EisenbudMaximalMinorInput (J : Type*) where
  PolynomialModel : Type u
  [polynomialAddCommGroup : AddCommGroup PolynomialModel]
  [polynomialModule : Module F PolynomialModel]
  polynomialMinor : J → PolynomialModel
  oneGeneric : Prop
  oneGeneric_proof : oneGeneric
  maximalMinors_independent : oneGeneric →
    LinearIndependent F polynomialMinor

attribute [instance] EisenbudMaximalMinorInput.polynomialAddCommGroup
attribute [instance] EisenbudMaximalMinorInput.polynomialModule

/--
The internal Cauchy--Binet/Boolean-cube transfer in Proposition 4.7.  Its
injectivity field says exactly that the bounded multilinear polynomial model
is detected by evaluation on the selected finite vector space.
-/
structure BooleanCubeEvaluationCertificate {J : Type*}
    (eisenbud : EisenbudMaximalMinorInput (F := F) J)
    (minor : J → CoordinateSpace F t → F) where
  evaluate : eisenbud.PolynomialModel →ₗ[F] (CoordinateSpace F t → F)
  injective : Function.Injective evaluate
  evaluates_minor : ∀ j, evaluate (eisenbud.polynomialMinor j) = minor j

namespace BooleanCubeEvaluationCertificate

/-- Construct the evaluation certificate from a squarefree-monomial model.
Injectivity is supplied by the proved Boolean-cube interpolation theorem, so
the only remaining datum is the concrete coefficient expansion of each
maximal minor. -/
noncomputable def ofSquarefreeModel {J : Type*}
    (eisenbud : EisenbudMaximalMinorInput (F := F) J)
    (minor : J → CoordinateSpace F t → F)
    (encoding : eisenbud.PolynomialModel ≃ₗ[F]
      BooleanCube.Coefficients (F := F) t)
    (evaluates_minor : ∀ j,
      BooleanCube.evaluationLinear (F := F) t
          (encoding (eisenbud.polynomialMinor j)) = minor j) :
    BooleanCubeEvaluationCertificate eisenbud minor where
  evaluate := (BooleanCube.evaluationLinear (F := F) t).comp encoding.toLinearMap
  injective :=
    (BooleanCube.evaluationLinear_injective (F := F) t).comp encoding.injective
  evaluates_minor := fun j ↦ evaluates_minor j

end BooleanCubeEvaluationCertificate

/-- Proposition 4.7: the maximal minors are independent as functions. -/
theorem proposition_4_7 {J : Type*}
    (eisenbud : EisenbudMaximalMinorInput (F := F) J)
    (minor : J → CoordinateSpace F t → F)
    (evaluation : BooleanCubeEvaluationCertificate eisenbud minor) :
    LinearIndependent F minor := by
  have hkernel : LinearMap.ker evaluation.evaluate = ⊥ :=
    LinearMap.ker_eq_bot.mpr evaluation.injective
  have hmapped :=
    (eisenbud.maximalMinors_independent eisenbud.oneGeneric_proof).map'
      evaluation.evaluate hkernel
  rw [show minor = evaluation.evaluate ∘ eisenbud.polynomialMinor by
    funext j
    exact (evaluation.evaluates_minor j).symm]
  exact hmapped

end Independence

section Levels

variable {F : Type u} [Field F] [Fintype F]
variable (P : SquareFieldParameters F)

/--
The Riemann--Roch and evaluation-code data at one tower level.  The fields
`directions` and `zeroDivisorDistance` are precisely the consequences of the
cited Riemann--Roch dimension, injectivity, point-separation, and zero-divisor
results from [Sti09].
-/
structure RiemannRochLevelInput (g : ℕ) where
  t : ℕ
  t_eq : t = 2 * g + 1
  directions : DirectionSet F t (Fin ((P.q - 2) * g))
  zeroDivisorDistance :
    HasLowerDistance F directions ((P.q - 5) * g)

/--
All finite multiplication/minor data at a Riemann--Roch level.  The number of
minor indices is `choose (3k) k`, where `k = ⌊g/4⌋`.
-/
structure MaximalMinorLevelData {g : ℕ} (level : RiemannRochLevelInput P g) where
  matrix : MultiplicationMatrixData level.directions
  MinorIndex : Type
  [minorFintype : Fintype MinorIndex]
  index_card : Fintype.card MinorIndex = Nat.choose (3 * (g / 4)) (g / 4)
  selection : MaximalMinorSelection level.directions matrix MinorIndex
  eisenbud : EisenbudMaximalMinorInput (F := F) MinorIndex
  evaluation : BooleanCubeEvaluationCertificate eisenbud
    (selectedMaximalMinor level.directions matrix selection)

attribute [instance] MaximalMinorLevelData.minorFintype

namespace MaximalMinorLevelData

/-- The determinant certificate is now computed from the selected literal
submatrices; it is not supplied as an independent proof field. -/
noncomputable def determinant {g : ℕ}
    {level : RiemannRochLevelInput P g}
    (data : MaximalMinorLevelData P level) :
    RankOneDeterminantCertificate level.directions data.matrix
      data.MinorIndex :=
  RankOneDeterminantCertificate.ofSelection level.directions
    data.matrix data.selection

/-- The maximal minors, regarded as elements of the affine-function subspace. -/
noncomputable def minorInAffine {g : ℕ} {level : RiemannRochLevelInput P g}
    (data : MaximalMinorLevelData P level) (j : data.MinorIndex) :
    affineFunctions F level.directions :=
  ⟨data.determinant.minor j, lemma_4_6 level.directions data.matrix data.determinant j⟩

/-- The certified maximal minors are independent inside `A(D)`. -/
theorem minorInAffine_linearIndependent {g : ℕ}
    {level : RiemannRochLevelInput P g}
    (data : MaximalMinorLevelData P level) :
    LinearIndependent F data.minorInAffine := by
  apply LinearIndependent.of_comp (affineFunctions F level.directions).subtype
  rw [show (affineFunctions F level.directions).subtype ∘ data.minorInAffine =
      data.determinant.minor by rfl]
  exact proposition_4_7 data.eisenbud data.determinant.minor data.evaluation

/-- The dimension bound furnished by the independent maximal minors. -/
theorem minorCount_le_finrank {g : ℕ}
    {level : RiemannRochLevelInput P g}
    (data : MaximalMinorLevelData P level) :
    Nat.choose (3 * (g / 4)) (g / 4) ≤
      Module.finrank F (affineFunctions F level.directions) := by
  rw [← data.index_card]
  exact data.minorInAffine_linearIndependent.fintype_card_le_finrank

end MaximalMinorLevelData

/--
The cited Section 4 inputs that construct the level data once the tower has
enough rational points.  No global existence statement is made: an application
must supply this record from [Sti09], [Eis05], and the explicit tower.
-/
structure SectionFourInput (tower : GarciaStichtenothTowerInput P) where
  constructionThreshold : ℕ
  level : ∀ r, constructionThreshold ≤ r →
    1 + (P.q - 2) * tower.genus r ≤ tower.rationalPointCount r →
      RiemannRochLevelInput P (tower.genus r)
  minors : ∀ r (hr : constructionThreshold ≤ r)
      (hpoints : 1 + (P.q - 2) * tower.genus r ≤ tower.rationalPointCount r),
    MaximalMinorLevelData P (level r hr hpoints)
  explicitAssembly : Prop
  explicitAssembly_proof : explicitAssembly

end Levels

section Arithmetic

/-- The elementary bound `n ≤ 2^(⌈n/4⌉)` used to absorb the polynomial
factor in the central-binomial estimate. -/
theorem nat_le_two_pow_quarterCeil {n : ℕ} (hn : 16 ≤ n) :
    n ≤ 2 ^ ((n + 3) / 4) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hsmall : n < 20
      · have hn_cases : n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 := by omega
        rcases hn_cases with h | h | h | h
        · subst n
          norm_num
        · subst n
          norm_num
        · subst n
          norm_num
        · subst n
          norm_num
      · have hprev : 16 ≤ n - 4 := by omega
        have ihprev := ih (n - 4) (by omega) hprev
        calc
          n ≤ 2 * (n - 4) := by omega
          _ ≤ 2 * 2 ^ (((n - 4) + 3) / 4) := Nat.mul_le_mul_left 2 ihprev
          _ = 2 ^ ((n + 3) / 4) := by
            rw [← pow_succ']
            congr 1
            omega

/-- The exact eventual numerical estimate used at the end of Section 4. -/
theorem paper_centralBinom_lower {g : ℕ} (hg : 40 ≤ g / 3) :
    2 ^ (2 * (2 * g + 1) / 7) ≤ Nat.centralBinom (g / 3) := by
  let n := g / 3
  let e := 2 * (2 * g + 1) / 7
  have hn : 40 ≤ n := by simpa [n] using hg
  have hg_upper : g ≤ 3 * n + 2 := by
    dsimp [n]
    omega
  have he_gap : e + (n + 3) / 4 ≤ 2 * n := by
    dsimp [e]
    omega
  have he : e ≤ 2 * n := le_trans (Nat.le_add_right e ((n + 3) / 4)) he_gap
  have hgap : (n + 3) / 4 ≤ 2 * n - e := by omega
  have hn_power : n ≤ 2 ^ (2 * n - e) :=
    (nat_le_two_pow_quarterCeil (by omega)).trans
      (Nat.pow_le_pow_right (by omega) hgap)
  have hmul : n * 2 ^ e ≤ 2 ^ (2 * n) := by
    calc
      n * 2 ^ e ≤ 2 ^ (2 * n - e) * 2 ^ e :=
        Nat.mul_le_mul_right (2 ^ e) hn_power
      _ = 2 ^ ((2 * n - e) + e) := by rw [← pow_add]
      _ = 2 ^ (2 * n) := by
        congr 1
        omega
  have hcentral : 2 ^ (2 * n) < n * Nat.centralBinom n := by
    calc
      2 ^ (2 * n) = 4 ^ n := by
        rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul]
      _ < n * Nat.centralBinom n := Nat.four_pow_lt_mul_centralBinom n (by omega)
  have hstrict : n * 2 ^ e < n * Nat.centralBinom n := lt_of_le_of_lt hmul hcentral
  have : 2 ^ e < Nat.centralBinom n := (Nat.mul_lt_mul_left (by omega)).mp hstrict
  exact this.le

/-- Reindexing a divergent natural sequence by a fixed forward shift preserves
divergence. -/
theorem TendsToInfinity.shift {f : ℕ → ℕ} (hf : TendsToInfinity f) (shift : ℕ) :
    TendsToInfinity fun r ↦ f (r + shift) := by
  intro B
  rcases hf B with ⟨r₀, hr₀⟩
  refine ⟨r₀, fun r hr ↦ hr₀ (r + shift) ?_⟩
  omega

/-- Converting the paper's `q²`-power to its binary exponent.  Natural
division makes the intended rounding explicit. -/
theorem squareField_power_le_binary_power {F : Type u} [Field F] [Fintype F]
    (P : SquareFieldParameters F) (t : ℕ) :
    (P.q ^ 2) ^ (t / (7 * P.h)) ≤ 2 ^ (2 * t / 7) := by
  rw [P.q_eq_two_pow, ← pow_mul, ← pow_mul]
  apply Nat.pow_le_pow_right (by omega)
  have hmul : 7 * P.h * (t / (7 * P.h)) ≤ t := Nat.mul_div_le t (7 * P.h)
  have hh : P.h * (t / (7 * P.h)) ≤ t / 7 := by
    apply (Nat.le_div_iff_mul_le (by omega)).2
    nlinarith
  calc
    P.h * (2 * (t / (7 * P.h))) = 2 * (P.h * (t / (7 * P.h))) := by
      ac_rfl
    _ ≤ 2 * (t / 7) := Nat.mul_le_mul_left 2 hh
    _ ≤ 2 * t / 7 := by omega

end Arithmetic

section Assembly

variable {F : Type u} [Field F] [Fintype F]
variable (P : SquareFieldParameters F)

/-- A precise, integer-rounded formulation of the direction family in Lemma 3.2. -/
structure Lemma32DirectionFamily where
  t : ℕ → ℕ
  genus : ℕ → ℕ
  genus_lower_bound : ∀ r, 120 ≤ genus r
  directions : (r : ℕ) → DirectionSet F (t r) (Fin ((P.q - 2) * genus r))
  t_eq : ∀ r, t r = 2 * genus r + 1
  t_tendsToInfinity : TendsToInfinity t
  size_linear : LinearBounded (fun r ↦ (P.q - 2) * genus r) t
  lowerDistance : ∀ r,
    HasLowerDistance F (directions r) ((P.q - 5) * genus r)
  relativeDistance : ∀ r,
    (P.q - 2) * ((P.q - 5) * genus r) ≥
      (P.q - 5) * ((P.q - 2) * genus r)
  affineDimensionLower : ∀ r,
    (P.q ^ 2) ^ (t r / (7 * P.h)) ≤
      Module.finrank F (affineFunctions F (directions r))
  /-- Stronger than the revised paper's real power `2^(t/3)`. -/
  affineDimensionLower_ceiling : ∀ r,
    2 ^ ((t r + 2) / 3) ≤
      Module.finrank F (affineFunctions F (directions r))
  explicitConstruction : Prop
  explicitConstruction_proof : explicitConstruction

/-- Lemma 3.2, assembled from the explicitly supplied cited dependencies. -/
theorem lemma_3_2
    (tower : GarciaStichtenothTowerInput P)
    (input : SectionFourInput P tower) :
    Nonempty (Lemma32DirectionFamily P) := by
  rcases tower.selectedPointCapacity with ⟨pointThreshold, hpoints⟩
  rcases tower.genus_tendsToInfinity 32400 with ⟨largeThreshold, hlarge⟩
  let shift := max input.constructionThreshold (max pointThreshold largeThreshold)
  have hconstruction (r : ℕ) : input.constructionThreshold ≤ r + shift := by
    dsimp [shift]
    omega
  have hpointThreshold (r : ℕ) : pointThreshold ≤ r + shift := by
    dsimp [shift]
    omega
  have hlargeThreshold (r : ℕ) : largeThreshold ≤ r + shift := by
    dsimp [shift]
    omega
  let points (r : ℕ) := hpoints (r + shift) (hpointThreshold r)
  let level (r : ℕ) := input.level (r + shift) (hconstruction r) (points r)
  let minors (r : ℕ) := input.minors (r + shift) (hconstruction r) (points r)
  have hnew (r : ℕ) : 2 ^ (((level r).t + 2) / 3) ≤
      Module.finrank F (affineFunctions F (level r).directions) := by
    conv_lhs => rw [(level r).t_eq]
    exact (revised_genus_binomial_lower (hlarge (r + shift) (hlargeThreshold r))).trans
      (minors r).minorCount_le_finrank
  refine ⟨?_⟩
  refine
    { t := fun r ↦ (level r).t
      genus := fun r ↦ tower.genus (r + shift)
      genus_lower_bound := fun r ↦ (by
        have := hlarge (r + shift) (hlargeThreshold r)
        omega)
      directions := fun r ↦ (level r).directions
      t_eq := fun r ↦ (level r).t_eq
      t_tendsToInfinity := ?_
      size_linear := ?_
      lowerDistance := fun r ↦ (level r).zeroDivisorDistance
      relativeDistance := ?_
      affineDimensionLower := ?_
      affineDimensionLower_ceiling := hnew
      explicitConstruction :=
        tower.explicitConstruction ∧ input.explicitAssembly
      explicitConstruction_proof :=
        ⟨tower.explicitConstruction_proof, input.explicitAssembly_proof⟩ }
  · have hgenus := tower.genus_tendsToInfinity.shift shift
    exact hgenus.mono <| Eventually.of_forall fun r ↦ by
      rw [(level r).t_eq]
      omega
  · refine ⟨P.q - 2, Eventually.of_forall fun r ↦ ?_⟩
    change (P.q - 2) * tower.genus (r + shift) ≤
      (P.q - 2) * ((level r).t + 1)
    rw [(level r).t_eq]
    exact Nat.mul_le_mul_left (P.q - 2) (by omega)
  · intro r
    exact le_of_eq (by ac_rfl)
  · intro r
    calc
      (P.q ^ 2) ^ ((level r).t / (7 * P.h))
          ≤ 2 ^ (2 * (level r).t / 7) :=
        squareField_power_le_binary_power P (level r).t
      _ ≤ 2 ^ (((level r).t + 2) / 3) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ Module.finrank F (affineFunctions F (level r).directions) :=
        hnew r

end Assembly

end HDXLean
