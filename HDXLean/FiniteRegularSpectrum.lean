import HDXLean.AffineRelationSpectrum
import HDXLean.AffineRelationCombinatorics
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Finite regular graph facts used by the Fourier interface

This file separates two standard finite-dimensional facts from the Fourier
calculation.  The first is purely combinatorial: a disconnected nonnegative
symmetric graph whose weighted degree is one has a nonconstant mean-zero
eigenfunction with eigenvalue one.  The proof below constructs that function
from a connected component.
-/

namespace HDXLean

open scoped BigOperators

namespace WeightedGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Every vertex has weighted degree one. -/
def IsUnitRegular (G : WeightedGraph V) : Prop :=
  ∀ v, G.degree v = 1

private theorem reachable_symm (G : WeightedGraph V) {u v : V}
    (h : Relation.ReflTransGen G.Adj u v) :
    Relation.ReflTransGen G.Adj v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.head ((G.adj_symm).mpr hyz) ih

private theorem reachable_adjacent_iff (G : WeightedGraph V) (root u v : V)
    (huv : G.Adj u v) :
    Relation.ReflTransGen G.Adj root u ↔
      Relation.ReflTransGen G.Adj root v := by
  constructor
  · intro h
    exact Relation.ReflTransGen.tail h huv
  · intro h
    exact Relation.ReflTransGen.tail h ((G.adj_symm).mp huv)

private theorem weight_eq_zero_of_not_adj (G : WeightedGraph V) {u v : V}
    (h : ¬ G.Adj u v) : G.weight u v = 0 := by
  apply le_antisymm
  · exact not_lt.mp h
  · exact G.weight_nonneg u v

/-- A function constant on connected components is fixed by the random walk
of a unit-regular graph. -/
theorem walk_eq_self_of_constant_on_adjacent (G : WeightedGraph V)
    (hregular : G.IsUnitRegular) (f : V → ℝ)
    (hconstant : ∀ {u v}, G.Adj u v → f u = f v) :
    G.walk f = f := by
  funext u
  have hsum : (∑ v : V, G.weight u v * f v) = G.degree u * f u := by
    rw [WeightedGraph.degree, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _hv
    by_cases hadj : G.Adj u v
    · rw [hconstant hadj]
    · rw [weight_eq_zero_of_not_adj G hadj]
      simp
  rw [WeightedGraph.walk, hsum, hregular u]
  norm_num

/-- A disconnected unit-regular finite weighted graph has eigenvalue one on
the mean-zero subspace. -/
theorem one_meanZeroEigenvalue_of_not_connected
    (G : WeightedGraph V) (hregular : G.IsUnitRegular)
    (hconnected : ¬ G.Connected) :
    AffineRelationSpectrum.IsMeanZeroEigenvalue G 1 := by
  classical
  unfold Connected at hconnected
  push Not at hconnected
  obtain ⟨root, outsideVertex, houtside⟩ := hconnected
  let inComponent : Finset V := Finset.univ.filter fun v ↦
    Relation.ReflTransGen G.Adj root v
  let outComponent : Finset V := Finset.univ.filter fun v ↦
    ¬ Relation.ReflTransGen G.Adj root v
  let f : V → ℝ := fun v ↦
    if Relation.ReflTransGen G.Adj root v then
      (outComponent.card : ℝ)
    else -((inComponent.card : ℝ))
  have hrootIn : root ∈ inComponent := by
    change root ∈ Finset.univ.filter fun v ↦
      Relation.ReflTransGen G.Adj root v
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩
  have houtsideIn : outsideVertex ∈ outComponent := by
    simp [outComponent, houtside]
  have houtCard : 0 < outComponent.card := Finset.card_pos.mpr ⟨outsideVertex, houtsideIn⟩
  have hfne : f ≠ 0 := by
    intro hf
    have hrootValue := congrFun hf root
    have hrefl : Relation.ReflTransGen G.Adj root root :=
      Relation.ReflTransGen.refl
    simp only [f, hrefl, if_pos, Pi.zero_apply] at hrootValue
    have : (0 : ℝ) < outComponent.card := by exact_mod_cast houtCard
    linarith
  have hmean : G.weightedMean f = 0 := by
    unfold WeightedGraph.weightedMean
    change ∀ u, G.degree u = 1 at hregular
    simp_rw [hregular]
    simp only [one_mul]
    rw [show (∑ u : V, f u) =
        (∑ u ∈ (Finset.univ : Finset V),
          if Relation.ReflTransGen G.Adj root u then
            (outComponent.card : ℝ)
          else -((inComponent.card : ℝ))) by
      simp [f]]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hinFilter :
        (Finset.univ.filter fun u : V ↦
          Relation.ReflTransGen G.Adj root u) = inComponent := rfl
    have houtFilter :
        (Finset.univ.filter fun u : V ↦
          ¬ Relation.ReflTransGen G.Adj root u) = outComponent := rfl
    rw [hinFilter, houtFilter]
    ring
  have hfixed : G.walk f = f := by
    apply walk_eq_self_of_constant_on_adjacent G hregular f
    intro u v huv
    have hiff := reachable_adjacent_iff G root u v huv
    simp only [f]
    rw [hiff]
  refine ⟨f, hfne, hmean, ?_⟩
  simpa using hfixed

end WeightedGraph

namespace RelationMatrix

universe u v

variable {R : Type u} {C : Type v} [Fintype R] [DecidableEq R]
  [Fintype C] [DecidableEq C]

omit [DecidableEq R] in
/-- Double counting at a fixed column: each incident weight-three row has
exactly two further columns. -/
theorem sum_countingGram_off_diagonal (H : BinaryMatrix R C)
    (hrow : RowsHaveWeightThree H) (c : C) :
    ∑ d ∈ (Finset.univ.erase c : Finset C), countingGram H c d =
      2 * columnWeight H c := by
  classical
  simp only [countingGram, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hcolumn : 2 * columnWeight H c =
      ∑ r : R, if H r c ≠ 0 then 2 else 0 := by
    unfold columnWeight
    rw [Finset.card_eq_sum_ones, Finset.mul_sum, ← Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _hr
    by_cases h : H r c ≠ 0 <;> simp
  rw [hcolumn]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hrc : H r c ≠ 0
  · rw [if_pos hrc]
    have hcond : ∀ d : C,
        (H r c ≠ 0 ∧ H r d ≠ 0) ↔ H r d ≠ 0 :=
      fun d ↦ and_iff_right hrc
    simp_rw [hcond]
    have hcSupport : c ∈ rowSupport H r := by
      simp [rowSupport, hrc]
    rw [← Finset.sum_filter]
    simp only [← Finset.card_eq_sum_ones]
    change ((Finset.univ.erase c).filter fun d ↦ H r d ≠ 0).card = 2
    have heq :
        (Finset.univ.erase c).filter (fun d ↦ H r d ≠ 0) =
          (rowSupport H r).erase c := by
      ext d
      simp [rowSupport, and_comm]
    rw [heq, Finset.card_erase_of_mem hcSupport, hrow r]
  · simp [hrc]

omit [DecidableEq R] in
/-- The off-diagonal counting-Gram graph of a weight-three incidence matrix
has degree twice the corresponding column weight. -/
theorem gramGraph_degree (H : BinaryMatrix R C)
    (hrow : RowsHaveWeightThree H) (c : C) :
    (gramGraph H).degree c = 2 * (columnWeight H c : ℝ) := by
  classical
  rw [WeightedGraph.degree]
  simp only [gramGraph]
  have hsum :
      (∑ d : C, if c = d then 0 else (countingGram H c d : ℝ)) =
        ∑ d ∈ (Finset.univ.erase c : Finset C),
          (countingGram H c d : ℝ) := by
    rw [Finset.sum_ite]
    simp [Finset.filter_ne]
  rw [hsum, ← Nat.cast_sum, sum_countingGram_off_diagonal H hrow c]
  norm_num

end RelationMatrix

namespace WeightedGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Scaling a finite weighted graph scales all weighted degrees by the same
factor. -/
theorem degree_scale (G : WeightedGraph V) (a : ℝ) (ha : 0 ≤ a) (v : V) :
    (G.scale a ha).degree v = a * G.degree v := by
  simp only [degree, scale, ← Finset.mul_sum]

/-! ## The finite-dimensional spectral implication -/

open WithLp

/-- The symmetric real matrix of edge weights. -/
def weightMatrix (G : WeightedGraph V) : Matrix V V ℝ :=
  G.weight

/-- Sum of the coordinates of a Euclidean vector. -/
def coordinateSum : EuclideanSpace ℝ V →ₗ[ℝ] ℝ where
  toFun x := ∑ v : V, x v
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum]

/-- The ordinary mean-zero subspace.  On a unit-regular graph this is the
stationary mean-zero subspace as well. -/
def meanZeroSubspace : Submodule ℝ (EuclideanSpace ℝ V) :=
  LinearMap.ker (coordinateSum (V := V))

theorem weightMatrix_isHermitian (G : WeightedGraph V) :
    (weightMatrix G).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro u v
  simp [weightMatrix, G.weight_symm]

/-- Symmetry exchanges the two finite sums in the total coordinate sum of a
matrix-vector product. -/
theorem sum_weightMatrix_mulVec (G : WeightedGraph V)
    (x : EuclideanSpace ℝ V) :
    (∑ u : V, Matrix.mulVec (weightMatrix G) x u) =
      ∑ v : V, G.degree v * x v := by
  simp only [Matrix.mulVec, dotProduct, weightMatrix, degree]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _hv
  rw [← Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro u _hu
  rw [G.weight_symm]

theorem weightMatrix_preserves_meanZero (G : WeightedGraph V)
    (hregular : G.IsUnitRegular) (x : meanZeroSubspace (V := V)) :
    Matrix.toEuclideanLin (weightMatrix G) x.1 ∈
      meanZeroSubspace (V := V) := by
  change coordinateSum (Matrix.toEuclideanLin (weightMatrix G) x.1) = 0
  change (∑ u : V, Matrix.mulVec (weightMatrix G) x.1 u) = 0
  rw [sum_weightMatrix_mulVec]
  change ∀ v, G.degree v = 1 at hregular
  simp_rw [hregular]
  simp only [one_mul]
  exact x.2

/-- Restriction of the walk matrix to the mean-zero subspace. -/
noncomputable def restrictedWalk (G : WeightedGraph V)
    (hregular : G.IsUnitRegular) :
    meanZeroSubspace (V := V) →ₗ[ℝ] meanZeroSubspace (V := V) :=
  LinearMap.codRestrict (meanZeroSubspace (V := V))
    ((Matrix.toEuclideanLin (weightMatrix G)).domRestrict
      (meanZeroSubspace (V := V)))
    (weightMatrix_preserves_meanZero G hregular)

theorem restrictedWalk_isSymmetric (G : WeightedGraph V)
    (hregular : G.IsUnitRegular) :
    (restrictedWalk G hregular).IsSymmetric := by
  intro x y
  change inner ℝ ((Matrix.toEuclideanLin (weightMatrix G)) x.1) y.1 =
    inner ℝ x.1 ((Matrix.toEuclideanLin (weightMatrix G)) y.1)
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (weightMatrix_isHermitian G)) x.1 y.1

/-- An eigenvector of the restricted operator is a mean-zero eigenfunction of
the graph walk. -/
theorem restricted_eigenvalue_isMeanZero (G : WeightedGraph V)
    (hregular : G.IsUnitRegular)
    (mu : ℝ) (x : meanZeroSubspace (V := V)) (hxne : x ≠ 0)
    (heigen : restrictedWalk G hregular x = mu • x) :
    AffineRelationSpectrum.IsMeanZeroEigenvalue G mu := by
  let f : V → ℝ := fun v ↦ x.1 v
  have hfne : f ≠ 0 := by
    intro hf
    apply hxne
    apply Subtype.ext
    exact (WithLp.ext_iff 2).2 hf
  have hmean : G.weightedMean f = 0 := by
    unfold weightedMean
    change ∀ u, G.degree u = 1 at hregular
    simp_rw [hregular]
    simp only [one_mul]
    exact x.2
  have hwalk : G.walk f = fun v ↦ mu * f v := by
    funext v
    have hev := congrArg
      (fun z : meanZeroSubspace (V := V) ↦ z.1 v) heigen
    change Matrix.mulVec (weightMatrix G) x.1 v = mu * x.1 v at hev
    change Matrix.mulVec (weightMatrix G) x.1 v / G.degree v = mu * x.1 v
    rw [hregular v, div_one]
    exact hev
  exact ⟨f, hfne, hmean, hwalk⟩

/-- On a finite unit-regular graph, a uniform absolute bound on the
mean-zero eigenvalues implies the weighted `L²` contraction inequality.
The proof applies the spectral theorem to the invariant mean-zero subspace. -/
theorem twoSidedSpectralBound_of_meanZero_eigenvalues
    (G : WeightedGraph V) (hregular : G.IsUnitRegular)
    (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (heigenBound : ∀ mu : ℝ,
      AffineRelationSpectrum.IsMeanZeroEigenvalue G mu → |mu| ≤ lambda) :
    G.TwoSidedSpectralBound lambda := by
  refine ⟨hlambda, ?_⟩
  intro f hmean
  have hsum : ∑ v : V, f v = 0 := by
    unfold weightedMean at hmean
    change ∀ u, G.degree u = 1 at hregular
    simpa only [hregular, one_mul] using hmean
  let xLp : EuclideanSpace ℝ V := WithLp.toLp 2 f
  let x : meanZeroSubspace (V := V) := ⟨xLp, hsum⟩
  let T := restrictedWalk G hregular
  have hT : T.IsSymmetric := restrictedWalk_isSymmetric G hregular
  let n := Module.finrank ℝ (meanZeroSubspace (V := V))
  have hn : Module.finrank ℝ (meanZeroSubspace (V := V)) = n := rfl
  let b := hT.eigenvectorBasis hn
  have heigenvalueBound :
      ∀ i : Fin n, |hT.eigenvalues hn i| ≤ lambda := by
    intro i
    apply heigenBound
    apply restricted_eigenvalue_isMeanZero G hregular
      (hT.eigenvalues hn i) (b i)
    · exact b.orthonormal.ne_zero i
    · exact hT.apply_eigenvectorBasis hn i
  have hnorm : ‖T x‖ ^ 2 ≤ lambda ^ 2 * ‖x‖ ^ 2 := by
    rw [← b.repr.norm_map (T x), ← b.repr.norm_map x]
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ i : Fin n, (b.repr (T x) i) ^ 2) =
          ∑ i : Fin n,
            (hT.eigenvalues hn i * b.repr x i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        have hcoordinate :=
          hT.eigenvectorBasis_apply_self_apply hn x i
        change b.repr (T x) i =
          hT.eigenvalues hn i * b.repr x i at hcoordinate
        exact congrArg (fun z : ℝ ↦ z ^ 2) hcoordinate
      _ ≤ ∑ i : Fin n, lambda ^ 2 * (b.repr x i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        have hsquare : (hT.eigenvalues hn i) ^ 2 ≤ lambda ^ 2 := by
          calc
            (hT.eigenvalues hn i) ^ 2 = |hT.eigenvalues hn i| ^ 2 :=
              (sq_abs _).symm
            _ ≤ lambda ^ 2 :=
              (sq_le_sq₀ (abs_nonneg _) hlambda).2 (heigenvalueBound i)
        simpa [mul_pow] using
          mul_le_mul_of_nonneg_right hsquare (sq_nonneg (b.repr x i))
      _ = lambda ^ 2 * ∑ i : Fin n, (b.repr x i) ^ 2 := by
        rw [Finset.mul_sum]
  have hsquareInput : G.sqNorm f = ‖x‖ ^ 2 := by
    calc
      G.sqNorm f = ∑ v : V, f v ^ 2 := by
        unfold sqNorm
        apply Finset.sum_congr rfl
        intro v _hv
        rw [hregular v, one_mul]
      _ = ‖x.1‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
      _ = ‖x‖ ^ 2 := rfl
  have hwalkPoint (v : V) : (T x).1 v = G.walk f v := by
    change Matrix.mulVec (weightMatrix G) x.1 v = G.walk f v
    unfold walk
    rw [hregular v, div_one]
    rfl
  have hsquareOutput : G.sqNorm (G.walk f) = ‖T x‖ ^ 2 := by
    calc
      G.sqNorm (G.walk f) = ∑ v : V, (G.walk f v) ^ 2 := by
        unfold sqNorm
        apply Finset.sum_congr rfl
        intro v _hv
        rw [hregular v, one_mul]
      _ = ∑ v : V, ((T x).1 v) ^ 2 := by
        apply Finset.sum_congr rfl
        intro v _hv
        rw [hwalkPoint]
      _ = ‖(T x).1‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
      _ = ‖T x‖ ^ 2 := rfl
  rw [hsquareInput, hsquareOutput]
  exact hnorm

end WeightedGraph

namespace AffineRelationSpectrum

universe u v

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
  [CharP F 2] [Algebra F₂ F]
variable {t : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The concrete normalized relation graph is unit-regular.  This uses only
the exact row and column counts from Lemma 3.5. -/
theorem relationGraph_isUnitRegular (D : DirectionSet F t ι)
    (hfield : 2 < Fintype.card F) (hdirections : Nonempty ι) :
    (relationGraph D).IsUnitRegular := by
  intro c
  have hcolumn := AffineRelation.constantColumnWeight D hfield hdirections
  have hrho : 0 < AffineRelation.rho F ι := hcolumn.1
  have hfieldWeak : 2 ≤ Fintype.card F := hfield.le
  have hnormalization :
      normalization (F := F) (ι := ι) =
        2 * (AffineRelation.rho F ι : ℝ) :=
    normalization_eq_two_rho_of_count (AffineRelation.rho F ι)
      hfieldWeak (AffineRelation.rho_mul_two D)
  rw [relationGraph, WeightedGraph.degree_scale]
  rw [RelationMatrix.gramGraph_degree _ (AffineRelation.rowsHaveWeightThree D)]
  rw [hcolumn.2 c, hnormalization]
  have htwoRho : (2 : ℝ) * (AffineRelation.rho F ι : ℝ) ≠ 0 := by
    positivity
  field_simp

/-- The `one_of_disconnected` field of the Fourier interface follows from
the already-proved incidence counts, rather than requiring Fourier analysis. -/
theorem relationGraph_one_of_disconnected (D : DirectionSet F t ι)
    (hfield : 2 < Fintype.card F) (hdirections : Nonempty ι) :
    ¬(relationGraph D).Connected →
      IsMeanZeroEigenvalue (relationGraph D) 1 :=
  WeightedGraph.one_meanZeroEigenvalue_of_not_connected
    (relationGraph D) (relationGraph_isUnitRegular D hfield hdirections)

/-- The entire Fourier interface follows from candidate completeness.  The
other two fields are consequences of finite symmetric spectral theory and the
incidence-count proof that the concrete relation graph is unit-regular. -/
theorem FourierInterface.ofComplete
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (hfield : 2 < Fintype.card F) (hdirections : Nonempty ι)
    (hcomplete : ∀ mu,
      IsMeanZeroEigenvalue (relationGraph D) mu → IsBlockCandidate D mu) :
    FourierInterface input D where
  complete := hcomplete
  one_of_disconnected :=
    relationGraph_one_of_disconnected D hfield hdirections
  l2_bound_of_candidates lambda hlambda hcandidates := by
    apply WeightedGraph.twoSidedSpectralBound_of_meanZero_eigenvalues
      (relationGraph D) (relationGraph_isUnitRegular D hfield hdirections)
      lambda hlambda
    intro mu hmu
    exact hcandidates mu (hcomplete mu hmu)

end AffineRelationSpectrum

end HDXLean
