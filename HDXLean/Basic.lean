import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Positivity

/-!
# Basic finite objects for the HDX paper

This file fixes the semantic objects used by the rest of the formalization.
The paper works only with finite graphs and finite simplicial complexes, so we
state the spectral bound directly as the weighted `L²` contraction inequality.
This avoids choosing an ordering of the vertices or a matrix representation.
-/

namespace HDXLean

open scoped BigOperators

/-- The binary field used throughout the paper. -/
abbrev F₂ := ZMod 2

/-! ## Finite weighted graphs -/

/-- A finite undirected loopless graph with nonnegative real edge weights. -/
structure WeightedGraph (V : Type*) [Fintype V] [DecidableEq V] where
  weight : V → V → ℝ
  weight_symm : ∀ u v, weight u v = weight v u
  weight_self : ∀ u, weight u u = 0
  weight_nonneg : ∀ u v, 0 ≤ weight u v

namespace WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The positive-weight edge relation. -/
def Adj (G : WeightedGraph V) (u v : V) : Prop := 0 < G.weight u v

theorem adj_symm (G : WeightedGraph V) {u v : V} : G.Adj u v ↔ G.Adj v u := by
  rw [Adj, Adj, G.weight_symm]

theorem not_adj_self (G : WeightedGraph V) (u : V) : ¬G.Adj u u := by
  simp [Adj, G.weight_self]

/-- Combinatorial connectedness of the positive-weight support. -/
def Connected (G : WeightedGraph V) : Prop :=
  ∀ u v, Relation.ReflTransGen G.Adj u v

/-- Weighted degree. -/
noncomputable def degree (G : WeightedGraph V) (u : V) : ℝ :=
  ∑ v : V, G.weight u v

theorem degree_nonneg (G : WeightedGraph V) (u : V) : 0 ≤ G.degree u := by
  exact Finset.sum_nonneg fun _ _ ↦ G.weight_nonneg _ _

/-- The (total) random-walk operator. Isolated zero-degree vertices are sent to
zero; all graph instances used in the main proof are connected and nontrivial. -/
noncomputable def walk (G : WeightedGraph V) (f : V → ℝ) (u : V) : ℝ :=
  (∑ v : V, G.weight u v * f v) / G.degree u

/-- The unnormalized stationary weighted mean. Its zero set is exactly the
orthogonal complement of the constants for the stationary inner product. -/
noncomputable def weightedMean (G : WeightedGraph V) (f : V → ℝ) : ℝ :=
  ∑ u : V, G.degree u * f u

/-- The squared stationary `L²` seminorm, without the harmless volume factor. -/
noncomputable def sqNorm (G : WeightedGraph V) (f : V → ℝ) : ℝ :=
  ∑ u : V, G.degree u * (f u) ^ 2

theorem sqNorm_nonneg (G : WeightedGraph V) (f : V → ℝ) :
    0 ≤ G.sqNorm f := by
  exact Finset.sum_nonneg fun u _ ↦
    mul_nonneg (G.degree_nonneg u) (sq_nonneg (f u))

/-- The paper's two-sided normalized-adjacency bound, stated as the equivalent
finite-dimensional weighted `L²` inequality on mean-zero functions. -/
def TwoSidedSpectralBound (G : WeightedGraph V) (lambda : ℝ) : Prop :=
  0 ≤ lambda ∧
    ∀ f : V → ℝ, G.weightedMean f = 0 →
      G.sqNorm (G.walk f) ≤ lambda ^ 2 * G.sqNorm f

/-- A stronger spectral estimate also proves every weaker nonnegative estimate. -/
theorem TwoSidedSpectralBound.mono {G : WeightedGraph V} {lambda mu : ℝ}
    (h : G.TwoSidedSpectralBound lambda) (hle : lambda ≤ mu) :
    G.TwoSidedSpectralBound mu := by
  refine ⟨h.1.trans hle, fun f hf ↦ ?_⟩
  have hsquare : lambda ^ 2 ≤ mu ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self h.1 hle
  calc
    G.sqNorm (G.walk f) ≤ lambda ^ 2 * G.sqNorm f := h.2 f hf
    _ ≤ mu ^ 2 * G.sqNorm f :=
      mul_le_mul_of_nonneg_right hsquare (G.sqNorm_nonneg f)

/-- A two-sided spectral expander is connected and satisfies the norm bound. -/
def IsTwoSidedSpectralExpander (G : WeightedGraph V) (lambda : ℝ) : Prop :=
  G.Connected ∧ G.TwoSidedSpectralBound lambda

/-- Scaling every edge by a positive constant does not change the walk. -/
noncomputable def scale (c : ℝ) (hc : 0 ≤ c) (G : WeightedGraph V) : WeightedGraph V where
  weight u v := c * G.weight u v
  weight_symm u v := by rw [G.weight_symm]
  weight_self u := by simp [G.weight_self]
  weight_nonneg u v := mul_nonneg hc (G.weight_nonneg u v)

end WeightedGraph

/-! ## Finite measured pure simplicial complexes -/

/-- A finite pure measured simplicial complex, presented by its top faces.
Faces are ordinary `Finset`s, so multiplicities are impossible. -/
structure MeasuredComplex (V : Type*) [Fintype V] [DecidableEq V] where
  dim : ℕ
  topFaces : Finset (Finset V)
  top_card : ∀ T ∈ topFaces, T.card = dim + 1
  topWeight : Finset V → ℝ
  topWeight_pos : ∀ T ∈ topFaces, 0 < topWeight T
  topWeight_zero : ∀ T ∉ topFaces, topWeight T = 0
  topWeight_sum : ∑ T ∈ topFaces, topWeight T = 1

namespace MeasuredComplex

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Membership in the downward closure of the top faces. The empty face is
included whenever the complex has a top face. -/
def IsFace (X : MeasuredComplex V) (F : Finset V) : Prop :=
  ∃ T ∈ X.topFaces, F ⊆ T

theorem top_isFace (X : MeasuredComplex V) {T : Finset V}
    (hT : T ∈ X.topFaces) : X.IsFace T :=
  ⟨T, hT, Finset.Subset.rfl⟩

theorem isFace_mono (X : MeasuredComplex V) {F F' : Finset V}
    (hF : X.IsFace F) (hsub : F' ⊆ F) : X.IsFace F' := by
  obtain ⟨T, hT, hFT⟩ := hF
  exact ⟨T, hT, hsub.trans hFT⟩

/-- A vertex of the link of `F`. -/
def LinkVertex (X : MeasuredComplex V) (F : Finset V) :=
  {v : V // v ∉ F ∧ X.IsFace (insert v F)}

noncomputable instance (X : MeasuredComplex V) (F : Finset V) :
    Fintype (X.LinkVertex F) := by
  classical
  letI : Finite (X.LinkVertex F) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance (X : MeasuredComplex V) (F : Finset V) :
    DecidableEq (X.LinkVertex F) :=
  Classical.decEq _

/-- Unnormalized conditioned edge weight in the link of `F`. The omitted
conditioning and binomial factors are common positive scalars and hence cancel
from the random-walk operator. -/
noncomputable def linkEdgeWeight (X : MeasuredComplex V) (F : Finset V)
    (u v : X.LinkVertex F) : ℝ :=
  if u = v then 0
  else
    ∑ T ∈ X.topFaces with insert v.1 (insert u.1 F) ⊆ T, X.topWeight T

theorem linkEdgeWeight_symm (X : MeasuredComplex V) (F : Finset V)
    (u v : X.LinkVertex F) :
    X.linkEdgeWeight F u v = X.linkEdgeWeight F v u := by
  classical
  by_cases h : u = v
  · subst v
    simp [linkEdgeWeight]
  · have hvu : v ≠ u := Ne.symm h
    simp only [linkEdgeWeight, h, hvu, ↓reduceIte]
    rw [Finset.insert_comm v.1 u.1]

theorem linkEdgeWeight_nonneg (X : MeasuredComplex V) (F : Finset V)
    (u v : X.LinkVertex F) : 0 ≤ X.linkEdgeWeight F u v := by
  classical
  by_cases h : u = v
  · simp [linkEdgeWeight, h]
  · simp only [linkEdgeWeight, h, ↓reduceIte]
    refine Finset.sum_nonneg fun T hT ↦ le_of_lt (X.topWeight_pos T ?_)
    exact (Finset.mem_filter.mp hT).1

/-- The weighted one-skeleton of a link. -/
noncomputable def linkGraph (X : MeasuredComplex V) (F : Finset V) :
    WeightedGraph (X.LinkVertex F) where
  weight := X.linkEdgeWeight F
  weight_symm := X.linkEdgeWeight_symm F
  weight_self u := by simp [linkEdgeWeight]
  weight_nonneg := X.linkEdgeWeight_nonneg F

/-- Every link whose one-skeleton should be positive-dimensional is connected.
For a `d`-complex this includes the empty-face link (the one-skeleton) and all
faces of cardinality at most `d - 1`. -/
def PositiveLinksConnected (X : MeasuredComplex V) : Prop :=
  ∀ F : Finset V, X.IsFace F → F.card + 1 ≤ X.dim →
    (X.linkGraph F).Connected

/-- The two-sided spectral condition on every codimension-two link. -/
def CodimensionTwoBound (X : MeasuredComplex V) (lambda : ℝ) : Prop :=
  ∀ F : Finset V, X.IsFace F → F.card + 1 = X.dim →
    (X.linkGraph F).TwoSidedSpectralBound lambda

/-- Local spectral expansion in the convention of the paper. -/
def IsTwoSidedLocalSpectralExpander (X : MeasuredComplex V) (lambda : ℝ) : Prop :=
  X.PositiveLinksConnected ∧ X.CodimensionTwoBound lambda

/-- Monotonicity in the local spectral parameter. -/
theorem IsTwoSidedLocalSpectralExpander.mono {X : MeasuredComplex V}
    {lambda mu : ℝ} (h : X.IsTwoSidedLocalSpectralExpander lambda)
    (hle : lambda ≤ mu) : X.IsTwoSidedLocalSpectralExpander mu := by
  refine ⟨h.1, fun F hF hcard ↦ ?_⟩
  exact (h.2 F hF hcard).mono hle

/-- The top-face measure is uniform. -/
def IsUnweighted (X : MeasuredComplex V) : Prop :=
  ∀ T ∈ X.topFaces, X.topWeight T = (X.topFaces.card : ℝ)⁻¹

/-- Number of top faces containing an unordered edge. -/
def edgeCodegree (X : MeasuredComplex V) (x y : V) : ℕ :=
  (X.topFaces.filter fun T ↦ x ∈ T ∧ y ∈ T).card

end MeasuredComplex

/-! ## Translation invariance and Cayley presentations -/

section Cayley

variable {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]

/-- Translate every vertex of a face by the same group element. -/
def translateFace (g : V) (F : Finset V) : Finset V :=
  F.image fun x ↦ g + x

omit [Fintype V] in
theorem mem_translateFace_iff (g x : V) (F : Finset V) :
    x ∈ translateFace g F ↔ x - g ∈ F := by
  classical
  constructor
  · intro hx
    simp only [translateFace, Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [add_sub_cancel_left]
  · intro hx
    refine Finset.mem_image.mpr ⟨x - g, hx, ?_⟩
    simp [sub_eq_add_neg, add_assoc, add_comm g]

/-- Translation invariance of both the top-face set and its per-face measure. -/
def TranslationInvariant (X : MeasuredComplex V) : Prop :=
  ∀ g T, (translateFace g T ∈ X.topFaces ↔ T ∈ X.topFaces) ∧
    X.topWeight (translateFace g T) = X.topWeight T

/-- A Cayley presentation of the one-skeleton of a measured complex. -/
structure CayleyPresentation (X : MeasuredComplex V) where
  generators : Finset V
  zero_not_mem : 0 ∉ generators
  neg_mem_iff : ∀ s, -s ∈ generators ↔ s ∈ generators
  edge_iff : ∀ x y,
    X.IsFace {x, y} ↔ x = y ∨ y - x ∈ generators

/-- Cayley degree, namely the cardinality of the generator set. -/
def CayleyPresentation.degree {X : MeasuredComplex V}
    (C : CayleyPresentation X) : ℕ :=
  C.generators.card

/-- A measured Cayley complex packages its translation-invariant measure and
its Cayley one-skeleton. -/
structure CayleyComplex where
  complex : MeasuredComplex V
  cayley : CayleyPresentation complex
  translationInvariant : TranslationInvariant complex

end Cayley

/-! ## Finite binary incidence matrices -/

section BinaryMatrix

variable {R C : Type*} [Fintype R] [DecidableEq R]
  [Fintype C] [DecidableEq C]

/-- A binary matrix, used algebraically over `F₂`. -/
abbrev BinaryMatrix (R C : Type*) := Matrix R C F₂

/-- Support of one binary row. -/
def rowSupport (H : BinaryMatrix R C) (r : R) : Finset C :=
  Finset.univ.filter fun c ↦ H r c ≠ 0

/-- Hamming weight of a binary vector. -/
def hammingWeight (x : C → F₂) : ℕ :=
  (Finset.univ.filter fun c ↦ x c ≠ 0).card

/-- Number of rows containing a column. -/
def columnWeight (H : BinaryMatrix R C) (c : C) : ℕ :=
  (Finset.univ.filter fun r ↦ H r c ≠ 0).card

/-- The row code over `F₂`. -/
def rowCode (H : BinaryMatrix R C) : Submodule F₂ (C → F₂) :=
  Submodule.span F₂ (Set.range fun r ↦ H r)

/-- The minimum-distance-at-least-three condition in a convention-independent
form (it also behaves correctly for the zero code). -/
def RowDistanceAtLeastThree (H : BinaryMatrix R C) : Prop :=
  ∀ x ∈ rowCode H, x ≠ 0 → 3 ≤ hammingWeight x

/-- Counting Gram matrix. This is deliberately `ℕ`-valued: the paper's graph
matrix is not the product of `H` with its transpose in `F₂`. -/
def countingGram (H : BinaryMatrix R C) (c c' : C) : ℕ :=
  (Finset.univ.filter fun r ↦ H r c ≠ 0 ∧ H r c' ≠ 0).card

omit [DecidableEq R] [Fintype C] [DecidableEq C] in
theorem countingGram_symm (H : BinaryMatrix R C) (c c' : C) :
    countingGram H c c' = countingGram H c' c := by
  classical
  simp [countingGram, and_comm]

omit [DecidableEq R] [Fintype C] [DecidableEq C] in
theorem countingGram_self (H : BinaryMatrix R C) (c : C) :
    countingGram H c c = columnWeight H c := by
  classical
  simp [countingGram, columnWeight]

/-- The off-diagonal real counting-Gram graph attached to an incidence matrix. -/
noncomputable def gramGraph (H : BinaryMatrix R C) : WeightedGraph C where
  weight c c' := if c = c' then 0 else (countingGram H c c' : ℝ)
  weight_symm c c' := by
    by_cases h : c = c'
    · subst c'
      simp
    · have h' : c' ≠ c := Ne.symm h
      simp [h, h', countingGram_symm]
  weight_self c := by simp
  weight_nonneg c c' := by positivity

end BinaryMatrix

end HDXLean
