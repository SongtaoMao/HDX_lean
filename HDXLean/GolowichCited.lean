import HDXLean.WeightedRayleigh
import Mathlib.Data.Nat.Choose.Basic

/-! Explicit statements of the literature inputs in Section 5.

Source: Golowich, APPROX/RANDOM 2021, Definition 12 and Theorem 18,
https://drops.dagstuhl.de/storage/00lipics/lipics-vol207-approx-random2021/LIPIcs.APPROX-RANDOM.2021.38/LIPIcs.APPROX-RANDOM.2021.38.pdf

Only the cited product construction and its ONE-SIDED nonempty-link bound
are assumed. No Cayley presentation, degree formula, skeleton, or two-sided
norm bound is contained in this interface. The upper bound is written in
the equivalent stationary Rayleigh-quotient formulation.
-/
namespace HDXLean.GolowichProduct
open scoped BigOperators
variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]

/-- Literal facets in the cited product construction: distinct labels and
projection onto exactly one positive-weight base edge. -/
def IsProductTop (G : WeightedGraph V) (K : ℕ) (σ : Finset (V × A)) : Prop :=
  σ.card = K + 1 ∧ Set.InjOn Prod.snd (σ : Set (V × A)) ∧
    ∃ u v, G.Adj u v ∧ σ.image Prod.fst = {u, v}

/-- Symmetric ordered-endpoint version of the cited top-face mass. For a
facet, its two endpoint orderings contribute equally; the common factor two
vanishes on normalization. -/
noncomputable def productMass (G : WeightedGraph V) (K : ℕ)
    (σ : Finset (V × A)) : ℝ := by
  classical
  exact if IsProductTop G K σ then
    ∑ u, ∑ v, if G.Adj u v ∧ σ.image Prod.fst = {u, v}
      then G.weight u v / (Nat.choose (K - 1) ((σ.filter (fun z ↦ z.1 = u)).card - 1) : ℝ)
      else 0
    else 0

/-- The measured object is identified by its defining facets and weights;
this is not a record of the final claims of Theorem 1.2. -/
structure ProductData (G : WeightedGraph V) (K : ℕ) (A : Type*)
    [Fintype A] [DecidableEq A] where
  complex : MeasuredComplex (V × A)
  dim_eq : complex.dim = K
  top_iff : ∀ σ, σ ∈ complex.topFaces ↔ IsProductTop G K σ
  weight_eq : ∀ σ, complex.topWeight σ =
    productMass G K σ / ∑ τ : Finset (V × A), productMass G K τ

/-- User-authorized cited statements. The hypotheses of Theorem 18 are
retained explicitly. This record contains no paper-owned spectral step. -/
structure LiteratureInput : Type 1 where
  definition12 : ∀ (V A : Type) [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (G : WeightedGraph V) (K : ℕ), G.Connected → 4 ≤ Fintype.card V →
    2 ≤ K → 2 * K ≤ Fintype.card A → Nonempty (ProductData G K A)
  theorem18 : ∀ (V A : Type) [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (G : WeightedGraph V) (K : ℕ) (Z : ProductData G K A),
    G.Connected → 4 ≤ Fintype.card V → 2 ≤ K → 2 * K ≤ Fintype.card A →
    ∀ F : Finset (V × A), Z.complex.IsFace F → 1 ≤ F.card → F.card + 1 ≤ K →
      (Z.complex.linkGraph F).Connected ∧
      (Z.complex.linkGraph F).UpperRayleighBound (1 / ((F.card + 1 : ℕ) : ℝ))

/-- Formalized cited Lemma: [Gol21, Definition 12]. -/
theorem golowich_definition12 (input : LiteratureInput)
    (V A : Type) [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (G : WeightedGraph V) (K : ℕ) (hc : G.Connected) (hV : 4 ≤ Fintype.card V)
    (hK : 2 ≤ K) (hA : 2 * K ≤ Fintype.card A) : Nonempty (ProductData G K A) :=
  input.definition12 V A G K hc hV hK hA

/-- Formalized cited Lemma: [Gol21, Theorem 18], nonempty links only. -/
theorem golowich_theorem18 (input : LiteratureInput)
    (V A : Type) [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (G : WeightedGraph V) (K : ℕ) (Z : ProductData G K A)
    (hc : G.Connected) (hV : 4 ≤ Fintype.card V) (hK : 2 ≤ K)
    (hA : 2 * K ≤ Fintype.card A) (F : Finset (V × A))
    (hF : Z.complex.IsFace F) (hn : 1 ≤ F.card) (hr : F.card + 1 ≤ K) :
    (Z.complex.linkGraph F).Connected ∧
    (Z.complex.linkGraph F).UpperRayleighBound (1 / ((F.card + 1 : ℕ) : ℝ)) :=
  input.theorem18 V A G K Z hc hV hK hA F hF hn hr

end HDXLean.GolowichProduct
