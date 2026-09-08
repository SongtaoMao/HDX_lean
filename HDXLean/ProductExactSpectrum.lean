import HDXLean.SectionFiveFormalized
import HDXLean.ProductGlobalGap
import HDXLean.CubeSpectralGap

/-!
# Exact global and local spectral statements for the actual product family

Source: Golowich, APPROX/RANDOM 2021, Theorem 18 and Lemmas 20--21,
https://drops.dagstuhl.de/storage/00lipics/lipics-vol207-approx-random2021/LIPIcs.APPROX-RANDOM.2021.38/LIPIcs.APPROX-RANDOM.2021.38.pdf

The cited statements refer to the literal `ProductData` facets and weights.
The base-cube spectrum, face classification, and skeleton transport are
proved internally. These additional cited equalities are kept separate from
the upper-bound-only inputs sufficient for the main existence theorem.
-/
namespace HDXLean.GolowichProduct
open scoped BigOperators
open AffineRelationSpectrum

/-- The minimum-degree condition needed by the leaf-eigenspace argument in
the cited single-fiber computation. It is automatic for cubes of rank >= 2. -/
def TwoNeighbors {V : Type*} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) : Prop :=
  ∀ u, ∃ v w, G.Adj u v ∧ G.Adj u w ∧ v ≠ w

/-- Exact external spectral statements, not output certificates for the
paper's skeleton or cube family. The degree-two safeguard avoids using the
single-fiber eigenvalue argument when its leaf-difference space is zero. -/
structure ExactSpectrumInput : Type 1 where
  theorem18_global : ∀ (V A : Type) [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] (G : WeightedGraph V) (K : ℕ)
    (Z : ProductData G K A), G.Connected → 4 ≤ Fintype.card V →
    2 ≤ K → 2 * K ≤ Fintype.card A → ∀ gap : ℝ,
    G.HasSpectralGap gap →
    (Z.complex.linkGraph ∅).HasSpectralGap
      (gap / ∑ j ∈ Finset.range K, (1 : ℝ) / ((j : ℝ) + 1))
  lemma20_mixed : ∀ (V A : Type) [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] (G : WeightedGraph V) (K : ℕ)
    (Z : ProductData G K A), G.Connected → 4 ≤ Fintype.card V →
    2 ≤ K → 2 * K ≤ Fintype.card A →
    ∀ F : Finset (V × A), Z.complex.IsFace F →
    2 ≤ F.card → F.card + 1 ≤ K → (F.image Prod.fst).card = 2 →
    IsMeanZeroEigenvalue (Z.complex.linkGraph F) (1 / ((F.card + 1 : ℕ) : ℝ))
  lemma21_single : ∀ (V A : Type) [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] (G : WeightedGraph V) (K : ℕ)
    (Z : ProductData G K A), G.Connected → 4 ≤ Fintype.card V →
    2 ≤ K → 2 * K ≤ Fintype.card A → TwoNeighbors G →
    ∀ F : Finset (V × A), Z.complex.IsFace F →
    1 ≤ F.card → F.card + 1 ≤ K → (F.image Prod.fst).card = 1 →
    IsMeanZeroEigenvalue (Z.complex.linkGraph F) (1 / ((F.card + 1 : ℕ) : ℝ))

theorem cubeGraph_twoNeighbors (k : ℕ) (hk : 2 ≤ k) : TwoNeighbors (cubeGraph k) := by
  intro x
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  refine ⟨x + cubeBasis k i, x + cubeBasis k j,
    (cubeGraph_adj k _ _).mpr ⟨i, rfl⟩,
    (cubeGraph_adj k _ _).mpr ⟨j, rfl⟩, ?_⟩
  intro h
  have hij := cubeBasis_injective k (add_left_cancel h)
  have := congrArg Fin.val hij
  norm_num [i, j] at this

theorem product_face_projection_card {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] (G : WeightedGraph V) (K : ℕ)
    (Z : ProductData G K A) (F : Finset (V × A))
    (hF : Z.complex.IsFace F) (hn : 1 ≤ F.card) :
    (F.image Prod.fst).card = 1 ∨ (F.image Prod.fst).card = 2 := by
  classical
  obtain ⟨T, hT, hFT⟩ := hF
  obtain ⟨_, _, u, v, _, he⟩ := (Z.top_iff T).mp hT
  have hsub : F.image Prod.fst ⊆ ({u, v} : Finset V) := by
    rw [← he]
    exact Finset.image_subset_image hFT
  have hle := Finset.card_le_card hsub
  have hpair : ({u, v} : Finset V).card ≤ 2 := by
    by_cases huv : u = v <;> simp [huv]
  have hpos := Finset.card_pos.mpr ((Finset.card_pos.mp hn).image Prod.fst)
  omega

/-- Every codimension-two link of the actual constructed skeleton has the
claimed eigenvalue `1/d`. The existence theorem's upper bound alone would
not imply this sharpness statement. -/
theorem formalizedOutput_link_eigenvalue (input : LiteratureInput)
    (spectra : ExactSpectrumInput) (d k : ℕ) (hd : 2 ≤ d) (hk : 2 ≤ k)
    (F : Finset (Cube k × Label d))
    (hF : (formalizedOutput input d k hd hk).complex.complex.IsFace F)
    (hcard : F.card + 1 = d) :
    IsMeanZeroEigenvalue
      ((formalizedOutput input d k hd hk).complex.complex.linkGraph F)
      (1 / (d : ℝ)) := by
  let Z := citedCubeProduct input d k hd hk
  have hle : d ≤ Z.complex.dim := by rw [Z.dim_eq]; omega
  have hFZ : Z.complex.IsFace F :=
    ((Z.complex.skeleton_isFace_iff d hle F).mp hF).1
  change IsMeanZeroEigenvalue ((Z.complex.skeleton d hle).linkGraph F) _
  apply Z.complex.skeleton_link_eigenvalue d hle F (by omega)
  have hc := cubeGraph_connected k
  have hv := cube_card_ge_four k hk
  have ha : 2 * (2 * d) ≤ Fintype.card (Label d) := by
    simpa only [show 2 * (2 * d) = 4 * d by omega] using label_capacity d
  have hn : 1 ≤ F.card := by omega
  rcases product_face_projection_card (cubeGraph k) (2 * d) Z F hFZ hn with h | h
  · simpa only [hcard] using spectra.lemma21_single (Cube k) (Label d)
      (cubeGraph k) (2 * d) Z hc hv (by omega) ha (cubeGraph_twoNeighbors k hk)
      F hFZ hn (by omega) h
  · have htwo : 2 ≤ F.card := by
      have := Finset.card_image_le (f := Prod.fst) (s := F)
      omega
    simpa only [hcard] using spectra.lemma20_mixed (Cube k) (Label d)
      (cubeGraph k) (2 * d) Z hc hv (by omega) ha F hFZ htwo (by omega) h

/-- Identification of the numerical formula with the exact one-sided gap of
the global graph of the actual constructed skeleton. -/
theorem formalizedOutput_globalGap (input : LiteratureInput)
    (spectra : ExactSpectrumInput) (d k : ℕ) (hd : 2 ≤ d) (hk : 2 ≤ k) :
    ((formalizedOutput input d k hd hk).complex.complex.linkGraph ∅).HasSpectralGap
      (productGlobalGap d k) := by
  let Z := citedCubeProduct input d k hd hk
  have hle : d ≤ Z.complex.dim := by rw [Z.dim_eq]; omega
  change ((Z.complex.skeleton d hle).linkGraph ∅).HasSpectralGap _
  apply Z.complex.skeleton_link_spectralGap d hle ∅ (by simp; omega)
  have h := spectra.theorem18_global (Cube k) (Label d) (cubeGraph k) (2 * d) Z
    (cubeGraph_connected k) (cube_card_ge_four k hk) (by omega)
    (by simpa only [show 2 * (2 * d) = 4 * d by omega] using label_capacity d)
    (2 / (k : ℝ)) (cubeGraph_spectralGap k (by omega))
  simpa only [productGlobalGap, harmonicFactor, div_div] using h

/-- The exact gaps of these graphs are positive and approach zero; the
statement now quantifies over the actual graph, not just an arithmetic proxy. -/
theorem formalizedOutput_globalGap_tendsToZero (input : LiteratureInput)
    (spectra : ExactSpectrumInput) (d : ℕ) (hd : 2 ≤ d) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∀ hk : 2 ≤ k,
      ((formalizedOutput input d k hd hk).complex.complex.linkGraph ∅).HasSpectralGap
        (productGlobalGap d k) ∧
      0 < productGlobalGap d k ∧ productGlobalGap d k < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := productGlobalGap_tendsToZero d hd ε hε
  exact ⟨N, fun k hk hk2 ↦
    ⟨formalizedOutput_globalGap input spectra d k hd hk2, hN k hk⟩⟩

/-- Coordinate concatenation does not change the exact global gap. Thus the
same formula holds on the literal binary coordinate space in the final family. -/
theorem coordinateAt_globalGap (input : LiteratureInput) (spectra : ExactSpectrumInput)
    (d : ℕ) (hd : 2 ≤ d) (r : ℕ) :
    ((coordinateAt (sectionFiveInput_of_literature input) d hd r).complex.linkGraph ∅).HasSpectralGap
      (productGlobalGap d (r + 2)) := by
  let X := (formalizedOutput input d (r + 2) hd (by omega)).complex.complex
  change ((X.relabel (coordinateEquiv d r).toEquiv).linkGraph ∅).HasSpectralGap _
  have h := X.link_spectralGap_relabel (coordinateEquiv d r).toEquiv ∅
    (formalizedOutput_globalGap input spectra d (r + 2) hd (by omega))
  have he : (coordinateEquiv d r).toEquiv.finsetCongr ∅ = ∅ := by simp
  rw [he] at h
  exact h

/-- The exact nontrivial link eigenvalue also survives the final coordinate
identification; this is the Section 6 sharpness statement for the actual family. -/
theorem coordinateAt_link_eigenvalue (input : LiteratureInput) (spectra : ExactSpectrumInput)
    (d : ℕ) (hd : 2 ≤ d) (r : ℕ)
    (F : Finset (Fin (ambientDimension d r) → F₂))
    (hF : (coordinateAt (sectionFiveInput_of_literature input) d hd r).complex.IsFace F)
    (hcard : F.card + 1 = d) :
    IsMeanZeroEigenvalue
      ((coordinateAt (sectionFiveInput_of_literature input) d hd r).complex.linkGraph F)
      (1 / (d : ℝ)) := by
  let X := (formalizedOutput input d (r + 2) hd (by omega)).complex.complex
  let e := (coordinateEquiv d r).toEquiv
  obtain ⟨F0, rfl⟩ := e.finsetCongr.surjective F
  have hF0 : X.IsFace F0 := by
    have h := (X.isFace_relabel_iff e (e.finsetCongr F0)).mp hF
    change X.IsFace (e.finsetCongr.symm (e.finsetCongr F0)) at h
    simpa only [Equiv.symm_apply_apply] using h
  have hcard0 : F0.card + 1 = d := by simpa using hcard
  change IsMeanZeroEigenvalue ((X.relabel e).linkGraph (e.finsetCongr F0)) _
  exact X.link_eigenvalue_relabel e F0
    (formalizedOutput_link_eigenvalue input spectra d (r + 2) hd (by omega) F0 hF0 hcard0)

end HDXLean.GolowichProduct
