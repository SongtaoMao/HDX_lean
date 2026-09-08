import HDXLean.CubeProductCayley

/-! The graph-product route to Theorem 1.2, assembled from cited statements
only. All former output-certificate fields are constructed below. -/
namespace HDXLean.GolowichProduct

noncomputable def citedCubeProduct (input : LiteratureInput) (d k : ℕ)
    (hd : 2 ≤ d) (hk : 2 ≤ k) : ProductData (cubeGraph k) (2 * d) (Label d) :=
  (golowich_definition12 input (Cube k) (Label d) (cubeGraph k) (2 * d)
    (cubeGraph_connected k) (cube_card_ge_four k hk) (by omega)
    (by simpa only [show 2 * (2 * d) = 4 * d by omega] using label_capacity d)).some

theorem citedCubeProduct_link (input : LiteratureInput) (d k : ℕ)
    (hd : 2 ≤ d) (hk : 2 ≤ k) (F : Finset (Cube k × Label d))
    (hF : (citedCubeProduct input d k hd hk).complex.IsFace F)
    (hn : 1 ≤ F.card) (hr : F.card + 1 ≤ 2 * d) :
    ((citedCubeProduct input d k hd hk).complex.linkGraph F).Connected ∧
    ((citedCubeProduct input d k hd hk).complex.linkGraph F).UpperRayleighBound
      (1 / ((F.card + 1 : ℕ) : ℝ)) :=
  golowich_theorem18 input (Cube k) (Label d) (cubeGraph k) (2 * d)
    (citedCubeProduct input d k hd hk) (cubeGraph_connected k)
    (cube_card_ge_four k hk) (by omega)
    (by simpa only [show 2 * (2 * d) = 4 * d by omega] using label_capacity d)
    F hF hn hr

/-- The formerly assumed Section 5 output is now built from the cited
product and one-sided link theorem. The degree and two-sided norm fields are
proved internally and are not literature premises. -/
noncomputable def formalizedOutput (input : LiteratureInput) (d k : ℕ)
    (hd : 2 ≤ d) (hk : 2 ≤ k) : Output d k := by
  let Z := citedCubeProduct input d k hd hk
  let C := cubeProductCayley d k hd hk Z
  have hdim : C.complex.dim = 2 * d := Z.dim_eq
  have hle : d ≤ C.complex.dim := by omega
  let Y := C.skeleton d hle (by omega)
  refine
    { complex := Y
      dimension_eq := rfl
      degree_eq := by
        change (C.skeleton d hle (by omega)).cayley.degree = _
        rw [CayleyComplex.skeleton_degree]
        exact cubeProductCayley_degree d k hd hk Z
      positiveLinksConnected := ?_
      codimensionTwoBound := ?_ }
  · intro F hF hcard
    change ((Z.complex.skeleton d hle).linkGraph F).Connected
    have hr : F.card + 1 ≤ d := hcard
    have hFZ : Z.complex.IsFace F := ((Z.complex.skeleton_isFace_iff d hle F).mp hF).1
    apply Z.complex.skeleton_link_connected d hle F hr
    by_cases he : F = ∅
    · subst F
      exact Z.empty_link_connected _ _ (by omega)
        ((show 2 * d + 1 ≤ 4 * d by omega).trans (label_capacity d))
        (cubeGraph_connected k) (cubeGraph_neighbor k (by omega))
    · exact (citedCubeProduct_link input d k hd hk F hFZ
        (by have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he); omega)
        (by omega)).1
  · intro F hF hcard
    change ((Z.complex.skeleton d hle).linkGraph F).TwoSidedSpectralBound (1 / (d : ℝ))
    have hr : F.card + 1 = d := hcard
    have hFZ : Z.complex.IsFace F := ((Z.complex.skeleton_isFace_iff d hle F).mp hF).1
    apply Z.complex.skeleton_link_bound d hle F (by omega)
    apply Z.complex.sectionFive_twoSided_of_upper d hd Z.dim_eq F hr
    have hupper := (citedCubeProduct_link input d k hd hk F hFZ (by omega) (by omega)).2
    simpa only [hr] using hupper

/-- No project-owned assumptions remain in this construction of the interim
interface; it is retained only for reuse of coordinate and asymptotic proofs. -/
noncomputable def sectionFiveInput_of_literature (input : LiteratureInput) : SectionFiveInput where
  output d hd k hk := formalizedOutput input d k hd hk

end HDXLean.GolowichProduct
