import HDXLean.SkeletonCayley

/-! The optimal-order comparison cited in Section 5. The cited bound is
assumed for the two-dimensional complex; reduction of a higher-dimensional
complex to its measured two-skeleton is proved here. -/
namespace HDXLean

/-- [DLW25, Corollary 181], connected-link clause, in the native Cayley
representation. No proof of the cited rank bound is requested or supplied.
Source: https://drops.dagstuhl.de/storage/00lipics/lipics-vol339-ccc2025/LIPIcs.CCC.2025.7/LIPIcs.CCC.2025.7.pdf
-/
structure DegreeLowerBoundLiterature : Type 1 where
  corollary181 : ∀ (n : ℕ) (C : CayleyComplex (V := Fin n → F₂)),
    C.complex.dim = 2 → (C.complex.linkGraph ∅).Connected →
    (C.complex.linkGraph {0}).Connected → 2 * n - 1 ≤ C.cayley.degree

theorem dlw_corollary181 (input : DegreeLowerBoundLiterature) (n : ℕ)
    (C : CayleyComplex (V := Fin n → F₂)) (hd : C.complex.dim = 2)
    (hc : (C.complex.linkGraph ∅).Connected) (hv : (C.complex.linkGraph {0}).Connected) :
    2 * n - 1 ≤ C.cayley.degree := input.corollary181 n C hd hc hv

/-- The cited lower bound applies to the higher-dimensional convention of
the current paper, because the two-skeleton preserves generators and links. -/
theorem degree_lower_of_positiveLinksConnected (input : DegreeLowerBoundLiterature)
    (n : ℕ) (C : CayleyComplex (V := Fin n → F₂)) (hd : 2 ≤ C.complex.dim)
    (hc : C.complex.PositiveLinksConnected) : 2 * n - 1 ≤ C.cayley.degree := by
  have hzero : C.complex.IsFace {0} := by
    have h := (C.cayley.edge_iff 0 0).mpr (Or.inl rfl)
    simpa using h
  have hempty : C.complex.IsFace ∅ := C.complex.isFace_mono hzero (Finset.empty_subset _)
  let Y := C.skeleton 2 hd (by omega)
  have hY : 2 * n - 1 ≤ Y.cayley.degree := by
    apply dlw_corollary181 input n Y rfl
    · exact C.complex.skeleton_link_connected 2 hd ∅ (by simp)
        (hc ∅ hempty (by simp; omega))
    · exact C.complex.skeleton_link_connected 2 hd {0} (by simp)
        (hc {0} hzero (by simpa using hd))
  exact hY

end HDXLean
