import HDXLean.Relabeling
import Mathlib.LinearAlgebra.Pi

/-!
# Products of binary coordinate spaces

The weighted lift initially lives on a product of binary vector spaces.  This
module gives the explicit additive equivalence with one larger coordinate
space, closing the coordinate-space identification used in Theorem 1.2.
-/

namespace HDXLean

/-- Concatenate two binary coordinate vectors. -/
noncomputable def binaryProductEquiv (n r : ℕ) :
    ((Fin n → F₂) × (Fin r → F₂)) ≃+ (Fin (n + r) → F₂) :=
  (((LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin r) F₂ F₂).symm.trans
      (LinearEquiv.piCongrLeft F₂ (fun _ : Fin n ⊕ Fin r ↦ F₂)
        finSumFinEquiv.symm).symm).toAddEquiv)

end HDXLean
