import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Lean.Elab.Tactic.Omega

/-!
# Selecting the Section 4 row and column function families

For `k = floor(g/4)`, the manuscript uses divisors of degrees `g+k` and
`2g-k`. The arithmetic consequences of the general Riemann--Roch lower
bound, and the selection of independent function families of sizes `k` and
`3k`, are proved here. The spaces and their RR lower bounds must still be
instantiated for the actual curve; no final independence conclusion is
supplied as an assumption.
-/
namespace HDXLean.SectionFourSubspaces

/-- The degree of `A = (g+k) P_infinity`, for `k = floor(g/4)`. -/
def degreeA (g : ℕ) : ℕ := g + g / 4

/-- The degree of `B = (2g-k) P_infinity`. -/
def degreeB (g : ℕ) : ℕ := 2 * g - g / 4

/-- The natural-number form of the RR lower bound is equivalent to the
additive form `degree+1 <= dimension+genus`, including small degrees. -/
theorem riemannRoch_lower_iff (g degree dimension : ℕ) :
    degree + 1 - g ≤ dimension ↔ degree + 1 ≤ dimension + g := by omega

theorem degreeA_add_degreeB (g : ℕ) : degreeA g + degreeB g = 3 * g := by
  unfold degreeA degreeB
  omega

theorem rowCount_pos (g : ℕ) (hg : 4 ≤ g) : 0 < g / 4 := by omega

/-- Specialize `ell(A) >= deg(A)+1-g`; the spare dimension is retained. -/
theorem row_dimension_lower (g ellA : ℕ)
    (hRR : degreeA g + 1 - g ≤ ellA) : g / 4 + 1 ≤ ellA := by
  unfold degreeA at hRR
  omega

/-- Specialize `ell(B) >= deg(B)+1-g` and use `4 floor(g/4) <= g`.
This proves the stronger `3k+1` bound used in the manuscript. -/
theorem column_dimension_lower (g ellB : ℕ)
    (hRR : degreeB g + 1 - g ≤ ellB) : 3 * (g / 4) + 1 ≤ ellB := by
  unfold degreeB at hRR
  omega

section FunctionSpaces

variable (F U V : Type*) [Field F]
  [AddCommGroup U] [Module F U] [FiniteDimensional F U]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- The actual selected functions, indexed by the paper's matrix dimensions.
Their independence is a proved field of the construction below. -/
structure FunctionFamilies (g : ℕ) where
  row : Fin (g / 4) → U
  column : Fin (3 * (g / 4)) → V
  row_independent : LinearIndependent F row
  column_independent : LinearIndependent F column

/-- Select the manuscript's `k` and `3k` functions from the RR dimension
bounds. This is non-algorithmic basis selection, within the formalized scope. -/
noncomputable def selectFamilies (g : ℕ)
    (hA : degreeA g + 1 - g ≤ Module.finrank F U)
    (hB : degreeB g + 1 - g ≤ Module.finrank F V) : FunctionFamilies F U V g := by
  have hrow : g / 4 ≤ Module.finrank F U :=
    (Nat.le_succ (g / 4)).trans (row_dimension_lower g _ hA)
  have hcolumn : 3 * (g / 4) ≤ Module.finrank F V :=
    (Nat.le_succ (3 * (g / 4))).trans (column_dimension_lower g _ hB)
  let hrowChoice := exists_linearIndependent_of_le_finrank hrow
  let hcolumnChoice := exists_linearIndependent_of_le_finrank hcolumn
  exact ⟨Classical.choose hrowChoice, Classical.choose hcolumnChoice,
    Classical.choose_spec hrowChoice, Classical.choose_spec hcolumnChoice⟩

/-- The selected row and column types have exactly the manuscript sizes. -/
theorem selected_index_cardinalities (g : ℕ) :
    Fintype.card (Fin (g / 4)) = g / 4 ∧
    Fintype.card (Fin (3 * (g / 4))) = 3 * (g / 4) := by simp

end FunctionSpaces

end HDXLean.SectionFourSubspaces
