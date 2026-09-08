import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card

/-!
# Canonical indices for all maximal minors

The selected columns are now constructed from all `k`-element subsets of
`Fin m`. Their count and pairwise distinctness are proved, not supplied as
unrelated fields of a construction certificate.
-/

namespace HDXLean.CanonicalMaximalMinors

/-- Every `k`-element column subset, with its inherited increasing order. -/
abbrev Index (k m : ℕ) := ↥((Finset.univ : Finset (Fin m)).powersetCard k)

theorem index_card (k m : ℕ) : Fintype.card (Index k m) = Nat.choose m k := by
  simp [Index, Finset.card_powersetCard]

/-- The increasing enumeration of the chosen column subset. -/
noncomputable def column {k m : ℕ} (j : Index k m) : Fin k → Fin m :=
  j.val.orderEmbOfFin (Finset.mem_powersetCard.mp j.property).2

theorem column_injective {k m : ℕ} (j : Index k m) :
    Function.Injective (column j) :=
  (j.val.orderEmbOfFin (Finset.mem_powersetCard.mp j.property).2).injective

theorem range_column {k m : ℕ} (j : Index k m) :
    Set.range (column j) = (j.val : Set (Fin m)) :=
  Finset.range_orderEmbOfFin _ _

theorem column_range_injective (k m : ℕ) :
    Function.Injective (fun j : Index k m ↦ Set.range (column j)) := by
  intro j l h
  apply Subtype.ext
  exact Finset.coe_injective (by simpa only [range_column] using h)

end HDXLean.CanonicalMaximalMinors
