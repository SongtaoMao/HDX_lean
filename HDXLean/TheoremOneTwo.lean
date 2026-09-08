import HDXLean.SectionFiveFormalized

/-!
# The outer quantifiers of the current Theorem 1.2

The revised Section 5 constructs the higher-dimensional family directly from
Golowich's graph product.  It no longer invokes Theorem 1.1 or the former
weighted clone lift. The actual product Cayley structure, induced measured
skeleton, exact degree, connectivity, two-sided norm, linear asymptotics,
and coordinate transport are internal proofs. Only the cited product
construction and one-sided Golowich theorem are supplied as literature input.
Algorithmic running-time/encoding claims remain outside this interface.
-/

namespace HDXLean

namespace TheoremOneTwo

/-- The current outer form of Theorem 1.2: for every fixed `d ≥ 2`, the
cited Section 5 input produces an infinite family of `d`-dimensional
abelian Cayley complexes with codimension-two local spectral norm at most
`1 / d` and Cayley degree `Theta_d(n)` in the ambient binary dimension. -/
theorem theoremOneTwo (d : ℕ) (hd : 2 ≤ d)
    (literature : GolowichProduct.LiteratureInput) :
    Nonempty (LinearDegreeHigherDimensionalFamily d) := by
  exact ⟨GolowichProduct.family (GolowichProduct.sectionFiveInput_of_literature literature) d hd⟩

end TheoremOneTwo

end HDXLean
