import HDXLean.BinaryCoordinates
import HDXLean.Families

/-!
# The graph-product family used in the current Section 5

The current proof of Theorem 1.2 no longer uses the weighted clone lift.  It
applies Golowich's graph-product construction to a binary cube, takes the
`d`-skeleton, and transports the product group to one binary coordinate
space.

`SectionFiveInput` is the intermediate output interface used by the parameter,
coordinate-transport and linear-asymptotic proofs below. It is no longer a
user-supplied premise of the main theorem: `SectionFiveFormalized` constructs
every field from the named literature statements in `GolowichCited`, using
the actual product facets/weights, Cayley generators, measured skeleton, and
internally proved lower-Rayleigh and two-sided-operator arguments.
-/

namespace HDXLean

namespace GolowichProduct

/-- The fixed binary label rank used when the target dimension is `d`. -/
def labelRank (d : ℕ) : ℕ := 4 * d

/-- The label group.  Its order is a power of two at least `4d`. -/
abbrev Label (d : ℕ) := Fin (labelRank d) → F₂

theorem card_label (d : ℕ) :
    Fintype.card (Label d) = 2 ^ (4 * d) := by
  change Fintype.card (Fin (4 * d) → F₂) = binaryVertexCount (4 * d)
  exact binaryVertexCount_card (4 * d)

/-- The paper takes `K = 2d` and requires at least `2K = 4d` labels. -/
theorem label_capacity (d : ℕ) :
    4 * d ≤ Fintype.card (Label d) := by
  rw [card_label]
  exact (4 * d).lt_two_pow_self.le

/-- The concrete output needed from the graph-product construction for the
`k`-dimensional binary cube and target skeleton dimension `d`.

The spectral fields use the native operator-norm language of this
development. `SectionFiveFormalized.formalizedOutput` (in this namespace)
constructs these fields from the cited one-sided bound and internal proofs.
-/
structure Output (d k : ℕ) where
  complex : CayleyComplex
    (V := (Fin k → F₂) × Label d)
  dimension_eq : complex.complex.dim = d
  positiveLinksConnected : complex.complex.PositiveLinksConnected
  codimensionTwoBound :
    complex.complex.CodimensionTwoBound (1 / (d : ℝ))
  degree_eq : complex.cayley.degree =
    (Fintype.card (Label d) - 1) * (k + 1)

/-- Intermediate output interface, constructed by `sectionFiveInput_of_literature`.
The restrictions `d ≥ 2` and `k ≥ 2` are precisely those used in the paper:
the latter ensures that the cube has at least four vertices. -/
structure SectionFiveInput : Type 1 where
  output : ∀ (d : ℕ), 2 ≤ d → ∀ (k : ℕ), 2 ≤ k → Output d k

/-- Use the `r`-th cube dimension `k = r + 2`. -/
noncomputable def outputAt (input : SectionFiveInput)
    (d : ℕ) (hd : 2 ≤ d) (r : ℕ) : Output d (r + 2) :=
  input.output d hd (r + 2) (by omega)

/-- Ambient binary coordinate dimension after concatenating cube and label
coordinates. -/
def ambientDimension (d r : ℕ) : ℕ := (r + 2) + labelRank d

/-- The concrete concatenation equivalence, with its target written using
`ambientDimension`. -/
noncomputable def coordinateEquiv (d r : ℕ) :
    ((Fin (r + 2) → F₂) × Label d) ≃+
      (Fin (ambientDimension d r) → F₂) := by
  change ((Fin (r + 2) → F₂) × (Fin (labelRank d) → F₂)) ≃+
    (Fin ((r + 2) + labelRank d) → F₂)
  exact binaryProductEquiv (r + 2) (labelRank d)

/-- The graph-product skeleton before concatenating binary coordinates. -/
noncomputable def rawAt (input : SectionFiveInput)
    (d : ℕ) (hd : 2 ≤ d) (r : ℕ) :
    CayleyComplex (V := (Fin (r + 2) → F₂) × Label d) :=
  (outputAt input d hd r).complex

/-- The same complex on the literal coordinate space `F₂^(k+4d)`. -/
noncomputable def coordinateAt (input : SectionFiveInput)
    (d : ℕ) (hd : 2 ≤ d) (r : ℕ) :
    CayleyComplex (V := Fin (ambientDimension d r) → F₂) :=
  (rawAt input d hd r).relabel
    (coordinateEquiv d r)

@[simp]
theorem coordinateAt_dimension (input : SectionFiveInput)
    (d : ℕ) (hd : 2 ≤ d) (r : ℕ) :
    (coordinateAt input d hd r).complex.dim = d := by
  exact (outputAt input d hd r).dimension_eq

theorem coordinateAt_localExpansion (input : SectionFiveInput)
    (d : ℕ) (hd : 2 ≤ d) (r : ℕ) :
    (coordinateAt input d hd r).complex.IsTwoSidedLocalSpectralExpander
      (1 / (d : ℝ)) := by
  apply MeasuredComplex.localSpectralExpander_relabel
  exact ⟨(outputAt input d hd r).positiveLinksConnected,
    (outputAt input d hd r).codimensionTwoBound⟩

theorem coordinateAt_degree (input : SectionFiveInput)
    (d : ℕ) (hd : 2 ≤ d) (r : ℕ) :
    (coordinateAt input d hd r).cayley.degree =
      (Fintype.card (Label d) - 1) * ((r + 2) + 1) := by
  rw [coordinateAt, CayleyComplex.relabel_degree]
  exact (outputAt input d hd r).degree_eq

theorem ambientDimension_tendsToInfinity (d : ℕ) :
    TendsToInfinity (ambientDimension d) := by
  intro B
  refine ⟨B, fun r hr ↦ ?_⟩
  dsimp [ambientDimension]
  omega

/-- The exact degree formula gives the strengthened `Theta_d(n)` conclusion
of the current theorem, not merely a polynomial upper bound. -/
theorem coordinateAt_degree_theta (input : SectionFiveInput)
    (d : ℕ) (hd : 2 ≤ d) :
    ThetaLinear
      (fun r ↦ (coordinateAt input d hd r).cayley.degree)
      (ambientDimension d) := by
  let c := Fintype.card (Label d) - 1
  let a := labelRank d
  have hcard : 2 ≤ Fintype.card (Label d) := by
    rw [card_label]
    have hrank : 1 ≤ 4 * d := by omega
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (4 * d) := Nat.pow_le_pow_right (by omega) hrank
  have hc : 1 ≤ c := by
    dsimp [c]
    omega
  constructor
  · refine ⟨c, Eventually.of_forall fun r ↦ ?_⟩
    change (coordinateAt input d hd r).cayley.degree ≤
      c * (ambientDimension d r + 1)
    rw [coordinateAt_degree]
    dsimp [c, ambientDimension]
    exact Nat.mul_le_mul_left _ (by omega)
  · refine ⟨a + 1, Eventually.of_forall fun r ↦ ?_⟩
    change ambientDimension d r ≤
      (a + 1) * ((coordinateAt input d hd r).cayley.degree + 1)
    rw [coordinateAt_degree]
    change (r + 2) + a ≤ (a + 1) * (c * ((r + 2) + 1) + 1)
    have hbase : (r + 2) + a ≤ (a + 1) * (r + 3) := by
      calc
        (r + 2) + a ≤ (r + 3) + a * (r + 3) :=
          Nat.add_le_add (by omega) (Nat.le_mul_of_pos_right a (by omega))
        _ = (a + 1) * (r + 3) := by ring
    have hdegree : r + 3 ≤ c * (r + 3) + 1 := by
      calc
        r + 3 = 1 * (r + 3) := by simp
        _ ≤ c * (r + 3) := Nat.mul_le_mul_right (r + 3) hc
        _ ≤ c * (r + 3) + 1 := Nat.le_add_right _ _
    exact hbase.trans (Nat.mul_le_mul_left (a + 1) hdegree)

/-- The coordinate complexes form the exact linear-degree family asserted by
the current Theorem 1.2. -/
noncomputable def family (input : SectionFiveInput)
    (d : ℕ) (hd : 2 ≤ d) : LinearDegreeHigherDimensionalFamily d where
  ambientDimension := ambientDimension d
  complex := coordinateAt input d hd
  dimension_eq := coordinateAt_dimension input d hd
  localExpansion := coordinateAt_localExpansion input d hd
  ambientDimension_tendsToInfinity := ambientDimension_tendsToInfinity d
  degree_polynomial :=
    (coordinateAt_degree_theta input d hd).polynomiallyBounded
  degree_theta := coordinateAt_degree_theta input d hd

end GolowichProduct

end HDXLean
