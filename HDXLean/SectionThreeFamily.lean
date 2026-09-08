import HDXLean.AffineRelationCertificate
import HDXLean.AlgebraicGeometry
import HDXLean.FiniteFourierBasis
import HDXLean.TwoDimensionalIndexed

/-!
# The relation-matrix family from the algebraic-geometric directions

This module installs the concrete affine relation matrix at every level of a
`Lemma32DirectionFamily`.  All exact combinatorial, kernel, and spectral
fields of Lemma 2.3 are derived here.  The three remaining elementary
asymptotic consequences of the nullity lower bound are kept together in
`AsymptoticCertificate`; this makes the boundary visible while those natural-
logarithm estimates are formalized separately.
-/

namespace HDXLean

namespace SectionThreeFamily

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  [CharP F 2] [Algebra F₂ F]
variable (P : SquareFieldParameters F)

/-- The intrinsic row type at level `r`. -/
abbrev Row (family : Lemma32DirectionFamily P) (r : ℕ) :=
  AffineRelation.RowIndex F (family.t r)
    (Fin ((P.q - 2) * family.genus r))

/-- The intrinsic column type at level `r`. -/
abbrev Column (family : Lemma32DirectionFamily P) (r : ℕ) :=
  AffineRelation.Column F (family.t r)

/-- The concrete relation matrix at level `r`. -/
noncomputable def matrix (family : Lemma32DirectionFamily P) (r : ℕ) :
    BinaryMatrix (Row P family r) (Column P family r) :=
  AffineRelation.matrix (family.directions r)

/-- The exact common column weight at level `r`. -/
def rho (family : Lemma32DirectionFamily P) (r : ℕ) : ℕ :=
  AffineRelation.rho F (Fin ((P.q - 2) * family.genus r))

/-- The binary nullity used as the ambient dimension after compilation. -/
noncomputable def ambientDimension
    (family : Lemma32DirectionFamily P) (r : ℕ) : ℕ :=
  RelationMatrix.nullity (matrix P family r)

/-- The only numerical conclusions not needed to establish an individual
matrix certificate.  They are the natural-logarithm consequences of the
exponential nullity lower bound used at the end of Section 3.3. -/
structure AsymptoticCertificate (family : Lemma32DirectionFamily P) : Prop where
  ambientDimension_tendsToInfinity :
    TendsToInfinity (ambientDimension P family)
  degree_polynomial :
    PolynomiallyBounded
      (fun r ↦ Fintype.card (Column P family r))
      (ambientDimension P family)
  rho_logarithmic :
    LogarithmicallyBounded (rho P family) (ambientDimension P family)

omit [CharP F 2] [Algebra F₂ F] in
/-- The exact column-count formula in Lemma 2.3. -/
theorem columnCount_formula (family : Lemma32DirectionFamily P) (r : ℕ) :
    Fintype.card (Column P family r) =
      (P.q ^ 2 - 1) * (P.q ^ 2) ^ family.t r := by
  rw [AffineRelation.card_column, P.card_field]

omit [Algebra F₂ F] in
/-- The exact division-free row-count formula in Lemma 2.3. -/
theorem rowCount_formula (family : Lemma32DirectionFamily P) (r : ℕ) :
    3 * Fintype.card (Row P family r) =
      rho P family r * Fintype.card (Column P family r) := by
  exact AffineRelation.three_mul_card_rowIndex_eq_rho_mul_card_column
    (family.directions r)

omit [DecidableEq F] [CharP F 2] [Algebra F₂ F] in
/-- Since `q` is fixed, the common column weight is linear in the direction
count and therefore linear in the ambient parameter `t`. -/
theorem rho_linear_in_t (family : Lemma32DirectionFamily P) :
    LinearBounded (rho P family) family.t := by
  rcases family.size_linear with ⟨C, r₀, hsize⟩
  let K := (Fintype.card F - 2) * (Fintype.card F - 1)
  refine ⟨K * C, r₀, fun r hr ↦ ?_⟩
  have hcard : Fintype.card (Fin ((P.q - 2) * family.genus r)) =
      (P.q - 2) * family.genus r := Fintype.card_fin _
  calc
    rho P family r =
        ((Fintype.card F - 2) *
          ((Fintype.card F - 1) * ((P.q - 2) * family.genus r))) / 2 := by
      simp only [rho, AffineRelation.rho, hcard]
    _ ≤ (Fintype.card F - 2) *
          ((Fintype.card F - 1) * ((P.q - 2) * family.genus r)) :=
      Nat.div_le_self _ _
    _ = K * ((P.q - 2) * family.genus r) := by
      dsimp [K]
      ac_rfl
    _ ≤ K * (C * (family.t r + 1)) :=
      Nat.mul_le_mul_left K (hsize r hr)
    _ = (K * C) * (family.t r + 1) := by
      dsimp [K]
      ac_rfl

set_option maxHeartbeats 3200000 in
/-- Assemble the concrete matrices into the arbitrary-index version of Lemma
2.3.  The finite Fourier bridge is proved internally in
`FiniteFourierBasis`; the only external inputs here are the cited trace facts. -/
noncomputable def toIndexedCertificate {lambda : ℝ}
    (family : Lemma32DirectionFamily P)
    (traceInput : FiniteFieldTrace.LiteratureInput F)
    (hchoice : 4 / ((P.q : ℝ) - 2) < lambda)
    (asymptotics : AsymptoticCertificate P family) :
    IndexedLemmaTwoThreeCertificate lambda where
  h := P.h
  q := P.q
  q_eq := P.q_eq_two_pow
  q_at_least_eight := P.q_ge_eight
  q_spectral_choice := hchoice
  t := family.t
  Row := Row P family
  Column := Column P family
  rowFintype := fun _ ↦ inferInstance
  rowDecidableEq := fun _ ↦ inferInstance
  columnFintype := fun _ ↦ inferInstance
  columnDecidableEq := fun _ ↦ inferInstance
  rowCount := fun r ↦ Fintype.card (Row P family r)
  columnCount := fun r ↦ Fintype.card (Column P family r)
  rowCount_eq_card := fun _ ↦ rfl
  columnCount_eq_card := fun _ ↦ rfl
  rho := rho P family
  ambientDimension := ambientDimension P family
  matrix := matrix P family
  columnCount_formula := columnCount_formula P family
  rowCount_formula := rowCount_formula P family
  nullity_eq := fun _ ↦ rfl
  t_tendsToInfinity := family.t_tendsToInfinity
  rho_linear_in_t := rho_linear_in_t P family
  ambientDimension_tendsToInfinity := asymptotics.ambientDimension_tendsToInfinity
  degree_polynomial := asymptotics.degree_polynomial
  rho_logarithmic := asymptotics.rho_logarithmic
  spectralCertificate := fun r ↦
    AffineRelation.sectionThreeSpectralCertificate traceInput
      (family.directions r) P.q (family.genus r) P.q_ge_eight
      (lt_of_lt_of_le (by norm_num) (family.genus_lower_bound r))
      P.card_field (Fintype.card_fin _) (family.lowerDistance r)
      (FiniteFourierBasis.interface traceInput (family.directions r)
        (by
          rw [P.card_field]
          nlinarith [P.q_ge_eight])
        (Fintype.card_pos_iff.mp (by
          rw [Fintype.card_fin]
          exact Nat.mul_pos
            (Nat.sub_pos_of_lt
              (lt_of_lt_of_le (by norm_num) P.q_ge_eight))
            (lt_of_lt_of_le (by norm_num) (family.genus_lower_bound r)))))
      lambda hchoice

/-- The concrete Section 3 family, the cited compiler, and the three explicit
asymptotic estimates yield the family asserted in Theorem 1.1. -/
noncomputable def toTwoDimensionalFamily {lambda : ℝ}
    (family : Lemma32DirectionFamily P)
    (traceInput : FiniteFieldTrace.LiteratureInput F)
    (hchoice : 4 / ((P.q : ℝ) - 2) < lambda)
    (asymptotics : AsymptoticCertificate P family)
    (compiler : RelationCompiler.LiteratureInput) :
    TwoDimensionalFamily lambda :=
  IndexedLemmaTwoThreeCertificate.toTwoDimensionalFamily
    (toIndexedCertificate P family traceInput hchoice asymptotics)
    compiler

end SectionThreeFamily

end HDXLean
