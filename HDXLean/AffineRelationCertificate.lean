import HDXLean.AffineRelationCombinatorics
import HDXLean.AffineRelationKernel
import HDXLean.AffineRelationSpectrum
import HDXLean.SectionThreeArithmetic

/-!
# Complete certificates for the affine relation matrix

This module combines Lemmas 3.5--3.7 in the exact structure consumed by the
cited relation-matrix compiler.  It also performs the parameter substitution
from Section 3.3, so a direction set with the size and distance supplied by
Lemma 3.2 produces a certificate at any target larger than `4/(q-2)`.
-/

namespace HDXLean

open AffineRelationSpectrum

namespace AffineRelation

universe u v

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
  [CharP F 2] [Algebra F₂ F]
variable {t : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- Lemmas 3.5 and 3.6 packaged as the hypotheses of the cited compiler. -/
theorem compilerHypotheses
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (hfield : 2 < Fintype.card F) (hdirections : Nonempty ι) :
    RelationMatrix.CompilerHypotheses (matrix D) (rho F ι) where
  rowsDistinct := rowsDistinct D
  rowsHaveWeightThree := rowsHaveWeightThree D
  constantColumnWeight := constantColumnWeight D hfield hdirections
  rowDistance := AffineRelationKernel.rowDistanceAtLeastThree input D

/-- Lemmas 3.5--3.7 combined into the final relation-matrix certificate.
The only extra input is the explicit finite Fourier interface exposed by
`AffineRelationSpectrum.FourierInterface`. -/
theorem fullSpectralCertificate
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι) (minimumWeight : ℕ)
    (hlower : HasLowerDistance F D minimumWeight)
    (hminimum : 0 < minimumWeight)
    (hfield : 4 ≤ Fintype.card F) (hdirections : Nonempty ι)
    (fourier : FourierInterface input D)
    (lambda : ℝ)
    (hnegative : 1 / ((Fintype.card F : ℝ) - 2) ≤ lambda)
    (hupper : max
      (1 - (Fintype.card F : ℝ) * (minimumWeight : ℝ) /
        (((Fintype.card F : ℝ) - 1) * (Fintype.card ι : ℝ)))
      (1 / (((Fintype.card F : ℝ) - 2) *
        ((Fintype.card F : ℝ) - 1))) ≤ lambda) :
    RelationMatrix.SpectralCertificate (matrix D) (rho F ι) lambda := by
  have hfieldTwo : 2 < Fintype.card F := by omega
  have hfieldReal : 4 ≤ fieldCard (F := F) := by
    simp only [fieldCard]
    exact_mod_cast hfield
  have hdirectionsReal : 0 < directionCount (ι := ι) := by
    simp only [directionCount]
    exact_mod_cast Fintype.card_pos_iff.mpr hdirections
  have hnormalization :
      normalization (F := F) (ι := ι) = 2 * (rho F ι : ℝ) :=
    normalization_eq_two_rho_of_count (rho F ι) (by omega) (rho_mul_two D)
  exact AffineRelationSpectrum.spectralCertificate input D minimumWeight hlower
    hminimum hfieldReal hdirectionsReal fourier (rho F ι)
    (compilerHypotheses input D hfieldTwo hdirections)
    (pairMultiplicityAtMostOne D) hnormalization lambda hnegative hupper

/-- Section 3.3 specialization.  Here `q` is the square root of the field
size, `g` is the tower genus, and the direction set has the exact size and
lower distance supplied by Lemma 3.2. -/
theorem sectionThreeSpectralCertificate
    (input : FiniteFieldTrace.LiteratureInput F)
    (D : DirectionSet F t ι)
    (q g : ℕ) (hq : 8 ≤ q) (hg : 0 < g)
    (hfieldCard : Fintype.card F = q ^ 2)
    (hdirectionCard : Fintype.card ι = (q - 2) * g)
    (hlower : HasLowerDistance F D ((q - 5) * g))
    (fourier : FourierInterface input D)
    (lambda : ℝ) (hchoice : 4 / ((q : ℝ) - 2) < lambda) :
    RelationMatrix.SpectralCertificate (matrix D) (rho F ι) lambda := by
  have hfieldFour : 4 ≤ Fintype.card F := by
    rw [hfieldCard]
    nlinarith
  have hdirectionPositive : 0 < Fintype.card ι := by
    rw [hdirectionCard]
    exact Nat.mul_pos (by omega) hg
  have hdirections : Nonempty ι := Fintype.card_pos_iff.mp hdirectionPositive
  have hminimum : 0 < (q - 5) * g := Nat.mul_pos (by omega) hg
  apply fullSpectralCertificate input D ((q - 5) * g) hlower hminimum
    hfieldFour hdirections fourier lambda
  · have hneg := sectionThree_one_div_sq_sub_two_lt_four_div_sub_two
      (show (8 : ℝ) ≤ q by exact_mod_cast hq)
    have hfieldReal : (Fintype.card F : ℝ) = (q : ℝ) ^ 2 := by
      exact_mod_cast hfieldCard
    rw [hfieldReal]
    exact hneg.le.trans hchoice.le
  · have hqReal : (8 : ℝ) ≤ q := by exact_mod_cast hq
    have hgReal : (0 : ℝ) < g := by exact_mod_cast hg
    have hfieldReal : (Fintype.card F : ℝ) = (q : ℝ) ^ 2 := by
      exact_mod_cast hfieldCard
    have hdirectionReal : (Fintype.card ι : ℝ) = ((q : ℝ) - 2) * g := by
      rw [hdirectionCard]
      norm_num only [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ q)]
    have hminimumReal : (((q - 5) * g : ℕ) : ℝ) =
        ((q : ℝ) - 5) * g := by
      norm_num only [Nat.cast_mul, Nat.cast_sub (by omega : 5 ≤ q)]
    rw [hfieldReal, hdirectionReal, hminimumReal,
      sectionThree_direction_endpoint_eq hqReal hgReal]
    exact (sectionThree_max_upper_lt_four_div_sub_two hqReal).le.trans
      hchoice.le

end AffineRelation

end HDXLean
