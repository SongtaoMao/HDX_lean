import HDXLean.AlgebraicGeometry

/-!
# Point selection capacity from the cited tower limits

The eventual availability of `(q-2)g` evaluation points and one reserved
point is a deduction from the point/genus ratio, not another tower axiom.
-/

namespace HDXLean

/-- The epsilon `1/2` and genus at least two provide the one extra point
needed for `P_infinity`. -/
theorem selectedPointCapacity_of_ratio (q : ℕ) (hq : 2 ≤ q)
    (points genus : ℕ → ℕ) (hgenus : TendsToInfinity genus)
    (hratio : PointGenusRatioConverges points genus (q - 1 : ℕ)) :
    Eventually fun r ↦ 1 + (q - 2) * genus r ≤ points r := by
  obtain ⟨N, hN⟩ := (hratio (1 / 2) (by norm_num)).and (hgenus 2)
  refine ⟨N, fun r hr ↦ ?_⟩
  obtain ⟨hclose, hg⟩ := hN r hr
  have hgpos : (0 : ℝ) < genus r := by positivity
  have hlow := (abs_lt.mp hclose).1
  have hquot : ((q - 1 : ℕ) : ℝ) - 1 / 2 < (points r : ℝ) / genus r := by
    linarith
  have hprod := (lt_div_iff₀ hgpos).mp hquot
  have hqcast : ((q - 1 : ℕ) : ℝ) = ((q - 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show q - 1 = (q - 2) + 1 by omega)
  rw [hqcast] at hprod
  have hgcast : (2 : ℝ) ≤ genus r := by exact_mod_cast hg
  have hfinal : (1 : ℝ) + ((q - 2 : ℕ) : ℝ) * genus r ≤ points r := by
    nlinarith
  exact_mod_cast hfinal

/-- Assemble the historical tower record from its growth statements,
internally filling the formerly separate point-capacity field. The legacy
algorithmic marker is set to `True` because algorithmic claims are excluded;
it is not a certificate of an algorithm. -/
def GarciaStichtenothTowerInput.ofGrowth
    {F : Type*} [Field F] [Fintype F] (P : SquareFieldParameters F)
    (genus points : ℕ → ℕ) (hgenus : TendsToInfinity genus)
    (hratio : PointGenusRatioConverges points genus (P.q - 1 : ℕ)) :
    GarciaStichtenothTowerInput P where
  genus := genus
  rationalPointCount := points
  genus_tendsToInfinity := hgenus
  point_genus_ratio := hratio
  selectedPointCapacity := selectedPointCapacity_of_ratio P.q
    (le_trans (by norm_num) P.q_ge_eight) points genus hgenus hratio
  explicitConstruction := True
  explicitConstruction_proof := trivial

end HDXLean
