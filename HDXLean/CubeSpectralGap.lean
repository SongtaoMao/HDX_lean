import HDXLean.BinaryCube
import HDXLean.FiniteFourierBasis
import HDXLean.ExactSpectralGap
import HDXLean.WeightedRayleigh

/-! The exact cube spectral gap is proved internally, by the binary Fourier
basis. It is not included among the Golowich literature assumptions. -/
namespace HDXLean.GolowichProduct
open scoped BigOperators
open AffineRelationSpectrum

/-- The binary field trace is the identity; its trace package is proved by
finite calculation, with no literature input. -/
def binaryTrace : FiniteFieldTrace.LiteratureInput F₂ where
  trace := LinearMap.id
  pairing_nondegenerate z h := by simpa using h 1
  character_orthogonality z := by
    classical
    change (∑ p : F₂, if p * z = 0 then (1 : ℝ) else -1) =
      if z = 0 then (Fintype.card F₂ : ℝ) else 0
    have hu : (Finset.univ : Finset F₂) = {0, 1} := by decide
    rw [hu]
    have hz : z = (0 : F₂) ∨ z = (1 : F₂) := by
      by_cases hz : z = 0
      · exact Or.inl hz
      · exact Or.inr (Fin.eq_one_of_ne_zero _ hz)
    rcases hz with rfl | rfl <;> norm_num

noncomputable abbrev cubeCharacter (k : ℕ) :=
  FiniteFourierBasis.character (t := k) binaryTrace

theorem cubeGraph_neighbor_sum (k : ℕ) (x : Cube k) (f : Cube k → ℝ) :
    (∑ y, (cubeGraph k).weight x y * f y) =
      ∑ i : Fin k, f (x + cubeBasis k i) := by
  classical
  let e : Fin k → Cube k := fun i ↦ x + cubeBasis k i
  have hinj : Function.Injective e := by
    intro i j h
    exact cubeBasis_injective k (add_left_cancel h)
  have hfilter : (Finset.univ.filter (CubeAdj k x)) = Finset.univ.image e := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, CubeAdj, e]
    exact exists_congr fun i ↦ eq_comm
  calc
    _ = ∑ y ∈ Finset.univ.filter (CubeAdj k x), f y := by
      simp [cubeGraph, Finset.sum_filter, ite_mul]
    _ = ∑ y ∈ Finset.univ.image e, f y := by rw [hfilter]
    _ = _ := Finset.sum_image (fun i _ j _ h ↦ hinj h)

@[simp] theorem cubeGraph_degree (k : ℕ) (x : Cube k) :
    (cubeGraph k).degree x = k := by
  simpa [WeightedGraph.degree] using cubeGraph_neighbor_sum k x (fun _ ↦ 1)

theorem cubeCharacter_basis (k : ℕ) (b : Cube k) (i : Fin k) :
    cubeCharacter k b (cubeBasis k i) = if b i = 0 then 1 else -1 := by
  classical
  simp [cubeCharacter, FiniteFourierBasis.character, AffineRelation.baseCharacter,
    FiniteFourierBasis.dotFunctional, cubeBasis, FiniteFieldTrace.signCharacter,
    binaryTrace, Pi.single_apply]

noncomputable def cubeFrequencyWeight (k : ℕ) (b : Cube k) : ℕ :=
  (Finset.univ.filter fun i ↦ b i ≠ 0).card

theorem cube_character_sign_sum (k : ℕ) (b : Cube k) :
    (∑ i : Fin k, cubeCharacter k b (cubeBasis k i)) =
      (k : ℝ) - 2 * cubeFrequencyWeight k b := by
  classical
  simp_rw [cubeCharacter_basis]
  have h : ∀ i : Fin k, (if b i = 0 then (1 : ℝ) else -1) =
      1 - 2 * (if b i ≠ 0 then 1 else 0) := by
    intro i
    by_cases hi : b i = 0 <;> norm_num [hi]
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hs : (∑ i : Fin k, if b i ≠ 0 then (1 : ℝ) else 0) =
      (cubeFrequencyWeight k b : ℝ) := by
    rw [← Finset.sum_filter]
    simp [cubeFrequencyWeight]
  rw [hs]
  simp

theorem cubeCharacter_eigen (k : ℕ) (hk : 1 ≤ k) (b : Cube k) :
    (cubeGraph k).walk (cubeCharacter k b) = fun x ↦
      (1 - 2 * (cubeFrequencyWeight k b : ℝ) / k) * cubeCharacter k b x := by
  funext x
  rw [WeightedGraph.walk, cubeGraph_neighbor_sum, cubeGraph_degree]
  simp_rw [← FiniteFourierBasis.character_add_argument]
  rw [← Finset.mul_sum, cube_character_sign_sum]
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  field_simp

theorem cubeFrequencyWeight_pos (k : ℕ) (b : Cube k) (hb : b ≠ 0) :
    1 ≤ cubeFrequencyWeight k b := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
    by_contra h
    apply hb
    funext i
    exact not_not.mp (not_exists.mp h i)
  exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩

theorem cubeGraph_character_mean (k : ℕ) (b : Cube k) (hb : b ≠ 0) :
    (cubeGraph k).weightedMean (cubeCharacter k b) = 0 := by
  simp only [WeightedGraph.weightedMean, cubeGraph_degree, ← Finset.mul_sum]
  rw [FiniteFourierBasis.character_sum_eq_zero binaryTrace b hb, mul_zero]

/-- Every mean-zero cube eigenvalue is one of the nonzero-frequency values. -/
theorem cubeGraph_eigenvalue_le (k : ℕ) (hk : 1 ≤ k) (μ : ℝ)
    (hμ : IsMeanZeroEigenvalue (cubeGraph k) μ) : μ ≤ 1 - 2 / (k : ℝ) := by
  classical
  obtain ⟨f, hfn, hfm, hfw⟩ := hμ
  obtain ⟨b, hb⟩ : ∃ b : Cube k,
      FiniteFourierBasis.coefficient binaryTrace f b ≠ 0 := by
    by_contra h
    apply hfn
    funext x
    have hi := FiniteFourierBasis.inversion binaryTrace f x
    have hz : ∀ b : Cube k, FiniteFourierBasis.coefficient binaryTrace f b = 0 :=
      fun b ↦ not_not.mp (not_exists.mp h b)
    simpa [hz] using hi.symm
  have hb0 : b ≠ 0 := by
    intro he
    subst b
    apply hb
    have hm : (∑ x : Cube k, f x) = 0 := by
      simp only [WeightedGraph.weightedMean, cubeGraph_degree,
        ← Finset.mul_sum] at hfm
      exact (mul_eq_zero.mp hfm).resolve_left (by positivity)
    simp [FiniteFourierBasis.coefficient, hm]
  let a : ℝ := 1 - 2 * (cubeFrequencyWeight k b : ℝ) / k
  have hei := cubeCharacter_eigen k hk b
  have hinner : (∑ x : Cube k, cubeCharacter k b x * f x) ≠ 0 := by
    intro h
    apply hb
    simp [FiniteFourierBasis.coefficient, h]
  have hsymmetric : (∑ x : Cube k, cubeCharacter k b x * (cubeGraph k).walk f x) =
      ∑ x : Cube k, (cubeGraph k).walk (cubeCharacter k b) x * f x := by
    have henergy (f g : Cube k → ℝ) : (cubeGraph k).energy f g =
        (k : ℝ) * ∑ x, f x * (cubeGraph k).walk g x := by
      rw [WeightedGraph.energy_walk _ (by intro x; simp; positivity), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [cubeGraph_degree]
      ring
    have he := (cubeGraph k).energy_symm (cubeCharacter k b) f
    rw [henergy, henergy] at he
    have he' := mul_left_cancel₀ (show (k : ℝ) ≠ 0 by positivity) he
    simpa only [mul_comm] using he'
  have hmul : μ * (∑ x : Cube k, cubeCharacter k b x * f x) =
      a * (∑ x : Cube k, cubeCharacter k b x * f x) := by
    rw [hfw, hei] at hsymmetric
    simpa only [a, Finset.mul_sum, mul_assoc, mul_left_comm] using hsymmetric
  have hμa : μ = a := mul_right_cancel₀ hinner hmul
  rw [hμa]
  have hw : (1 : ℝ) ≤ cubeFrequencyWeight k b := by
    exact_mod_cast cubeFrequencyWeight_pos k b hb0
  have hk0 : (0 : ℝ) < k := by positivity
  dsimp [a]
  apply sub_le_sub_left
  exact (div_le_div_iff_of_pos_right hk0).mpr (by linarith)

/-- The normalized hypercube walk has one-sided spectral gap exactly `2/k`.
No external cube-spectrum theorem is assumed. -/
theorem cubeGraph_spectralGap (k : ℕ) (hk : 1 ≤ k) :
    (cubeGraph k).HasSpectralGap (2 / (k : ℝ)) := by
  classical
  let i : Fin k := ⟨0, by omega⟩
  let b := cubeBasis k i
  have hb : b ≠ 0 := cubeBasis_ne_zero k i
  have hw : cubeFrequencyWeight k b = 1 := by
    have hf : (Finset.univ.filter fun j ↦ b j ≠ 0) = {i} := by
      ext j
      simp [b, cubeBasis, Pi.single_apply, eq_comm]
    simp [cubeFrequencyWeight, hf]
  refine ⟨⟨cubeCharacter k b, ?_, cubeGraph_character_mean k b hb, ?_⟩,
    cubeGraph_eigenvalue_le k hk⟩
  · intro h
    have hz := congrFun h 0
    simp at hz
  · simpa [hw] using cubeCharacter_eigen k hk b

end HDXLean.GolowichProduct
