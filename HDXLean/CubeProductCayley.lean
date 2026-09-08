import HDXLean.BinaryCube
import HDXLean.GolowichProduct
import HDXLean.ProductTranslation
import HDXLean.ProductConnected

namespace HDXLean.GolowichProduct

def cubeSteps (k : ℕ) : Finset (Cube k) := insert 0 (Finset.univ.image (cubeBasis k))

def productGenerators (d k : ℕ) : Finset (Cube k × Label d) :=
  (cubeSteps k).product (Finset.univ.erase 0)

theorem cubeSteps_card (k : ℕ) : (cubeSteps k).card = k + 1 := by
  have hn : (0 : Cube k) ∉ Finset.univ.image (cubeBasis k) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro i _ hi
    exact cubeBasis_ne_zero k i hi
  rw [cubeSteps, Finset.card_insert_of_notMem hn,
    Finset.card_image_of_injective _ (cubeBasis_injective k)]
  simp

theorem productGenerators_card (d k : ℕ) :
    (productGenerators d k).card = (Fintype.card (Label d) - 1) * (k + 1) := by
  change ((cubeSteps k) ×ˢ (Finset.univ.erase (0 : Label d))).card = _
  rw [Finset.card_product, cubeSteps_card,
    Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  exact Nat.mul_comm _ _

theorem cube_neg (k : ℕ) (x : Cube k) : -x = x := by
  have h := cube_add_self k x
  exact neg_eq_of_add_eq_zero_left h

theorem mem_productGenerators_sub (d k : ℕ) (x y : Cube k × Label d) :
    y - x ∈ productGenerators d k ↔
      x.2 ≠ y.2 ∧ (x.1 = y.1 ∨ (cubeGraph k).Adj x.1 y.1) := by
  classical
  change y - x ∈ (cubeSteps k) ×ˢ (Finset.univ.erase (0 : Label d)) ↔ _
  simp only [Finset.mem_product, cubeSteps, Finset.mem_insert,
    Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true,
    Prod.fst_sub, Prod.snd_sub, sub_eq_zero, cubeGraph_adj, CubeAdj]
  have he : (∃ i, cubeBasis k i = y.1 - x.1) ↔ ∃ i, y.1 = x.1 + cubeBasis k i := by
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by rw [hi]; simp [add_comm x.1]⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, by rw [hi]; simp⟩
  rw [he]
  have hn : y.2 - x.2 ≠ 0 ↔ x.2 ≠ y.2 := by
    rw [sub_ne_zero]
    exact ne_comm
  rw [hn, eq_comm (a := y.1) (b := x.1)]
  tauto

/-- The paper's Cayley structure and exact degree on the actual cited product. -/
noncomputable def cubeProductCayley (d k : ℕ) (hd : 2 ≤ d) (hk : 2 ≤ k)
    (Z : ProductData (cubeGraph k) (2 * d) (Label d)) :
    CayleyComplex (V := Cube k × Label d) where
  complex := Z.complex
  translationInvariant := Z.translationInvariant _ (cubeGraph_translation k) _
  cayley :=
    { generators := productGenerators d k
      zero_not_mem := by simp [productGenerators]
      neg_mem_iff := by
        intro s
        have hs : -s = s := Prod.ext (cube_neg k s.1) (cube_neg (labelRank d) s.2)
        rw [hs]
      edge_iff := by
        intro x y
        rw [mem_productGenerators_sub]
        exact product_face_pair_iff _ _ Z (by omega)
          ((show 2 * d + 1 ≤ 4 * d by omega).trans (label_capacity d))
          (cubeGraph_neighbor k (by omega)) x y }

@[simp] theorem cubeProductCayley_degree (d k : ℕ) (hd : 2 ≤ d) (hk : 2 ≤ k)
    (Z : ProductData (cubeGraph k) (2 * d) (Label d)) :
    (cubeProductCayley d k hd hk Z).cayley.degree =
      (Fintype.card (Label d) - 1) * (k + 1) := productGenerators_card d k

end HDXLean.GolowichProduct
