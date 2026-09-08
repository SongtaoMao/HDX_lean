import HDXLean.ProductFaces
import HDXLean.SkeletonCayley

namespace HDXLean.GolowichProduct
open scoped BigOperators
variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
  [AddCommGroup V] [AddCommGroup A]

omit [Fintype V] [Fintype A] in
theorem product_projection_translate (g : V × A) (σ : Finset (V × A)) :
    (translateFace g σ).image Prod.fst = translateFace g.1 (σ.image Prod.fst) := by
  simp only [translateFace, Finset.image_image, Function.comp_def, Prod.fst_add]

omit [Fintype A] in
theorem productTop_translate (G : WeightedGraph V)
    (hG : ∀ g u v, G.weight (g + u) (g + v) = G.weight u v)
    (K : ℕ) (g : V × A) (σ : Finset (V × A)) (hσ : IsProductTop G K σ) :
    IsProductTop G K (translateFace g σ) := by
  obtain ⟨hc, hi, u, v, huv, hp⟩ := hσ
  refine ⟨by rwa [translateFace_card], ?_, g.1 + u, g.1 + v, ?_, ?_⟩
  · intro p hp q hq he
    change p ∈ σ.image (fun x ↦ g + x) at hp
    change q ∈ σ.image (fun x ↦ g + x) at hq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    exact congrArg (g + ·) (hi hp' hq' (add_left_cancel he))
  · simpa only [WeightedGraph.Adj, hG] using huv
  · rw [product_projection_translate, hp]
    simp only [translateFace, Finset.image_insert, Finset.image_singleton]

omit [Fintype A] in
theorem productTop_translate_iff (G : WeightedGraph V)
    (hG : ∀ g u v, G.weight (g + u) (g + v) = G.weight u v)
    (K : ℕ) (g : V × A) (σ : Finset (V × A)) :
    IsProductTop G K (translateFace g σ) ↔ IsProductTop G K σ := by
  constructor
  · intro h
    have ht := productTop_translate G hG K (-g) _ h
    have hc : translateFace (-g) (translateFace g σ) = σ := by
      simpa only [neg_neg] using translateFace_neg_cancel (-g) σ
    rwa [hc] at ht
  · exact productTop_translate G hG K g σ

omit [Fintype V] [Fintype A] in
theorem fiber_card_translate (g : V × A) (σ : Finset (V × A)) (u : V) :
    ((translateFace g σ).filter (fun z ↦ z.1 = g.1 + u)).card =
      (σ.filter (fun z ↦ z.1 = u)).card := by
  classical
  symm
  apply Finset.card_bij (fun z _ ↦ g + z)
  · intro z hz
    obtain ⟨hz, hzu⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨z, hz, rfl⟩,
      by simp only [Prod.fst_add, hzu]⟩
  · intro z _ z' _ h
    exact add_left_cancel h
  · intro z hz
    obtain ⟨hz, hzu⟩ := Finset.mem_filter.mp hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨w, Finset.mem_filter.mpr ⟨hw, add_left_cancel hzu⟩, rfl⟩

omit [Fintype V] [Fintype A] in
theorem projection_pair_translate_iff (g : V × A) (σ : Finset (V × A)) (u v : V) :
    (translateFace g σ).image Prod.fst = {g.1 + u, g.1 + v} ↔
      σ.image Prod.fst = {u, v} := by
  rw [product_projection_translate]
  have hp : translateFace g.1 ({u, v} : Finset V) = {g.1 + u, g.1 + v} := by
    simp only [translateFace, Finset.image_insert, Finset.image_singleton]
  rw [← hp]
  constructor
  · intro h
    apply Finset.Subset.antisymm
    · exact (translateFace_subset_iff _ _ _).mp h.le
    · exact (translateFace_subset_iff _ _ _).mp h.ge
  · exact congrArg _

omit [Fintype A] in
theorem productMass_translate (G : WeightedGraph V)
    (hG : ∀ g u v, G.weight (g + u) (g + v) = G.weight u v)
    (K : ℕ) (g : V × A) (σ : Finset (V × A)) :
    productMass G K (translateFace g σ) = productMass G K σ := by
  classical
  unfold productMass
  simp only [productTop_translate_iff G hG]
  split_ifs with ht
  · let f : V → V → ℝ := fun u v ↦
      if G.Adj u v ∧ (translateFace g σ).image Prod.fst = {u, v}
      then G.weight u v /
        (Nat.choose (K - 1) (((translateFace g σ).filter (fun z ↦ z.1 = u)).card - 1) : ℝ)
      else 0
    change (∑ u, ∑ v, f u v) = _
    rw [← Equiv.sum_comp (Equiv.addLeft g.1) (fun u ↦ ∑ v, f u v)]
    apply Finset.sum_congr rfl
    intro u _
    rw [← Equiv.sum_comp (Equiv.addLeft g.1) (f ((Equiv.addLeft g.1) u))]
    apply Finset.sum_congr rfl
    intro v _
    dsimp [f]
    simp only [WeightedGraph.Adj, hG, projection_pair_translate_iff, fiber_card_translate]
    congr 1
  · rfl

theorem ProductData.translationInvariant (G : WeightedGraph V)
    (hG : ∀ g u v, G.weight (g + u) (g + v) = G.weight u v)
    (K : ℕ) (Z : ProductData G K A) : TranslationInvariant Z.complex := by
  intro g σ
  constructor
  · rw [Z.top_iff, Z.top_iff]
    exact productTop_translate_iff G hG K g σ
  · rw [Z.weight_eq, Z.weight_eq, productMass_translate G hG]

end HDXLean.GolowichProduct
