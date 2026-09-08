import HDXLean.GolowichCited
import Mathlib.Data.Finset.Card

/-! Edges of the literal product complex. Extending a pair to a facet is
proved with fresh labels, not assumed from the desired Cayley conclusion. -/
namespace HDXLean.GolowichProduct
variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]

theorem pair_extends_to_productTop (G : WeightedGraph V) (K : ℕ) (hK : 2 ≤ K)
    (hA : K + 1 ≤ Fintype.card A) (u v y : V) (huv : G.Adj u v)
    (hy : y = u ∨ y = v) (a b : A) (hab : a ≠ b) :
    ∃ σ : Finset (V × A), IsProductTop G K σ ∧ {(u, a), (y, b)} ⊆ σ := by
  classical
  have hcapa : ({a, b} : Finset A).card < Fintype.card A := by
    simp [hab]; omega
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({a, b} : Finset A).card < (Finset.univ : Finset A).card by simpa using hcapa)
  have hca : c ≠ a := by intro h; apply hc; simp [h]
  have hcb : c ≠ b := by intro h; apply hc; simp [h]
  have hsmall : ({a, b, c} : Finset A).card ≤ K + 1 := by
    have : ({a, b, c} : Finset A).card = 3 := by simp [hab, hca.symm, hcb.symm]
    omega
  obtain ⟨L, hLsmall, _, hLcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ ({a, b, c} : Finset A)) hsmall (by simpa using hA)
  let f : A → V × A := fun z ↦ (if z = c then v else if z = b then y else u, z)
  have hinj : Function.Injective f := fun z z' he ↦ congrArg Prod.snd he
  have haL : a ∈ L := hLsmall (by simp)
  have hbL : b ∈ L := hLsmall (by simp)
  have hcL : c ∈ L := hLsmall (by simp)
  have hfa : f a = (u, a) := by simp [f, hca.symm, hab]
  have hfb : f b = (y, b) := by simp [f, hcb.symm]
  have hfc : f c = (v, c) := by simp [f]
  refine ⟨L.image f, ⟨?_, ?_, u, v, huv, ?_⟩, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, hLcard]
  · intro p hp q hq he
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨z', _, rfl⟩ := Finset.mem_image.mp hq
    exact congrArg f he
  · apply Finset.Subset.antisymm
    · intro z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hp
      dsimp [f]
      split_ifs <;> simp_all
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz
      · rw [hz]
        exact Finset.mem_image.mpr ⟨(u, a),
          Finset.mem_image.mpr ⟨a, haL, hfa⟩, rfl⟩
      · rw [hz]
        exact Finset.mem_image.mpr ⟨(v, c),
          Finset.mem_image.mpr ⟨c, hcL, hfc⟩, rfl⟩
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨Finset.mem_image.mpr ⟨a, haL, hfa⟩,
      Finset.mem_image.mpr ⟨b, hbL, hfb⟩⟩

theorem product_face_pair_iff (G : WeightedGraph V) (K : ℕ) (Z : ProductData G K A)
    (hK : 2 ≤ K) (hA : K + 1 ≤ Fintype.card A)
    (hneigh : ∀ u, ∃ v, G.Adj u v) (x y : V × A) :
    Z.complex.IsFace {x, y} ↔
      x = y ∨ (x.2 ≠ y.2 ∧ (x.1 = y.1 ∨ G.Adj x.1 y.1)) := by
  classical
  constructor
  · rintro ⟨σ, hσ, hxy⟩
    obtain ⟨_, hinj, u, v, huv, hproj⟩ := (Z.top_iff σ).mp hσ
    have hx : x ∈ σ := hxy (by simp)
    have hy : y ∈ σ := hxy (by simp)
    by_cases heq : x = y
    · exact Or.inl heq
    · refine Or.inr ⟨fun h ↦ heq (hinj hx hy h), ?_⟩
      have hxu : x.1 ∈ ({u, v} : Finset V) := by
        rw [← hproj]; exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      have hyv : y.1 ∈ ({u, v} : Finset V) := by
        rw [← hproj]; exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxu hyv
      rcases hxu with hx | hx <;> rcases hyv with hy | hy
      · exact Or.inl (hx.trans hy.symm)
      · exact Or.inr (by simpa [hx, hy] using huv)
      · exact Or.inr (by simpa [hx, hy] using (G.adj_symm.mp huv))
      · exact Or.inl (hx.trans hy.symm)
  · intro h
    have hconstruct : ∀ (x y : V × A), x.2 ≠ y.2 →
        (x.1 = y.1 ∨ G.Adj x.1 y.1) → Z.complex.IsFace {x, y} := by
      intro x y hlabel hbase
      obtain ⟨v, hv, hy⟩ : ∃ v, G.Adj x.1 v ∧ (y.1 = x.1 ∨ y.1 = v) := by
        rcases hbase with heq | hedge
        · obtain ⟨v, hv⟩ := hneigh x.1
          exact ⟨v, hv, Or.inl heq.symm⟩
        · exact ⟨y.1, hedge, Or.inr rfl⟩
      obtain ⟨σ, hσ, hsub⟩ := pair_extends_to_productTop G K hK hA
        x.1 v y.1 hv hy x.2 y.2 hlabel
      exact ⟨σ, (Z.top_iff σ).mpr hσ, hsub⟩
    rcases h with rfl | ⟨hlab, hbase⟩
    · have hcard : 1 < Fintype.card A := by omega
      obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card hcard x.2
      exact Z.complex.isFace_mono
        (hconstruct x (x.1, b) hb.symm (Or.inl rfl)) (by simp)
    · exact hconstruct x y hlab hbase

end HDXLean.GolowichProduct
