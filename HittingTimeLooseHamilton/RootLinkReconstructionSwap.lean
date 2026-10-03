module

public import HittingTimeLooseHamilton.RootLinkReconstruction

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma rootCountSet_near (S : Finset A) (b j k : ℕ)
    (σ : FiniteOrder ↥S × FiniteOrder ↥((univ:Finset A)\S))
    (hjk : j≤k) (hkj : k≤j+1) (hkb : k≤b) (hkS : k≤S.card)
    (hjC : b-j≤(univ\S).card) :
    (rootCountSet S b j σ\rootCountSet S b k σ).card≤1 ∧
    (rootCountSet S b k σ\rootCountSet S b j σ).card≤1 := by
  have hS := rootPartPrefix_mono S σ.1 hjk
  have hC := rootPartPrefix_mono (univ\S) σ.2 (Nat.sub_le_sub_left hjk b)
  constructor
  · have hsub : rootCountSet S b j σ\rootCountSet S b k σ ⊆
        rootPartPrefix (univ\S) σ.2 (b-j)\rootPartPrefix (univ\S) σ.2 (b-k) := by
      intro x hx
      obtain ⟨hx,hnot⟩ := mem_sdiff.mp hx
      rcases mem_union.mp hx with hx|hx
      · exact False.elim (hnot (mem_union.mpr (Or.inl (hS hx))))
      · exact mem_sdiff.mpr ⟨hx,fun hh=>hnot (mem_union.mpr (Or.inr hh))⟩
    apply (card_le_card hsub).trans
    rw [card_sdiff_of_subset hC,rootPartPrefix_card _ _ _ hjC,
      rootPartPrefix_card _ _ _ ((Nat.sub_le_sub_left hjk b).trans hjC)]
    omega
  · have hsub : rootCountSet S b k σ\rootCountSet S b j σ ⊆
        rootPartPrefix S σ.1 k\rootPartPrefix S σ.1 j := by
      intro x hx
      obtain ⟨hx,hnot⟩ := mem_sdiff.mp hx
      rcases mem_union.mp hx with hx|hx
      · exact mem_sdiff.mpr ⟨hx,fun hh=>hnot (mem_union.mpr (Or.inl hh))⟩
      · exact False.elim (hnot (mem_union.mpr (Or.inr (hC hx))))
    apply (card_le_card hsub).trans
    rw [card_sdiff_of_subset hS,rootPartPrefix_card _ _ _ hkS,rootPartPrefix_card _ _ _ (hjk.trans hkS)]
    omega

lemma equal_card_near_swap {S T : Finset A} (hc : S.card=T.card) (hnear : (S\T).card≤1) :
    S=T ∨ ∃ x y : A, S.image (Equiv.swap x y)=T := by
  by_cases heq : S=T
  · exact Or.inl heq
  · right
    have hST : ¬S⊆T := by
      intro hh
      exact heq (eq_of_subset_of_card_le hh hc.symm.le)
    obtain ⟨x,hxS,hxT⟩ := not_subset.mp hST
    have hx : x∈S\T := mem_sdiff.mpr ⟨hxS,hxT⟩
    have hcST : (S\T).card=1 := by have := card_pos.mpr ⟨x,hx⟩; omega
    obtain ⟨x',hx'⟩ := card_eq_one.mp hcST
    have hxx' : x=x' := by simpa [hx'] using hx
    subst x'
    have hcTS : (T\S).card=1 := by
      have h1 := card_sdiff_add_card_inter S T
      have h2 := card_sdiff_add_card_inter T S
      rw [inter_comm T S] at h2
      omega
    obtain ⟨y,hy'⟩ := card_eq_one.mp hcTS
    have hy : y∈T\S := by rw [hy']; simp
    obtain ⟨hyT,hyS⟩ := mem_sdiff.mp hy
    have hxy : x≠y := by intro he; subst y; contradiction
    refine ⟨x,y,?_⟩
    have hsame (z : A) (hzx : z≠x) (hzy : z≠y) : z∈S ↔ z∈T := by
      have hs : z∉S\T := by rw [hx']; simpa
      have ht : z∉T\S := by rw [hy']; simpa
      simp only [mem_sdiff] at hs ht
      tauto
    ext z
    have he : z∈S.image (Equiv.swap x y) ↔ Equiv.swap x y z∈S := by
      constructor
      · rintro hz
        obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
        simpa using hw
      · intro hz
        exact mem_image.mpr ⟨Equiv.swap x y z,hz,by simp⟩
    rw [he]
    by_cases hzx : z=x
    · subst z
      simp [hyS,hxT]
    by_cases hzy : z=y
    · subst z
      simp [hxS,hyT]
    rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
    exact hsame z hzx hzy

lemma rootCountSet_swap (S : Finset A) (b j k : ℕ)
    (σ : FiniteOrder ↥S × FiniteOrder ↥((univ:Finset A)\S))
    (hjk : j≤k) (hkj : k≤j+1) (hkb : k≤b) (hkS : k≤S.card)
    (hjC : b-j≤(univ\S).card) :
    rootCountSet S b j σ=rootCountSet S b k σ ∨
      ∃ x y : A, (rootCountSet S b j σ).image (Equiv.swap x y)=rootCountSet S b k σ := by
  apply equal_card_near_swap
  · rw [rootCountSet_card _ _ _ _ (hjk.trans hkb) (hjk.trans hkS) hjC,
      rootCountSet_card _ _ _ _ hkb hkS ((Nat.sub_le_sub_left hjk b).trans hjC)]
  · exact (rootCountSet_near S b j k σ hjk hkj hkb hkS hjC).1
end LooseHamilton
