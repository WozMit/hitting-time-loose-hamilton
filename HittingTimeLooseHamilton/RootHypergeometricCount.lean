module

public import HittingTimeLooseHamilton.KahnRandomOrder
public import HittingTimeLooseHamilton.RootHypergeometricWeights
public import HittingTimeLooseHamilton.NatLawAtoms
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

public section

/-! Exact finite intersection counts for the root-link hypergeometric law. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {α : Type*} [DecidableEq α]

/-- Splitting a fixed-size subset by a distinguished subuniverse gives the
usual product of binomial coefficients. -/
theorem root_intersection_fiber_card (U S : Finset α) (hS : S⊆U) (b j : ℕ) (hj : j≤b) :
    ((U.powersetCard b).filter (fun A => (A∩S).card=j)).card =
      S.card.choose j*(U\S).card.choose (b-j) := by
  classical
  rw [←card_powersetCard j S,←card_powersetCard (b-j) (U\S),←card_product]
  apply card_bij (fun A _ => (A∩S,A\S))
  · intro A hA
    obtain ⟨⟨hAU,hAb⟩,hAS⟩ := by simpa only [mem_filter,mem_powersetCard] using hA
    apply mem_product.mpr
    constructor
    · exact mem_powersetCard.mpr ⟨inter_subset_right,hAS⟩
    · refine mem_powersetCard.mpr ⟨sdiff_subset_sdiff hAU subset_rfl,?_⟩
      change (A\S).card=b-j
      have h := card_sdiff_add_card_inter A S
      rw [hAS,hAb] at h
      omega
  · intro A hA B hB hAB
    have h1 := congrArg Prod.fst hAB
    have h2 := congrArg Prod.snd hAB
    dsimp only at h1 h2
    calc
      A = A\S∪A∩S := (sdiff_union_inter A S).symm
      _ = B\S∪B∩S := by rw [h1,h2]
      _ = B := sdiff_union_inter B S
  · intro p hp
    obtain ⟨hB,hC⟩ := mem_product.mp hp
    obtain ⟨hBS,hBj⟩ := mem_powersetCard.mp hB
    obtain ⟨hCU,hCc⟩ := mem_powersetCard.mp hC
    have hd : Disjoint p.1 p.2 := by
      apply disjoint_left.mpr
      intro a ha hb
      exact (mem_sdiff.mp (hCU hb)).2 (hBS ha)
    have hi : (p.1∪p.2)∩S=p.1 := by
      ext a
      simp only [mem_inter,mem_union]
      constructor
      · rintro ⟨ha,hS⟩
        exact ha.resolve_right (fun hb => (mem_sdiff.mp (hCU hb)).2 hS)
      · intro ha
        exact ⟨Or.inl ha,hBS ha⟩
    have hs : (p.1∪p.2)\S=p.2 := by
      ext a
      simp only [mem_sdiff,mem_union]
      constructor
      · rintro ⟨ha,hn⟩
        exact ha.resolve_left (fun hb=>hn (hBS hb))
      · intro ha
        exact ⟨Or.inr ha,(mem_sdiff.mp (hCU ha)).2⟩
    refine ⟨p.1∪p.2,mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_,?_⟩,?_⟩,?_⟩
    · exact union_subset (hBS.trans hS) (hCU.trans sdiff_subset)
    · rw [card_union_of_disjoint hd,hBj,hCc]
      omega
    · simpa only [hi] using hBj
    · exact Prod.ext hi hs

/-- An intersection cannot exceed the sampled set's fixed size. -/
theorem root_intersection_fiber_card_zero (U S : Finset α) (b j : ℕ) (hj : b<j) :
    ((U.powersetCard b).filter (fun A => (A∩S).card=j)).card=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro A hA
  obtain ⟨ha,hi⟩ := mem_filter.mp hA
  have hb := (mem_powersetCard.mp ha).2
  have hh := card_le_card (inter_subset_left : A∩S⊆A)
  omega

/-- Exact atom probability under uniform fixed-size subset sampling. -/
theorem root_intersection_uniform_atom (U S : Finset α) (hS : S⊆U) (b j : ℕ)
    [Nonempty ↥(U.powersetCard b)] (hj : j≤b) :
    (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event
      (fun A => (A.val∩S).card=j) =
      ((S.card.choose j:ℝ)*((U\S).card.choose (b-j):ℝ))/(U.card.choose b:ℝ) := by
  classical
  rw [FiniteEntropy.Law.uniform_event,Fintype.card_coe,card_powersetCard]
  have he : (univ.filter (fun A : ↥(U.powersetCard b) => (A.val∩S).card=j)).card =
      ((U.powersetCard b).filter (fun A => (A∩S).card=j)).card := by
    apply card_bij (fun A _ => A.val)
    · intro A hA
      exact mem_filter.mpr ⟨A.property,(mem_filter.mp hA).2⟩
    · intro A hA B hB he
      exact Subtype.ext he
    · intro A hA
      exact ⟨⟨A,(mem_filter.mp hA).1⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hA).2⟩,rfl⟩
  rw [he,root_intersection_fiber_card U S hS b j hj,Nat.cast_mul]

/-- The complete atom formula, including the zero mass beyond the sample size. -/
theorem root_intersection_natLawAtom (U S : Finset α) (hS : S⊆U) (b j : ℕ)
    [Nonempty ↥(U.powersetCard b)] :
    natLawAtom (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b))
      (fun A => (A.val∩S).card) j =
      rootHypergeometricWeight S.card (U\S).card b j/(U.card.choose b:ℝ) := by
  by_cases hj : j≤b
  · simpa only [natLawAtom,rootHypergeometricWeight,if_pos hj] using
      root_intersection_uniform_atom U S hS b j hj
  · have hz : natLawAtom (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b))
        (fun A => (A.val∩S).card) j = 0 := by
      apply natLawAtom_eq_zero _ _ b
      · intro A
        exact (card_le_card inter_subset_left).trans_eq (mem_powersetCard.mp A.property).2
      · omega
    rw [hz,rootHypergeometricWeight,if_neg hj,zero_div]
end LooseHamilton
