module

public import HittingTimeLooseHamilton.RootOuterKernel

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma outerExtension_card (U I : Finset A) (q : ℕ) (hIU : I⊆U) (hIq : I.card≤q) :
    Fintype.card (OuterExtension U I q)=(U.card-I.card).choose (q-I.card) := by
  classical
  have hs : (U\I).card=U.card-I.card := card_sdiff_of_subset hIU
  rw [← hs,← card_powersetCard]
  change (univ : Finset (OuterExtension U I q)).card = _
  apply card_bij (fun T _ => T.val\I)
  · intro T hT
    obtain ⟨hTU,hTq⟩ := mem_powersetCard.mp T.property.2
    exact mem_powersetCard.mpr ⟨sdiff_subset_sdiff hTU (Subset.refl _),by rw [card_sdiff_of_subset T.property.1,hTq]⟩
  · intro T hT S hS he
    apply Subtype.ext
    have hT' : T.val\I ∪ I=T.val := sdiff_union_of_subset T.property.1
    have hS' : S.val\I ∪ I=S.val := sdiff_union_of_subset S.property.1
    rw [← hT',he,hS']
  · intro S hS
    obtain ⟨hSU,hSc⟩ := mem_powersetCard.mp hS
    have hdis : Disjoint S I := by
      apply disjoint_left.mpr
      intro a ha hi
      exact (mem_sdiff.mp (hSU ha)).2 hi
    have hcard : (S∪I).card=q := by rw [card_union_of_disjoint hdis,hSc]; omega
    refine ⟨⟨S∪I,subset_union_right,mem_powersetCard.mpr ⟨union_subset
      (fun a ha => (mem_sdiff.mp (hSU ha)).1) hIU,hcard⟩⟩,mem_univ _,?_⟩
    ext a
    simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨h | h,hnot⟩
      · exact h
      · exact False.elim (hnot h)
    · intro ha
      exact ⟨Or.inl ha,fun hi=>disjoint_left.mp hdis ha hi⟩

end LooseHamilton
