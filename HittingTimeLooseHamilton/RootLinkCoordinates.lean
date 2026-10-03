module

public import HittingTimeLooseHamilton.RootLinkModels

public section

/-! Root-edge coordinates are exactly the (r-1)-subset link universe. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] lemma mem_rootEdgeUniverse (r : ℕ) (y : V) (e : Finset V) :
    e∈rootEdgeUniverse r y ↔ e.card=r ∧ y∈e := by simp [rootEdgeUniverse]

/-- Erasing the root is a bijection from present-root r-edges to (r-1)-sets avoiding it. -/
@[expose] def rootEdgeLinkEquiv (r : ℕ) (hr : 1 ≤ r) (y : V) :
    ↥(rootEdgeUniverse r y) ≃ ↥((univ.erase y).powersetCard (r-1)) where
  toFun e := ⟨e.val.erase y,mem_powersetCard.mpr ⟨by
      intro v hv
      exact mem_erase.mpr ⟨(mem_erase.mp hv).1,mem_univ _⟩,by
      rw [card_erase_of_mem ((mem_rootEdgeUniverse r y e.val).mp e.property).2,
        ((mem_rootEdgeUniverse r y e.val).mp e.property).1]⟩⟩
  invFun s := ⟨insert y s.val,(mem_rootEdgeUniverse r y _).mpr ⟨by
      have hy : y∉s.val := by intro hy; exact notMem_erase y univ ((mem_powersetCard.mp s.property).1 hy)
      rw [card_insert_of_notMem hy,(mem_powersetCard.mp s.property).2]
      omega,mem_insert_self _ _⟩⟩
  left_inv e := by
    apply Subtype.ext
    exact insert_erase ((mem_rootEdgeUniverse r y e.val).mp e.property).2
  right_inv s := by
    apply Subtype.ext
    apply erase_insert
    intro hy
    exact notMem_erase y univ ((mem_powersetCard.mp s.property).1 hy)

lemma rootEdgeUniverse_card (r : ℕ) (hr : 1 ≤ r) (y : V) :
    (rootEdgeUniverse r y).card=(Fintype.card V-1).choose (r-1) := by
  have h := Fintype.card_congr (rootEdgeLinkEquiv r hr y)
  simpa only [Fintype.card_coe,card_powersetCard,card_erase_of_mem (mem_univ y),card_univ] using h

/-- Setwise root erasure used to interpret a sampled root-edge set as an actual link. -/
@[expose] def rootLinkErase (y : V) (F : SimpleHypergraph V) : SimpleHypergraph V :=
  F.image (fun e=>e.erase y)

lemma rootLinkErase_card (r : ℕ) (y : V) (F : SimpleHypergraph V)
    (hF : F ⊆ rootEdgeUniverse r y) : (rootLinkErase y F).card=F.card := by
  apply card_image_iff.mpr
  intro e he f hf hef
  have he' := ((mem_rootEdgeUniverse r y e).mp (hF he)).2
  have hf' := ((mem_rootEdgeUniverse r y f).mp (hF hf)).2
  have hh := congrArg (fun s : Finset V=>insert y s) hef
  simpa only [insert_erase he',insert_erase hf'] using hh

lemma rootLinkErase_subset_universe (r : ℕ) (hr : 1 ≤ r) (y : V)
    (F : SimpleHypergraph V) (hF : F ⊆ rootEdgeUniverse r y) :
    rootLinkErase y F ⊆ (univ.erase y).powersetCard (r-1) := by
  intro s hs
  obtain ⟨e,he,rfl⟩ := mem_image.mp hs
  exact (rootEdgeLinkEquiv r hr y ⟨e,hF he⟩).property
end LooseHamilton
