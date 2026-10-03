module

public import HittingTimeLooseHamilton.PrivateBadRootCounting
public import HittingTimeLooseHamilton.AuxiliaryFrameCycles

public section

/-! Structural private-move splits give actual legal candidates in the source
frame. The target avoids original ports; the original prohibition stays fixed. -/
noncomputable section
namespace LooseHamilton
open Finset AuxiliaryFrame
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem PrivateRootSplitLegal.frame_candidate {r : ℕ} (hr : 3 ≤ r)
    {markers original : SimpleHypergraph V} {S q A R : Finset V} {x t u v : V}
    (h : PrivateRootSplitLegal r markers (allowedEdges r (originalPorts original))
      S q x t A R {u,v})
    (f : Frame r original)
    (hactive : f.active = univ \ insert x S) (hmarkers : f.markers = insert q markers)
    (htports : t ∉ originalPorts original) :
    f.LegalCandidate (insert t R,u,v) := by
  have htR : t ∉ R := by
    intro ht
    exact disjoint_left.mp h.split_legal.forbidden_disjoint
      (mem_union_right _ (mem_insert_of_mem ht)) (mem_union_left _ (mem_insert_self _ _))
  have htS : t ∉ S := by
    intro ht
    have hp := h.target_legal.private_card
    rw [insert_eq_of_mem ht, h.rest_card] at hp
    omega
  have htx : t ≠ x := by
    intro he
    exact disjoint_left.mp h.split_legal.forbidden_disjoint
      (mem_union_right _ (mem_insert_self _ _))
      (mem_union_left _ (by simp [he]))
  have htuv : t ∉ ({u,v} : Finset V) := by
    intro hh
    exact disjoint_left.mp h.split_legal.forbidden_disjoint
      (mem_union_left _ hh) (mem_union_left _ (mem_insert_self _ _))
  have htmark : t ∉ originalPorts (insert q markers) := by
    intro ht
    obtain ⟨m,hm,htm⟩ := mem_biUnion.mp ht
    have hh := h.target_legal.augmented_subset_active m hm htm
    exact (mem_sdiff.mp hh).2 (mem_insert_self _ _)
  have hRuv : Disjoint R {u,v} := h.split_legal.private_pair_disjoint.mono (subset_insert x R) subset_rfl
  have hnewdis : Disjoint (insert t R) {u,v} := by
    exact disjoint_insert_left.mpr ⟨htuv,hRuv⟩
  have hpc : (insert t R).card = r-2 := by
    rw [card_insert_of_notMem htR, h.split_legal.rest_card]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hmarkers]
    refine ⟨hpc,h.split_legal.pair_card,hnewdis,?_⟩
    apply disjoint_left.mpr
    intro w hw hm
    rcases mem_union.mp hw with hp | hp
    · rcases mem_insert.mp hp with rfl | hwR
      · exact htmark hm
      · exact disjoint_left.mp h.split_legal.forbidden_disjoint
          (mem_union_right _ (mem_insert_of_mem hwR)) (mem_union_right _ hm)
    · exact disjoint_left.mp h.split_legal.forbidden_disjoint
        (mem_union_left _ hp) (mem_union_right _ hm)
  · rw [hactive]
    intro w hw
    refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
    intro hdel
    rcases mem_insert.mp hdel with rfl | hwS
    · rcases mem_union.mp hw with hpriv | hpair
      · rcases mem_insert.mp hpriv with he | hR
        · exact htx he.symm
        · exact h.split_legal.x_not_mem_rest hR
      · exact disjoint_left.mp h.split_legal.private_pair_disjoint (mem_insert_self _ _) hpair
    · rcases mem_union.mp hw with hpriv | hpair
      · rcases mem_insert.mp hpriv with rfl | hR
        · exact htS hwS
        · exact disjoint_left.mp h.split_legal.forbidden_disjoint
            (mem_union_right _ (mem_insert_of_mem hR))
            (mem_union_left _ (mem_insert_of_mem hwS))
      · exact disjoint_left.mp h.split_legal.forbidden_disjoint
          (mem_union_left _ hpair) (mem_union_left _ (mem_insert_of_mem hwS))
  · apply (mem_allowedEdges _ _ _).mpr
    constructor
    · rw [card_union_of_disjoint hnewdis,hpc,h.split_legal.pair_card]; omega
    · have hsub : R ∪ {u,v} ⊆ insert x A := by
        rw [← mem_singleton.mp h.split_legal.edge_mem]
        intro w hw
        rcases mem_union.mp hw with hR | hp
        · exact mem_union_right _ (mem_insert_of_mem hR)
        · exact mem_union_left _ hp
      have he : (insert t R ∪ {u,v}) ∩ originalPorts original =
          (R ∪ {u,v}) ∩ originalPorts original := by
        ext w
        simp only [mem_inter, mem_union, mem_insert]
        constructor
        · rintro ⟨(⟨rfl⟩ | hR) | hp, hport⟩
          · exact False.elim (htports hport)
          · exact ⟨Or.inl hR,hport⟩
          · exact ⟨Or.inr hp,hport⟩
        · rintro ⟨hR | hp,hport⟩
          · exact ⟨Or.inl (Or.inr hR),hport⟩
          · exact ⟨Or.inr hp,hport⟩
      rw [he]
      exact (card_le_card (inter_subset_inter_right hsub)).trans
        ((mem_allowedEdges _ _ _).mp h.edge_allowed).2

end LooseHamilton
