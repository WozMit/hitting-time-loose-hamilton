module

public import HittingTimeLooseHamilton.AuxiliaryFrameParameters
public import HittingTimeLooseHamilton.BiasedRoleModels

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- Underlying edges of legal candidates, with the original-port prohibition. -/
@[expose] def candidateEdges (F : Frame r original) : Finset (Finset V) :=
  (F.active.powersetCard r).filter (fun e =>
    Disjoint e (originalPorts F.markers) ∧ (e ∩ originalPorts original).card ≤ 1)

@[expose] def edgeCandidates (e : Finset V) : Finset (Finset V × V × V) :=
  e.offDiag.image (fun p => (e \ {p.1,p.2},p))

lemma candidate_union_of_role {e : Finset V} {p : V × V}
    (hp : p ∈ e.offDiag) : (e \ {p.1,p.2}) ∪ {p.1,p.2} = e := by
  apply sdiff_union_of_subset
  exact insert_subset_iff.mpr ⟨(mem_offDiag.mp hp).1, singleton_subset_iff.mpr (mem_offDiag.mp hp).2.1⟩

lemma edgeCandidates_card {e : Finset V} (he : e.card = r) :
    (edgeCandidates e).card = r*(r-1) := by
  rw [edgeCandidates, card_image_of_injective]
  · exact directedRole_card he
  · intro a b h
    exact congrArg Prod.snd h

lemma legalCandidate_iff (F : Frame r original) (hr : 2 ≤ r)
    (c : Finset V × V × V) :
    F.LegalCandidate c ↔ ∃ e ∈ F.candidateEdges, c ∈ edgeCandidates e := by
  constructor
  · intro h
    let e := c.1 ∪ {c.2.1,c.2.2}
    have he : e.card = r := by
      dsimp [e]
      rw [card_union_of_disjoint h.1.private_pair_disjoint,
        h.1.private_card,h.1.pair_card]
      omega
    refine ⟨e, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨h.2.1,he⟩,
      h.1.ports_disjoint,(mem_allowedEdges r _ _).mp h.2.2 |>.2⟩, ?_⟩
    have huv : c.2.1 ≠ c.2.2 := by
      intro hh
      have := h.1.pair_card
      simp [hh] at this
    apply mem_image.mpr
    refine ⟨c.2, mem_offDiag.mpr ⟨?_,?_,huv⟩, ?_⟩
    · exact mem_union_right _ (by simp)
    · exact mem_union_right _ (by simp)
    · have hp : e \ {c.2.1,c.2.2} = c.1 := by
        dsimp [e]
        rw [union_sdiff_cancel_right h.1.private_pair_disjoint]
      exact Prod.ext hp rfl
  · rintro ⟨e,he,hc⟩
    obtain ⟨hp,hdis,hallow⟩ := mem_filter.mp he
    obtain ⟨hes,her⟩ := mem_powersetCard.mp hp
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hc
    have hpair : {p.1,p.2} ⊆ e := insert_subset_iff.mpr
      ⟨(mem_offDiag.mp hp).1, singleton_subset_iff.mpr (mem_offDiag.mp hp).2.1⟩
    have hpc : ({p.1,p.2} : Finset V).card = 2 := by
      simp [(mem_offDiag.mp hp).2.2]
    have hu := candidate_union_of_role hp
    refine ⟨⟨?_,hpc,sdiff_disjoint,?_⟩,?_,?_⟩
    · rw [card_sdiff_of_subset hpair,her,hpc]
    · simpa only [hu] using hdis
    · simpa only [hu] using hes
    · rw [hu,mem_allowedEdges]
      exact ⟨her,hallow⟩

/-- Ordered roles on a uniform edge family are disjoint between distinct edges. -/
theorem edgeCandidates_biUnion_card (E : Finset (Finset V))
    (hE : ∀ e ∈ E, e.card = r) :
    (E.biUnion edgeCandidates).card = E.card * (r*(r-1)) := by
  rw [card_biUnion]
  · calc
      ∑ e ∈ E, (edgeCandidates e).card = ∑ _e ∈ E, r*(r-1) := by
        apply sum_congr rfl
        intro e he
        exact edgeCandidates_card (hE e he)
      _ = _ := by simp [Nat.mul_comm]
  · intro e he f hf hef
    apply disjoint_left.mpr
    intro c hc hd
    obtain ⟨p,hp,hp'⟩ := mem_image.mp hc
    obtain ⟨q,hq,hq'⟩ := mem_image.mp hd
    have h1 : c.1 ∪ {c.2.1,c.2.2} = e := by
      rw [← hp']; exact candidate_union_of_role hp
    have h2 : c.1 ∪ {c.2.1,c.2.2} = f := by
      rw [← hq']; exact candidate_union_of_role hq
    exact hef (h1.symm.trans h2)

/-- Exact count: each legal underlying edge contributes all ordered endpoint pairs. -/
theorem candidates_card (F : Frame r original) (hr : 2 ≤ r) :
    F.candidates.card = F.candidateEdges.card * (r*(r-1)) := by
  have heq : F.candidates = F.candidateEdges.biUnion edgeCandidates := by
    ext c
    simp only [candidates,mem_filter,mem_univ,true_and,mem_biUnion]
    exact F.legalCandidate_iff hr c
  rw [heq]
  exact edgeCandidates_biUnion_card _ (fun e he =>
    (mem_powersetCard.mp (mem_filter.mp he).1).2)

/-- Boundary incidence concerns the whole candidate edge, including both endpoints. -/
@[expose] def boundaryCandidates (F : Frame r original) (D : Finset V) :=
  F.candidates.filter (fun c => ¬ Disjoint (c.1 ∪ {c.2.1,c.2.2}) D)

theorem boundaryCandidates_card (F : Frame r original) (hr : 2 ≤ r) (D : Finset V) :
    (F.boundaryCandidates D).card =
      (F.candidateEdges.filter (fun e => ¬ Disjoint e D)).card * (r*(r-1)) := by
  have heq : F.boundaryCandidates D =
      (F.candidateEdges.filter (fun e => ¬ Disjoint e D)).biUnion edgeCandidates := by
    ext c
    simp only [boundaryCandidates,candidates,mem_filter,mem_univ,true_and,mem_biUnion]
    constructor
    · rintro ⟨hc,hD⟩
      obtain ⟨e,he,hc⟩ := (F.legalCandidate_iff hr c).mp hc
      obtain ⟨p,hp,hp'⟩ := mem_image.mp hc
      refine ⟨e,⟨he,?_⟩,mem_image.mpr ⟨p,hp,hp'⟩⟩
      simpa only [← hp',candidate_union_of_role hp] using hD
    · rintro ⟨e,⟨he,hD⟩,hc⟩
      refine ⟨(F.legalCandidate_iff hr c).mpr ⟨e,he,hc⟩,?_⟩
      obtain ⟨p,hp,hp'⟩ := mem_image.mp hc
      simpa only [← hp',candidate_union_of_role hp] using hD
  rw [heq]
  exact edgeCandidates_biUnion_card _ (fun e he =>
    (mem_powersetCard.mp (mem_filter.mp (mem_filter.mp he).1).1).2)
end LooseHamilton.AuxiliaryFrame.Frame
