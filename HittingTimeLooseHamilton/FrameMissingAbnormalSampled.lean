module

public import HittingTimeLooseHamilton.FrameMissingAbnormalEdges
public import HittingTimeLooseHamilton.FrameSampledAbnormalMarkov

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival
variable {N r : ℕ} {original : Finset (Finset (Fin N))}

/-- Each sampled missing abnormal edge is witnessed by a sampled abnormal role.
The missing-edge selector itself uses only the remainder, never the batch. -/
theorem sampled_missingAbnormal_subset (f : Frame r original) (D : Finset (Fin N))
    (H T : SimpleHypergraph (Fin N)) (hr : 2 ≤ r) :
    T ∩ missingAbnormalEdges f D (rawRemainder f D H T) ⊆ sampledBadEdges f D H T := by
  classical
  intro e he
  obtain ⟨heT,heB⟩ := mem_inter.mp he
  obtain ⟨hec,_,_,a,ha,hbad⟩ := mem_filter.mp heB
  have hal : f.LegalCandidate a := (f.legalCandidate_iff hr a).mpr ⟨e,hec,ha⟩
  have hae : a.1 ∪ {a.2.1,a.2.2} = e := by
    obtain ⟨p,hp,rfl⟩ := mem_image.mp ha
    exact Frame.candidate_union_of_role hp
  apply mem_image.mpr
  refine ⟨a,?_,hae⟩
  apply mem_filter.mpr
  refine ⟨?_,?_,hbad⟩
  · simpa only [Frame.candidates,mem_filter,mem_univ,true_and] using hal
  · simpa only [hae] using heT

/-- Role counting controls the forward witness's sampled intersection. -/
theorem sampled_missingAbnormal_card_le (f : Frame r original) (D : Finset (Fin N))
    (H T : SimpleHypergraph (Fin N)) (hr : 2 ≤ r) :
    (T ∩ missingAbnormalEdges f D (rawRemainder f D H T)).card ≤
      (sampledBadRoles f D H T).card :=
  (card_le_card (sampled_missingAbnormal_subset f D H T hr)).trans
    (sampledBadEdges_card_le f D H T)

/-- The deterministic sampled-role threshold implies the missing-edge
intersection threshold used by reverse sampling. -/
theorem sampled_missingAbnormal_small (f : Frame r original) (D : Finset (Fin N))
    (H T : SimpleHypergraph (Fin N)) (hr : 2 ≤ r) (τ : ℕ)
    (hsmall : ((sampledBadRoles f D H T).card:ℝ) ≤ (FrameScales.alpha N)^2*τ) :
    ((T ∩ missingAbnormalEdges f D (rawRemainder f D H T)).card:ℝ) ≤
      (FrameScales.alpha N)^2*τ :=
  (Nat.cast_le.mpr (sampled_missingAbnormal_card_le f D H T hr)).trans hsmall

end LooseHamilton.CandidateBalance
