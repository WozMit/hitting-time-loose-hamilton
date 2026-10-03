module

public import HittingTimeLooseHamilton.FrameCandidatePersistenceUniform
public import HittingTimeLooseHamilton.FrameEntropyBridgeExisting

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameScales
attribute [local instance] Classical.propDecidable
variable {N r : ℕ} {original : Finset (Finset (Fin N))}

/-- Missing edges with a remainder-abnormal ordered role. This definition
uses only the frame, boundary and remainder G, never the removed batch or
source host. In particular it is fixed after conditioning on the remainder. -/
@[expose] def missingAbnormalEdges (f : Frame r original) (D : Finset (Fin N))
    (G : SimpleHypergraph (Fin N)) : SimpleHypergraph (Fin N) :=
  f.candidateEdges.filter (fun e => e∈samplingUniverse f D ∧ e∉G ∧
    ∃ a∈Frame.edgeCandidates e, alpha N/4 < |frameNormalizedCount f G a-1|)

lemma missingAbnormalEdges_subset (f : Frame r original) (D : Finset (Fin N))
    (G : SimpleHypergraph (Fin N)) :
    missingAbnormalEdges f D G ⊆ samplingUniverse f D \ G := by
  intro e he
  exact mem_sdiff.mpr ⟨(mem_filter.mp he).2.1,(mem_filter.mp he).2.2.1⟩

/-- Restoring the fixed exposed edges does not change which unexposed edges
are missing. The abnormality test is nevertheless always evaluated in G. -/
lemma missingAbnormalEdges_restored (f : Frame r original) (D : Finset (Fin N))
    (H F : SimpleHypergraph (Fin N)) :
    missingAbnormalEdges f D (F∪fixedAllowed f D H) =
      f.candidateEdges.filter (fun e => e∈samplingUniverse f D ∧ e∉F ∧
        ∃ a∈Frame.edgeCandidates e,
          alpha N/4 < |frameNormalizedCount f (F∪fixedAllowed f D H) a-1|) := by
  ext e
  simp only [missingAbnormalEdges,mem_filter]
  have hex : e∈samplingUniverse f D → e∉fixedAllowed f D H := by
    intro he hh
    exact (mem_sdiff.mp (mem_inter.mp hh).1).2 he
  simp only [mem_union,not_or]
  tauto

lemma missingAbnormalEdges_subset_restored (f : Frame r original) (D : Finset (Fin N))
    (H F : SimpleHypergraph (Fin N)) :
    missingAbnormalEdges f D (F∪fixedAllowed f D H) ⊆ samplingUniverse f D \ F := by
  intro e he
  rw [missingAbnormalEdges_restored] at he
  exact mem_sdiff.mpr ⟨(mem_filter.mp he).2.1,(mem_filter.mp he).2.2.1⟩

lemma samplingUniverse_card_le (f : Frame r original) (D : Finset (Fin N)) :
    (samplingUniverse f D).card≤f.n.choose r := by
  have hs : samplingUniverse f D⊆f.active.powersetCard r := by
    intro e he
    obtain ⟨he,hD⟩ := mem_filter.mp he
    obtain ⟨he,ha⟩ := mem_filter.mp he
    have hc := ((mem_allowedEdges _ _ _).mp he).1
    exact mem_powersetCard.mpr ⟨ha,hc⟩
  have hh := card_le_card hs
  simpa only [card_powersetCard,Frame.n] using hh

/-- The definition is literally remainder-measurable: identical restored
remainders produce identical missing abnormal-edge sets. -/
lemma missingAbnormalEdges_remainder_congr (f : Frame r original) (D : Finset (Fin N))
    (G G' : SimpleHypergraph (Fin N)) (h : G=G') :
    missingAbnormalEdges f D G=missingAbnormalEdges f D G' := congrArg _ h
end LooseHamilton.CandidateBalance
