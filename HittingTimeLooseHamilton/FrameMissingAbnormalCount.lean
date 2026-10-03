module

public import HittingTimeLooseHamilton.FrameMissingAbnormalEdges

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameScales
attribute [local instance] Classical.propDecidable
variable {N r : ℕ} {original : Finset (Finset (Fin N))}

/-- Every persisting abnormal role is either an existing exceptional role or
belongs to a missing abnormal edge. Each missing edge supports at most
r(r-1) ordered roles. -/
theorem persisting_card_le_existing_add_missing (f : Frame r original) (hr : 2≤r)
    (D : Finset (Fin N)) (H T : SimpleHypergraph (Fin N)) (hα : 0≤alpha N) :
    (persistingAbnormalCandidates f D H T).card ≤
      (f.existingExceptional (rawRemainder f D H T) (alpha N/4)).card+
        (missingAbnormalEdges f D (rawRemainder f D H T)).card*(r*(r-1)) := by
  let G := rawRemainder f D H T
  have hsub : persistingAbnormalCandidates f D H T ⊆
      f.existingExceptional G (alpha N/4) ∪
        (missingAbnormalEdges f D G).biUnion Frame.edgeCandidates := by
    intro a ha
    obtain ⟨hac,hD,_,habad⟩ := mem_filter.mp ha
    have hlegal : f.LegalCandidate a := by simpa [Frame.candidates] using hac
    obtain ⟨e,he,hae⟩ := (f.legalCandidate_iff hr a).mp hlegal
    have hea : a.1∪{a.2.1,a.2.2}=e := by
      obtain ⟨p,hp,hpa⟩ := mem_image.mp hae
      rw [←hpa]
      exact Frame.candidate_union_of_role hp
    have hbad : alpha N/4 < |frameNormalizedCount f G a-1| := by
      dsimp [G]
      linarith
    by_cases hg : e∈G
    · apply mem_union_left
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨hac,?_⟩,hbad⟩
      rw [hea]
      exact mem_filter.mpr ⟨mem_inter.mpr ⟨hg,hea ▸ hlegal.2.2⟩,hea ▸ hlegal.2.1⟩
    · apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨e,mem_filter.mpr ⟨he,?_,hg,⟨a,hae,hbad⟩⟩,hae⟩
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hea ▸ hlegal.2.2,hea ▸ hlegal.2.1⟩,hea ▸ hD⟩
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  have he : ((missingAbnormalEdges f D G).biUnion Frame.edgeCandidates).card =
      (missingAbnormalEdges f D G).card*(r*(r-1)) :=
    Frame.edgeCandidates_biUnion_card _ (fun e he =>
      (mem_powersetCard.mp (mem_filter.mp (mem_filter.mp he).1).1).2)
  rwa [he] at hh

/-- Finite density bridge, retaining the all-legal-candidate denominator. -/
theorem missingAbnormalEdges_card_lower (f : Frame r original) (hr : 2≤r)
    (D : Finset (Fin N)) (H T : SimpleHypergraph (Fin N)) (hα : 0≤alpha N)
    (hp : alpha N/2*f.candidates.card≤(persistingAbnormalCandidates f D H T).card)
    (he : ((f.existingExceptional (rawRemainder f D H T) (alpha N/4)).card:ℝ)≤
      alpha N/4*f.candidates.card)
    (hlegal : (f.n.choose r:ℝ)*(r*(r-1):ℕ)/2≤f.candidates.card) :
    alpha N*(f.n.choose r:ℝ)/8≤(missingAbnormalEdges f D (rawRemainder f D H T)).card := by
  have hc := persisting_card_le_existing_add_missing f hr D H T hα
  have hcR : ((persistingAbnormalCandidates f D H T).card:ℝ)≤
      (f.existingExceptional (rawRemainder f D H T) (alpha N/4)).card+
        (missingAbnormalEdges f D (rawRemainder f D H T)).card*(r*(r-1):ℕ) := by
    exact_mod_cast hc
  have hrpos : (0:ℝ)<(r*(r-1):ℕ) := by exact_mod_cast (Nat.mul_pos (by omega : 0<r) (by omega : 0<r-1))
  have hl := mul_le_mul_of_nonneg_left hlegal (show 0≤alpha N/4 by positivity)
  apply (mul_le_mul_iff_left₀ hrpos).mp
  nlinarith

/-- The ambient reverse sampling pool has at most binom(n_f,r) edges; hence
the cardinal lower bound gives the required alpha/8 density. -/
theorem missingAbnormalEdges_density (f : Frame r original) (D : Finset (Fin N))
    (H F : SimpleHypergraph (Fin N)) (hα : 0≤alpha N)
    (hcard : alpha N*(f.n.choose r:ℝ)/8≤
      (missingAbnormalEdges f D (F∪fixedAllowed f D H)).card) :
    missingAbnormalEdges f D (F∪fixedAllowed f D H)⊆samplingUniverse f D\F ∧
      alpha N/8*((samplingUniverse f D\F).card:ℝ)≤
        (missingAbnormalEdges f D (F∪fixedAllowed f D H)).card := by
  refine ⟨missingAbnormalEdges_subset_restored f D H F,?_⟩
  have hc : (samplingUniverse f D\F).card≤f.n.choose r :=
    (card_le_card sdiff_subset).trans (samplingUniverse_card_le f D)
  have hcR : ((samplingUniverse f D\F).card:ℝ)≤f.n.choose r := by exact_mod_cast hc
  have hh := mul_le_mul_of_nonneg_left hcR (show 0≤alpha N/8 by positivity)
  nlinarith
/-- A nonempty actual cycle family makes the reference binomial count positive. -/
lemma frame_choose_pos_of_cycles (f : Frame r original) (hr : 3≤r)
    (H : SimpleHypergraph (Fin N)) (hX : (f.cycleFamily H).Nonempty) :
    0<f.n.choose r := by
  apply Nat.choose_pos
  have hn := f.vertex_identity hr hX
  have hk := f.k_pos hr hX
  have hs : 0<f.s := f.markers_nonempty.card_pos
  have hm := Nat.mul_le_mul_left (r-1) hk
  nlinarith [show r-1+1=r by omega]

/-- Positive abnormal-edge density, including positivity of the reverse pool. -/
theorem missingAbnormalEdges_density_positive (f : Frame r original)
    (D : Finset (Fin N)) (H F : SimpleHypergraph (Fin N))
    (hα : 0<alpha N) (hn : 0<f.n.choose r)
    (hcard : alpha N*(f.n.choose r:ℝ)/8≤
      (missingAbnormalEdges f D (F∪fixedAllowed f D H)).card) :
    missingAbnormalEdges f D (F∪fixedAllowed f D H)⊆samplingUniverse f D\F ∧
    0<(samplingUniverse f D\F).card ∧
    alpha N/8≤((missingAbnormalEdges f D (F∪fixedAllowed f D H)).card:ℝ)/
      (samplingUniverse f D\F).card := by
  obtain ⟨hs,hd⟩ := missingAbnormalEdges_density f D H F hα.le hcard
  have hB : (0:ℝ)<(missingAbnormalEdges f D (F∪fixedAllowed f D H)).card :=
    (by positivity : (0:ℝ)<alpha N*(f.n.choose r:ℝ)/8).trans_le hcard
  have hpool : 0<(samplingUniverse f D\F).card :=
    (Nat.cast_pos.mp hB).trans_le (card_le_card hs)
  exact ⟨hs,hpool,(le_div_iff₀ (by exact_mod_cast hpool)).mpr hd⟩
end LooseHamilton.CandidateBalance
