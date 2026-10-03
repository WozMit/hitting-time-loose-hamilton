module

public import HittingTimeLooseHamilton.FrameCandidateInstability
public import HittingTimeLooseHamilton.FrameCandidateCounts

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameScales
attribute [local instance] Classical.propDecidable
variable {N r : ℕ} {original : Finset (Finset (Fin N))}

/-- Actual candidates that stay abnormal, away from the fixed boundary.
The denominator of their fraction remains the full legal candidate set. -/
@[expose] def persistingAbnormalCandidates (f : Frame r original) (D : Finset (Fin N))
    (H T : SimpleHypergraph (Fin N)) : Finset (Finset (Fin N) × Fin N × Fin N) :=
  f.candidates.filter (fun a => Disjoint (a.1∪{a.2.1,a.2.2}) D ∧
    alpha N < |frameNormalizedCount f H a-1| ∧
    alpha N/2 < |frameNormalizedCount f (rawRemainder f D H T) a-1|)

/-- Finite counting removes only boundary candidates and unstable large ones.
Tiny completions are retained through their deterministic abnormality bound. -/
theorem persisting_candidates_card (f : Frame r original) (D : Finset (Fin N))
    (H T : SimpleHypergraph (Fin N)) (hα : 0≤alpha N) (hαsmall : alpha N≤1/4)
    (hbad : f.candidateBad H (alpha N))
    (hboundary : ((f.boundaryCandidates D).card:ℝ)≤alpha N/4*f.candidates.card)
    (hunstable : largeCompletionUnstableFraction f D H T≤(alpha N)^2)
    (htransfer : ∀a∈f.candidates, ¬LargeCompletionUnstable f D H a T →
      alpha N < |frameNormalizedCount f H a-1| →
      alpha N/2 < |frameNormalizedCount f (rawRemainder f D H T) a-1|) :
    alpha N/2*f.candidates.card≤(persistingAbnormalCandidates f D H T).card := by
  classical
  let bad := f.candidates.filter (fun a => alpha N < |frameNormalizedCount f H a-1|)
  let unstable := f.candidates.filter (fun a => LargeCompletionUnstable f D H a T)
  have hbad' : alpha N*(f.candidates.card:ℝ)<bad.card := hbad
  have hpos : 0<(f.candidates.card:ℝ) := by
    have hbsub : bad.card≤f.candidates.card := card_le_card (filter_subset _ _)
    have hbsubR : (bad.card:ℝ)≤f.candidates.card := by exact_mod_cast hbsub
    have : (0:ℝ)≤f.candidates.card := Nat.cast_nonneg _
    nlinarith
  have hu : (unstable.card:ℝ)≤(alpha N)^2*f.candidates.card :=
    (div_le_iff₀ hpos).mp hunstable
  have hsub : bad ⊆ persistingAbnormalCandidates f D H T ∪
      (f.boundaryCandidates D ∪ unstable) := by
    intro a ha
    obtain ⟨hac,habad⟩ := mem_filter.mp ha
    by_cases hb : Disjoint (a.1∪{a.2.1,a.2.2}) D
    · by_cases hu : LargeCompletionUnstable f D H a T
      · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hac,hu⟩))
      · exact mem_union_left _ (mem_filter.mpr ⟨hac,hb,habad,htransfer a hac hu habad⟩)
    · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hac,hb⟩))
  have hcount := (card_le_card hsub).trans (card_union_le _ _)
  have hcount2 := card_union_le (f.boundaryCandidates D) unstable
  have hsum : (bad.card:ℝ)≤(persistingAbnormalCandidates f D H T).card+
      (f.boundaryCandidates D).card+unstable.card := by exact_mod_cast (by omega :
        bad.card≤(persistingAbnormalCandidates f D H T).card+(f.boundaryCandidates D).card+unstable.card)
  have hαsq : (alpha N)^2≤alpha N/4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hαsq hpos.le
  nlinarith
end LooseHamilton.CandidateBalance
