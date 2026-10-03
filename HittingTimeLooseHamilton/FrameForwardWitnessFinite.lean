module

public import HittingTimeLooseHamilton.FrameForwardWitnessDefinitions
public import HittingTimeLooseHamilton.FrameMissingAbnormalCount
public import HittingTimeLooseHamilton.FrameMissingAbnormalSampled
public import HittingTimeLooseHamilton.FrameForwardExposure

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameScales FrameSurvival
variable {N r : ℕ} {original : Finset (Finset (Fin N))}

/-- The deterministic forward witness uses actual counts on the raw remainder.
The eventual theorem discharges the existing-role and legal-count bounds. -/
theorem forwardWitness_of_good_counts (f : Frame r original) (hr : 3 ≤ r)
    (D : Finset (Fin N)) (S : SimpleHypergraph (Fin N)) (ell : Fin N → ℕ)
    (H : SimpleHypergraph (Fin N))
    (T : HostBatch (unexposed f D H) (batchSize f D H))
    (ht : 1 ≤ batchSize f D H) (hα : 0 ≤ alpha N)
    (hlegal : (f.n.choose r:ℝ)*(r*(r-1):ℕ)/2 ≤ f.candidates.card)
    (hexisting : ((f.existingExceptional (rawRemainder f D H T.val) (alpha N/4)).card:ℝ) ≤
      alpha N*(f.candidates.card:ℝ)/4)
    (hterminal : BatchRetainsLower S ell T.val)
    (hpersist : alpha N/2*f.candidates.card ≤ (persistingAbnormalCandidates f D H T.val).card)
    (hroles : ((sampledBadRoles f D H T.val).card:ℝ) ≤ (alpha N)^2*batchSize f D H) :
    ForwardWitnessSuccess f D S ell H T.val := by
  have hcard := missingAbnormalEdges_card_lower f (by omega) D H T.val hα hpersist
    (by nlinarith only [hexisting]) hlegal
  have hdensity := missingAbnormalEdges_density f D H (unexposed f D H \ T.val) hα hcard
  have hT := (mem_powersetCard.mp T.property)
  have hsub := removed_subset_record_reverse f D H T.val hT.1
  have hpositive : 0 < (samplingUniverse f D \ (unexposed f D H \ T.val)).card := by
    have hc := card_le_card hsub
    rw [hT.2] at hc
    omega
  exact ⟨hterminal,hdensity.1,hpositive,hdensity.2,
    sampled_missingAbnormal_small f D H T.val (by omega) (batchSize f D H) hroles⟩

end LooseHamilton.CandidateBalance
