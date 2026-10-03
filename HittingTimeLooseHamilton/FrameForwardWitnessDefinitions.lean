module

public import HittingTimeLooseHamilton.FrameMissingAbnormalEdges
public import HittingTimeLooseHamilton.NoDeficitModels

public section

/-! The pointwise forward witness, retaining both fixed terminal and fixed
allowed current edges after complement exposure. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameScales
variable {N r : ℕ} {original : Finset (Finset (Fin N))}

/-- The admissibility and witness facts needed by the restricted reverse count.
The terminal demand is checked on the original vertex set; the density is in
the unexposed reverse universe, while abnormality is evaluated in raw G. -/
@[expose] def ForwardWitnessSuccess (f : Frame r original) (D : Finset (Fin N))
    (S : SimpleHypergraph (Fin N)) (ell : Fin N → ℕ)
    (H T : SimpleHypergraph (Fin N)) : Prop :=
  let F := unexposed f D H \ T
  let G := rawRemainder f D H T
  let A := missingAbnormalEdges f D G
  BatchRetainsLower S ell T ∧
  A ⊆ samplingUniverse f D \ F ∧
  0 < (samplingUniverse f D \ F).card ∧
  alpha N/8*((samplingUniverse f D \ F).card:ℝ) ≤ A.card ∧
  ((T ∩ A).card:ℝ) ≤ (alpha N)^2*batchSize f D H

end LooseHamilton.CandidateBalance
