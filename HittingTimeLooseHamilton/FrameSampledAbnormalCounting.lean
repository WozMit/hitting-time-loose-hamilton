module

public import HittingTimeLooseHamilton.FrameSampledAbnormalDefinitions
public import HittingTimeLooseHamilton.FrameRemainderParameters
public import HittingTimeLooseHamilton.FrameEntropyBridgeExisting

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame
local instance sampledAbnormalCountingPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {N r : ℕ} {original : Finset (Finset (Fin N))}

/-- All legal roles whose edges belong to the actual sampling host. -/
@[expose] def sampleableRoles (f : Frame r original) (D : Finset (Fin N))
    (H : SimpleHypergraph (Fin N)) : Finset (Finset (Fin N) × Fin N × Fin N) := by
  classical
  exact f.candidates.filter (fun c => c.1 ∪ {c.2.1,c.2.2} ∈ unexposed f D H)

/-- Moving the common main indicator inside a finite role count is exact. -/
theorem mainSampledBadCount_eq (f : Frame r original) (D : Finset (Fin N))
    (H T : SimpleHypergraph (Fin N)) (hT : T ⊆ unexposed f D H) :
    mainSampledBadCount f D H T =
      (((sampleableRoles f D H).filter (fun a => a.1 ∪ {a.2.1,a.2.2} ∈ T ∧
        (MainCountSurvives f D H T ∧
          FrameScales.alpha N/4 < |frameNormalizedCount f (rawRemainder f D H T) a-1|))).card:ℝ) := by
  classical
  unfold mainSampledBadCount
  split_ifs with hmain
  · congr 2
    ext a
    simp only [sampledBadRoles, sampleableRoles, mem_filter]
    constructor
    · rintro ⟨ha,he,hbad⟩
      exact ⟨⟨ha,hT he⟩,he,hmain,hbad⟩
    · rintro ⟨⟨ha,_⟩,he,_,hbad⟩
      exact ⟨ha,he,hbad⟩
  · simp [hmain]

/-- Source abnormality among sampleable roles is included in the already
formalised raw-host entropy exceptional set. -/
theorem sampleable_sourceBad_subset (f : Frame r original) (D : Finset (Fin N))
    (H : SimpleHypergraph (Fin N)) (t : ℝ) :
    (sampleableRoles f D H).filter (fun a => t < |frameNormalizedCount f H a-1|) ⊆
      f.existingExceptional H t := by
  classical
  intro a ha
  obtain ⟨ha,hbad⟩ := mem_filter.mp ha
  obtain ⟨ha,he⟩ := mem_filter.mp ha
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨ha,?_⟩,hbad⟩
  exact batch_subset_raw f D H (unexposed f D H) (Subset.refl _) he

end LooseHamilton.CandidateBalance
