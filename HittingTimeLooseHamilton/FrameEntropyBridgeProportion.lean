module

public import HittingTimeLooseHamilton.FrameEntropyBridgeExceptional
public import HittingTimeLooseHamilton.FrameEntropyBridgePorts

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
open scoped BigOperators
local instance : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- The exceptional entropy roles count exactly the strict abnormal existing
candidate triples of the frame, with the actual completion counts. -/
theorem entropyInstance_exceptionalRoles (F : Frame r original) (hr : 3 ≤ r)
    (H : Finset (Finset V)) (hX : (F.cycleFamily H).Nonempty) (t : ℝ) :
    (F.entropyInstance H hX).exceptionalRoles t = (F.existingExceptional H t).card := by
  unfold BiasedRoleInstance.exceptionalRoles existingExceptional
  rw [F.entropyInstance_eligibleEdges H hX,
    F.existingCandidates_filter_card (by omega) H]
  refine (F.sum_numberedEdges (F.existingCandidateEdges H)
    (fun e he => (mem_filter.mp (mem_filter.mp he).1).2)
    (fun e => (e.offDiag.filter (fun uv => t*(F.entropyInstance H hX).roleReference <
      |(F.entropyInstance H hX).roleProbability e uv-(F.entropyInstance H hX).roleReference|)).card)).trans ?_
  apply sum_congr rfl
  intro e he
  refine (F.numberedEdge_offDiag_filter_card e
    (mem_filter.mp (mem_filter.mp he).1).2
    (fun uv => t*(F.entropyInstance H hX).roleReference <
      |(F.entropyInstance H hX).roleProbability (F.numberedEdge e) uv -
        (F.entropyInstance H hX).roleReference|)).trans ?_
  congr 1
  apply filter_congr
  intro uv huv
  exact F.entropyInstance_exceptional_role_iff hr H hX e he uv huv t

/-- The denominator is the exact number of existing legal ordered roles. -/
theorem entropyInstance_eligibleRoles (F : Frame r original) (hr : 3 ≤ r)
    (H : Finset (Finset V)) (hX : (F.cycleFamily H).Nonempty) :
    (F.entropyInstance H hX).eligibleRoles = (F.existingCandidates H).card := by
  rw [(F.entropyInstance H hX).eligibleRoles_eq,F.entropyInstance_eligibleEdges H hX]
  change (F.numberedEdges (F.existingCandidateEdges H)).card * (r*(r-1)) = _
  rw [F.numberedEdges_card (F.existingCandidateEdges H) (fun e he => (mem_filter.mp (mem_filter.mp he).1).2),
    F.existingCandidates_card (by omega) H]

/-- Exact transport to the native frame count fraction, before applying any
asymptotic bound. This is not an assumed role identity. -/
theorem entropyInstance_exceptionalProportion (F : Frame r original) (hr : 3 ≤ r)
    (H : Finset (Finset V)) (hX : (F.cycleFamily H).Nonempty) (t : ℝ) :
    (F.entropyInstance H hX).exceptionalProportion t = F.existingExceptionalProportion H t := by
  unfold BiasedRoleInstance.exceptionalProportion existingExceptionalProportion
  rw [F.entropyInstance_exceptionalRoles hr H hX t,F.entropyInstance_eligibleRoles hr H hX]

end LooseHamilton.AuxiliaryFrame.Frame
