module

public import HittingTimeLooseHamilton.FrameEntropyBridgeNumbering

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
open scoped BigOperators
local instance : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- The entropy test on an existing numbered edge is precisely the printed
strict candidate-count test, with no surrogate cycle/completion variables. -/
theorem entropyInstance_exceptional_role_iff (F : Frame r original) (hr : 3 ≤ r)
    (H : Finset (Finset V)) (hX : (F.cycleFamily H).Nonempty)
    (e : Finset V) (he : e ∈ F.existingCandidateEdges H)
    (uv : V × V) (huv : uv ∈ e.offDiag) (t : ℝ) :
    let D := F.entropyInstance H hX
    t*D.roleReference < |D.roleProbability (F.numberedEdge e)
      (F.numberVertex uv.1,F.numberVertex uv.2)-D.roleReference| ↔
    t < |(F.completionCount H (e \ {uv.1,uv.2},uv):ℝ) /
      ((F.cycleCount H:ℝ)/(((r:ℝ)-1)^2*F.mu H))-1| := by
  dsimp only
  refine ((F.entropyInstance H hX).exceptional_role_iff_relative hr t
    (F.numberedEdge e) (F.numberVertex uv.1,F.numberVertex uv.2)).trans ?_
  let c : Finset V × V × V := (e \ {uv.1,uv.2},uv)
  have hlegal : F.LegalCandidate c := (F.legalCandidate_iff (by omega) c).mpr
    ⟨e,F.existingCandidateEdges_subset H he,mem_image_of_mem _ huv⟩
  have hed : e ∈ F.rawHost H := (mem_filter.mp he).1
  have hactive : e ⊆ F.active := (mem_filter.mp hed).2
  have hu : uv.1 ∈ F.active := hactive (mem_offDiag.mp huv).1
  have hv : uv.2 ∈ F.active := hactive (mem_offDiag.mp huv).2.1
  have hprob := F.numberedCycleLaw_role hr H hX hlegal
    (by simpa only [c,candidate_union_of_role huv] using hed)
    ⟨uv.1,hu⟩ ⟨uv.2,hv⟩ rfl rfl
  simp only [c,candidate_union_of_role huv] at hprob
  have hp : (F.entropyInstance H hX).roleProbability (F.numberedEdge e)
      (F.numberVertex uv.1,F.numberVertex uv.2) =
      (F.completionCount H (e \ {uv.1,uv.2},uv):ℝ)/F.cycleCount H := by
    change directedRoleProbability r (F.numberedEdges F.markers)
      (F.numberedEdges (F.rawHost H)) F.numberedRoot F.numberedInitial
      (F.numberedCycleLaw H hX) (F.numberedEdge e) (F.numberVertex uv.1)
      (F.numberVertex uv.2) = _
    rw [F.numberVertex_of_mem hu, F.numberVertex_of_mem hv]
    exact hprob
  rw [hp]
  unfold BiasedRoleInstance.roleReference
  rw [F.entropyInstance_mu]
  simp only [div_eq_mul_inv,inv_div,inv_mul_eq_iff_eq_mul,inv_one,mul_one,inv_inv]
  ring_nf

end LooseHamilton.AuxiliaryFrame.Frame
