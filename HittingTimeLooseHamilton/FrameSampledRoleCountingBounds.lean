module

public import HittingTimeLooseHamilton.FrameSampledRoleCounting

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}
local instance sampledRoleBoundsPropDecidable : DecidablePred (fun p:Prop => p) := Classical.propDecidable

/-- All legal directed roles whose candidate edge belongs to the sampling host. -/
@[expose] def restrictedExistingCandidates (F : Frame r original) (U : SimpleHypergraph V) :=
  F.candidates.filter (fun c => c.1 ∪ {c.2.1,c.2.2} ∈ U)

lemma restrictedExistingCandidates_card_le (F : Frame r original) (hr : 2≤r)
    (H U : SimpleHypergraph V) (hU : U⊆F.rawHost H) :
    (F.restrictedExistingCandidates U).card ≤ U.card*(r*(r-1)) := by
  have hs : F.restrictedExistingCandidates U ⊆ U.biUnion edgeCandidates := by
    intro c hc
    obtain ⟨hc,he⟩ := mem_filter.mp hc
    obtain ⟨e,he',hce⟩ := (F.legalCandidate_iff hr c).mp (by simpa [candidates] using hc)
    obtain ⟨p,hp,hpc⟩ := mem_image.mp hce
    have hsame : c.1 ∪ {c.2.1,c.2.2}=e := by
      rw [←hpc]
      exact candidate_union_of_role hp
    exact mem_biUnion.mpr ⟨e,hsame ▸ he,mem_image.mpr ⟨p,hp,hpc⟩⟩
  apply (card_le_card hs).trans_eq
  apply edgeCandidates_biUnion_card
  intro e he
  exact ((mem_allowedEdges _ _ _).mp (F.rawHost_original_prohibition H (hU he))).1

lemma restrictedExistingCandidates_subset_existing (F : Frame r original)
    (H U : SimpleHypergraph V) (hU : U⊆F.rawHost H) :
    F.restrictedExistingCandidates U ⊆ F.existingCandidates H := by
  intro c hc
  obtain ⟨hc,he⟩ := mem_filter.mp hc
  exact mem_filter.mpr ⟨hc,hU he⟩

/-- The exceptional source roles in the sampling host are charged to the
already bounded complete raw-host exceptional family. -/
theorem restrictedExceptional_card_le (F : Frame r original)
    (H U : SimpleHypergraph V) (hU : U⊆F.rawHost H) (t : ℝ) :
    ((F.restrictedExistingCandidates U).filter (fun c =>
      t < |(F.completionCount H c:ℝ)/
        ((F.cycleCount H:ℝ)/(((r:ℝ)-1)^2*F.mu H))-1|)).card ≤
      (F.existingExceptional H t).card := by
  apply card_le_card
  exact filter_subset_filter _ (F.restrictedExistingCandidates_subset_existing H U hU)
end LooseHamilton.AuxiliaryFrame.Frame
