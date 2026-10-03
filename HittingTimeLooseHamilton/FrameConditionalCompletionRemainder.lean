module

public import HittingTimeLooseHamilton.FrameConditionalCompletion

public section

/-! Identifying the surviving actual families on the retained-boundary remainder. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

lemma rawHost_idempotent (f : Frame r original) (H : SimpleHypergraph V) :
    f.rawHost (f.rawHost H) = f.rawHost H := by
  ext e
  simp only [Frame.rawHost, mem_filter, mem_inter]
  tauto

lemma cycleFamily_rawHost (f : Frame r original) (H : SimpleHypergraph V) :
    f.cycleFamily (f.rawHost H) = f.cycleFamily H := by
  unfold Frame.cycleFamily
  rw [rawHost_idempotent]

lemma completionFamily_rawHost (f : Frame r original) (H : SimpleHypergraph V)
    (c : Finset V × V × V) :
    f.completionFamily (f.rawHost H) c = f.completionFamily H c := by
  unfold Frame.completionFamily
  rw [rawHost_idempotent]

/-- The entire cycle family on `G` is the actual surviving source family. -/
theorem rawRemainder_cycleFamily (f : Frame r original) (D : Finset V)
    (H T : SimpleHypergraph V) (hT : T ⊆ unexposed f D H) :
    f.cycleFamily (rawRemainder f D H T) = f.cycleFamily (H \ T) := by
  rw [rawRemainder_eq f D H T hT, ← f.rawHost_delete H T, cycleFamily_rawHost]

/-- No completion labels are lost when restoring the retained boundary. -/
theorem rawRemainder_completionFamily (f : Frame r original) (D : Finset V)
    (H T : SimpleHypergraph V) (c : Finset V × V × V)
    (hT : T ⊆ unexposed f D H) :
    f.completionFamily (rawRemainder f D H T) c = f.completionFamily (H \ T) c := by
  rw [rawRemainder_eq f D H T hT, ← f.rawHost_delete H T, completionFamily_rawHost]

theorem rawRemainder_completionCount (f : Frame r original) (D : Finset V)
    (H T : SimpleHypergraph V) (c : Finset V × V × V)
    (hT : T ⊆ unexposed f D H) :
    f.completionCount (rawRemainder f D H T) c = f.completionCount (H \ T) c :=
  congrArg Finset.card (rawRemainder_completionFamily f D H T c hT)

/-- This is the exact conditional expectation of the actual completion count on
`G`, with fixed boundary edges present, not merely an abstract indexed mean. -/
theorem conditional_completion_expectation_eq (f : Frame r original) (hr : 3 ≤ r)
    (D : Finset V) (H : SimpleHypergraph V) (c : Finset V × V × V)
    (hc : f.LegalCandidate c)
    (he : c.1 ∪ {c.2.1,c.2.2} ∈ unexposed f D H) {τ : ℕ}
    (hτ : τ-1 ≤ ((unexposed f D H).erase (c.1 ∪ {c.2.1,c.2.2})).card) :
    (∑ T, (hostBatchLaw hτ).mass T *
      (f.completionCount (rawRemainder f D H (insert (c.1 ∪ {c.2.1,c.2.2}) T.val)) c : ℝ)) =
    IndexedSurvival.mean hτ (f.completionFamily H c)
      (fun E => E ∩ unexposed f D H) := by
  unfold IndexedSurvival.mean
  apply sum_congr rfl
  intro T _
  have hT := (mem_powersetCard.mp T.property).1
  rw [rawRemainder_completionCount f D H _ c
    (insert_subset he (hT.trans (erase_subset _ _))),
    completionCount_conditioned_eq_indexed f hr D H T.val c hc hT]

end LooseHamilton.CandidateBalance
