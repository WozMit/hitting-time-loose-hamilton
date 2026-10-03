module

public import HittingTimeLooseHamilton.FrameConditionalCompletionRemainder
public import HittingTimeLooseHamilton.UniformConditionalEquivalence

public section

/-! Positivity and the normalized conditional law for the actual batch experiment. -/
noncomputable section
namespace LooseHamilton.FrameSurvival
open Finset
variable {α : Type*} [DecidableEq α]

/-- Deleting a present candidate has positive probability when the batch is nonempty. -/
theorem candidate_batch_event_pos {H : Finset α} {τ : ℕ} {e : α}
    (he : e ∈ H) (hτ : 1 ≤ τ) (hτH : τ ≤ H.card) :
    0 < (hostBatchLaw hτH).event (fun T => e ∈ T.val) := by
  classical
  letI := hostBatch_nonempty hτH
  have hsmall : τ-1 ≤ (H.erase e).card := by rw [card_erase_of_mem he]; omega
  letI := hostBatch_nonempty hsmall
  let E := candidateBatchEquiv he hτ
  letI : Nonempty (CandidateBatch H τ e) :=
    ⟨E.symm (Classical.choice (hostBatch_nonempty hsmall))⟩
  change 0 < (FiniteEntropy.uniform : FiniteEntropy.Law (HostBatch H τ)).event _
  rw [FiniteEntropy.Law.uniform_event, ← Fintype.card_subtype]
  apply div_pos <;> exact_mod_cast Fintype.card_pos

/-- An equality of normalized conditional probabilities, not only joint probabilities. -/
theorem candidate_batch_conditional_law {H : Finset α} {τ : ℕ} {e : α}
    (he : e ∈ H) (hτ : 1 ≤ τ) (hτH : τ ≤ H.card)
    (P : Finset α → Prop) :
    ((hostBatchLaw hτH).condition (fun T => e ∈ T.val)
      (candidate_batch_event_pos he hτ hτH)).event (fun T => P T.val) =
      (hostBatchLaw (show τ-1 ≤ (H.erase e).card by
        rw [card_erase_of_mem he]; omega)).event (fun T => P (insert e T.val)) := by
  classical
  rw [LooseHamilton.condition_event_eq_joint,
    candidate_conditioning he hτ hτH P]
  exact mul_div_cancel_left₀ _ (candidate_batch_event_pos he hτ hτH).ne'

end LooseHamilton.FrameSurvival
