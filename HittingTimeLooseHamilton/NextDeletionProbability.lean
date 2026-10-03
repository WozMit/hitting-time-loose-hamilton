module

public import HittingTimeLooseHamilton.NextDeletionJoint
public import HittingTimeLooseHamilton.ExtensionMarginalCompletion
public import HittingTimeLooseHamilton.KahnConditioning

public section

/-! Equation (eq:nextdelete): the next-deletion kernel of the actual law Q. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Conditional probability expressed as the joint-event/current-event ratio.
The theorem below separately establishes that the current-state event has positive probability. -/
@[expose] def nextDeletionProbability (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (H : SimpleHypergraph V) (e : Finset V) : ℝ :=
  (extensionLaw r M ell).event (fun ω =>
    extensionState ω.1 ω.2 j=H ∧ extensionState ω.1 ω.2 (j-1)=H.erase e) /
      (extensionLaw r M ell).event (fun ω => extensionState ω.1 ω.2 j=H)

lemma extension_current_state_positive (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)]
    (j : ℕ) (H : SimpleHypergraph V) (hH : H ⊆ completeEdges V r)
    (hHj : H.card=j) (hMj : M ≤ j) (hj : j ≤ (completeEdges V r).card)
    (hZ : 0<terminalCompletionCount r M ell H) :
    0 < (extensionLaw r M ell).event (fun ω => extensionState ω.1 ω.2 j=H) := by
  rw [extension_marginal_completion_probability r M ell j H hH hHj hMj hj]
  apply div_pos (by exact_mod_cast hZ)
  apply mul_pos
  · exact_mod_cast Fintype.card_pos
  · exact_mod_cast Nat.choose_pos (show j-M ≤ (completeEdges V r).card-M by omega)

/-- Exact next-deletion law at every reachable current state H of size j>M. -/
theorem next_deletion_probability (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)]
    (j : ℕ) (hMj : M<j) (hj : j ≤ (completeEdges V r).card)
    (H : SimpleHypergraph V) (hH : H ⊆ completeEdges V r) (hHj : H.card=j)
    (e : Finset V) (he : e∈H) (hZ : 0<terminalCompletionCount r M ell H) :
    nextDeletionProbability r M ell j H e =
      (terminalCompletionCount r M ell (H.erase e):ℝ) /
        (((j-M:ℕ):ℝ)*(terminalCompletionCount r M ell H:ℝ)) := by
  have hT : (Fintype.card (TerminalState V r M ell):ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hC : ((((completeEdges V r).card-M).choose (j-M)):ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (show j-M ≤ (completeEdges V r).card-M by omega)))
  have hZ' : (terminalCompletionCount r M ell H:ℝ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hdiff : ((j-M:ℕ):ℝ) ≠ 0 := by exact_mod_cast (show j-M ≠ 0 by omega)
  rw [nextDeletionProbability,extension_boundary_completion_probability r M ell j hMj hj H hH hHj e he,
    extension_marginal_completion_probability r M ell j H hH hHj hMj.le hj]
  field_simp <;> ring

/-- The ratio is precisely the event probability in the positive-probability conditional law. -/
lemma nextDeletionProbability_eq_condition (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (H : SimpleHypergraph V) (e : Finset V)
    (hH : 0<(extensionLaw r M ell).event (fun ω => extensionState ω.1 ω.2 j=H)) :
    nextDeletionProbability r M ell j H e =
      ((extensionLaw r M ell).condition (fun ω => extensionState ω.1 ω.2 j=H) hH).event
        (fun ω => extensionState ω.1 ω.2 (j-1)=H.erase e) := by
  classical
  unfold nextDeletionProbability FiniteEntropy.Law.condition FiniteEntropy.Law.event
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hc : extensionState ω.1 ω.2 j=H <;>
    by_cases hd : extensionState ω.1 ω.2 (j-1)=H.erase e <;> simp [hc,hd]
end LooseHamilton
