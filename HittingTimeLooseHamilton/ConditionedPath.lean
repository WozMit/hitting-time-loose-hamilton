module

public import HittingTimeLooseHamilton.ConditionedPathStatement
public import HittingTimeLooseHamilton.ExtensionPathLaw
public import HittingTimeLooseHamilton.NextDeletionProbability
public import HittingTimeLooseHamilton.ExtensionNextEvent
public import HittingTimeLooseHamilton.TerminalCompletionRecurrence

public section

/-! Item 19: complete conditioned path law and exact next-deletion formula. -/
noncomputable section
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Division is legitimate for every nonempty terminal family, with no
large-N or regularity assumption. -/
theorem extension_path_event_eq_conditioned (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (P : (ℕ → SimpleHypergraph V) → Prop) :
    (extensionLaw r M ell).event (fun ω => P (extensionState ω.1 ω.2)) =
      (processLaw V r).event (fun σ =>
        (∀ v, ell v ≤ vertexDegree (processState σ M) v) ∧
        P (fun j => processState σ (max M j))) /
      terminalFeasibilityProbability r M ell := by
  apply (eq_div_iff (terminalFeasibilityProbability_pos r M ell).ne').mpr
  exact extension_path_event_mul_feasibility r M ell P

/-- The complete item-19 statement, including positivity of every state on
which the displayed next-deletion probability is conditioned. -/
theorem conditioned_path_and_next_deletion : ConditionedPathAndNextDeletion := by
  intro V _ _ r M ell _
  refine ⟨extension_path_event_eq_conditioned r M ell,?_⟩
  intro j H e hMj hj hH hHj he hZ
  exact ⟨extension_current_state_positive r M ell j H hH hHj hMj.le hj hZ,
    next_deletion_probability r M ell j hMj hj H hH hHj e he hZ⟩

/-- Literal edge-deletion form of equation (eq:nextdelete). -/
theorem next_edge_deletion_probability (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)]
    (j : ℕ) (hMj : M < j) (hj : j ≤ (completeEdges V r).card)
    (H : SimpleHypergraph V) (hH : H ⊆ completeEdges V r) (hHj : H.card=j)
    (e : Finset V) (he : e∈H) (hZ : 0<terminalCompletionCount r M ell H) :
    (extensionLaw r M ell).event (fun ω =>
      extensionState ω.1 ω.2 j=H ∧ e∉extensionState ω.1 ω.2 (j-1)) /
      (extensionLaw r M ell).event (fun ω => extensionState ω.1 ω.2 j=H) =
      (terminalCompletionCount r M ell (H.erase e):ℝ) /
        (((j-M:ℕ):ℝ)*(terminalCompletionCount r M ell H:ℝ)) := by
  have hp : (fun ω : TerminalState V r M ell × MissingOrder V r M =>
      extensionState ω.1 ω.2 j=H ∧ e∉extensionState ω.1 ω.2 (j-1)) =
      (fun ω => extensionState ω.1 ω.2 j=H ∧ extensionState ω.1 ω.2 (j-1)=H.erase e) := by
    funext ω
    apply propext
    constructor
    · rintro ⟨hcur,habs⟩
      exact ⟨hcur,(extension_next_deletion_iff ω.1 ω.2 H e hMj hj hcur he).mpr habs⟩
    · rintro ⟨hcur,hprev⟩
      exact ⟨hcur,(extension_next_deletion_iff ω.1 ω.2 H e hMj hj hcur he).mp hprev⟩
  rw [hp]
  exact next_deletion_probability r M ell j hMj hj H hH hHj e he hZ
end LooseHamilton
