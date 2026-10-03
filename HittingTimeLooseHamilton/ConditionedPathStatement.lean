module

public import HittingTimeLooseHamilton.TerminalCompletionCount
public import HittingTimeLooseHamilton.TerminalFeasibilityPositive

public section

/-! The exact finite path-law and next-deletion statements of Section 5.
No asymptotic regularity hypothesis is required for these identities. -/
noncomputable section
namespace LooseHamilton

/-- Item 19: conditioning ordinary uniform deletion on terminal feasibility
gives exactly Q, for arbitrary events of the entire path. Below M the path is
clamped to its terminal graph, matching extensionState. The second clause is
the paper's next-deletion formula at each reachable nonterminal state. -/
@[expose] def ConditionedPathAndNextDeletion : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V], ∀ (r M : ℕ) (ell : V → ℕ),
    [Nonempty (TerminalState V r M ell)] →
    (∀ P : (ℕ → SimpleHypergraph V) → Prop,
      (extensionLaw r M ell).event (fun ω => P (extensionState ω.1 ω.2)) =
        (processLaw V r).event (fun σ =>
          (∀ v, ell v ≤ vertexDegree (processState σ M) v) ∧
          P (fun j => processState σ (max M j))) /
        terminalFeasibilityProbability r M ell) ∧
    (∀ (j : ℕ) (H : SimpleHypergraph V) (e : Finset V),
      M < j → j ≤ (completeEdges V r).card → H ⊆ completeEdges V r →
      H.card = j → e ∈ H → 0 < terminalCompletionCount r M ell H →
      0 < (extensionLaw r M ell).event (fun ω => extensionState ω.1 ω.2 j = H) ∧
      (extensionLaw r M ell).event (fun ω =>
        extensionState ω.1 ω.2 j = H ∧ extensionState ω.1 ω.2 (j-1) = H.erase e) /
        (extensionLaw r M ell).event (fun ω => extensionState ω.1 ω.2 j = H) =
        (terminalCompletionCount r M ell (H.erase e):ℝ) /
          ((j-M:ℕ)*(terminalCompletionCount r M ell H:ℝ)))
end LooseHamilton
