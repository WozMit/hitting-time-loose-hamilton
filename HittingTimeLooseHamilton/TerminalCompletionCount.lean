module

public import HittingTimeLooseHamilton.Models

public section

/-! The number of terminal-feasible subgraphs inside a current host. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

@[expose] def terminalCompletionCount (r M : ℕ) (ell : V → ℕ) (H : SimpleHypergraph V) : ℕ :=
  ((univ : Finset (TerminalState V r M ell)).filter (fun F => F.val ⊆ H)).card

lemma terminalCompletionCount_pos_iff (r M : ℕ) (ell : V → ℕ) (H : SimpleHypergraph V) :
    0<terminalCompletionCount r M ell H ↔ ∃ F : TerminalState V r M ell, F.val ⊆ H := by
  rw [terminalCompletionCount,Finset.card_pos]
  constructor
  · rintro ⟨F,hF⟩
    exact ⟨F,(mem_filter.mp hF).2⟩
  · rintro ⟨F,hF⟩
    exact ⟨F,mem_filter.mpr ⟨mem_univ _,hF⟩⟩
end LooseHamilton
