module

public import HittingTimeLooseHamilton.Models

public section

/-! Reading a one-step decrease of the extension path as the deleted edge. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- At a reachable nonterminal time, saying that the next graph is H-e is
exactly saying that e is absent after the next deletion. -/
theorem extension_next_deletion_iff {r M j : ℕ} {ell : V → ℕ}
    (F : TerminalState V r M ell) (σ : MissingOrder V r M)
    (H : SimpleHypergraph V) (e : Finset V) (hM : M < j)
    (hj : j ≤ (completeEdges V r).card) (hH : extensionState F σ j = H)
    (he : e ∈ H) :
    extensionState F σ (j-1) = H.erase e ↔ e ∉ extensionState F σ (j-1) := by
  constructor
  · intro h
    rw [h]
    exact notMem_erase _ _
  · intro h
    have hsub : extensionState F σ (j-1) ⊆ H := by
      rw [← hH]
      exact extensionState_mono F σ (Nat.sub_le j 1)
    apply eq_of_subset_of_card_le (subset_erase.mpr ⟨hsub,h⟩)
    rw [card_erase_of_mem he,← hH,
      extensionState_card F σ j (by omega) hj,
      extensionState_card F σ (j-1) (by omega) (by omega)]

end LooseHamilton
