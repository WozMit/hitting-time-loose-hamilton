module

public import HittingTimeLooseHamilton.TerminalFeasibilityFinite

public section

/-! Exact finite positivity of the event on which the path is conditioned. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Nonemptiness of the terminal family makes the conditioning probability
strictly positive; no asymptotic estimate is needed for this finite fact. -/
theorem terminalFeasibilityProbability_pos (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] :
    0 < terminalFeasibilityProbability r M ell := by
  classical
  obtain ⟨F⟩ := ‹Nonempty (TerminalState V r M ell)›
  have hM := terminal_size_le F
  rw [terminalFeasibilityProbability_eq_ratio r M ell hM]
  apply div_pos
  · exact_mod_cast (show 0 < (((completeEdges V r).powersetCard M).filter
        (fun G => ∀ v, ell v ≤ vertexDegree G v)).card from
      card_pos.mpr ⟨F.val,mem_filter.mpr
        ⟨mem_powersetCard.mpr ⟨F.property.1,F.property.2.1⟩,F.property.2.2⟩⟩)
  · exact_mod_cast Nat.choose_pos (by simpa only [completeEdges_card] using hM)
end LooseHamilton
