module

public import HittingTimeLooseHamilton.Models
public import HittingTimeLooseHamilton.KahnRandomOrder

public section

/-! The terminal coordinate of the existing extension law remains uniform. -/
noncomputable section
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem extension_terminal_event (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (P : SimpleHypergraph V → Prop) :
    (extensionLaw r M ell).event (fun ω => P ω.1.val) =
      (terminalLaw r M ell).event (fun F => P F.val) := by
  have h := FiniteEntropy.Law.event_prod_and (terminalLaw r M ell)
    (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M))
    (fun F => P F.val) (fun _ => True)
  simpa only [extensionLaw,and_true,FiniteEntropy.Law.event_true,mul_one] using h
end LooseHamilton
