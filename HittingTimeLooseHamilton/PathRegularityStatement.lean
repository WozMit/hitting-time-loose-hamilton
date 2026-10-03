module

public import HittingTimeLooseHamilton.PathRegularityModels

public section

/-! Proposition 4.4, with every asymptotic quantifier made explicit. -/
noncomputable section
namespace LooseHamilton

/-- Uniform high probability of all three path bounds, and the stated
bounded-deletion and fixed-original-port variants. Constants c,C depend only
on r; adjusted constants may also depend on the fixed deletion budget h.
The size cutoff may depend on all the displayed fixed parameters. -/
@[expose] def Proposition44 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ h : ℕ, ∃ c' C' : ℝ, 0 < c' ∧ 0 < C' ∧
      ∀ B L : ℝ, 0 ≤ B → 0 ≤ L → ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V], N₀ ≤ Fintype.card V →
          ∀ (M : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
            ∀ hadm : CoreAdmissible r M ell markers B,
            letI : Nonempty (TerminalState V r M ell) := hadm.feasible
            1-η ≤ (extensionLaw r M ell).event (fun ω =>
              PathRegularityEvent r M ell c C L ω ∧
              PathDeletionRegularityEvent r M ell h c' C' L ω ∧
              PathProhibitionRegularityEvent r M ell markers h C' L ω)
end LooseHamilton
