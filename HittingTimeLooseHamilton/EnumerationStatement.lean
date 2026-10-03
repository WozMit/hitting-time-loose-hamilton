module

public import HittingTimeLooseHamilton.Counting
public import HittingTimeLooseHamilton.Setup

public section

/-! # Exact target for Proposition 2.2

This file specifies the complete-host enumeration proposition. Its unconditional
proof is `LooseHamilton.proposition22` in `Enumeration.lean`, using the proved
bijection between finite encoding data and actual unoriented cycle edge sets.
-/
namespace LooseHamilton

/-- The right-hand side of the unrestricted complete-host formula. The private
allocation quotient is an integer (proved separately in `Allocation`). -/
@[expose] def completeHostFormula (r N k s : ℕ) : ℕ :=
  2 ^ (s - 1) * (k - 1).factorial * (N - 2 * s).choose (k - s) *
    (((r - 2) * k).factorial / ((r - 2).factorial ^ k))

/-- Proposition 2.2, with all hypotheses and both assertions explicit.
The ratio is real division, while the unrestricted count is a natural number. -/
@[expose] def Proposition22 : Prop :=
  ∀ r N k s : ℕ, 3 ≤ r → 1 ≤ s → max 3 s ≤ k → N = (r - 1) * k + s →
    ∀ markers : Finset (Finset (Fin N)), IsPairMatching markers → markers.card = s →
      unrestrictedCycleCount r markers (completeEdges (Fin N) r) =
        completeHostFormula r N k s ∧
      (2 * s ≤ k →
        (cycleCount r markers (completeEdges (Fin N) r) (originalPorts markers) : ℝ) =
          (unrestrictedCycleCount r markers (completeEdges (Fin N) r) : ℝ) *
            ((k - s).factorial * (k - s - 1).factorial : ℝ) /
              ((k - 1).factorial * (k - 2 * s).factorial : ℝ) ∧
        1 - (s : ℝ) * ((s : ℝ) - 1) / ((k : ℝ) - 1) ≤
          ((k - s).factorial * (k - s - 1).factorial : ℝ) /
            ((k - 1).factorial * (k - 2 * s).factorial : ℝ))

end LooseHamilton
