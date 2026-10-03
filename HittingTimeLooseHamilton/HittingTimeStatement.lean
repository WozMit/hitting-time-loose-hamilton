module

public import HittingTimeLooseHamilton.Setup

public section

/-! Theorem 1.1, `thm:main`: the loose-Hamilton hitting time equals the
minimum-degree-one hitting time for fixed r, along admissible vertex counts. -/
noncomputable section
namespace LooseHamilton.HittingTimeConclusion
open Filter

/-- Uniform epsilon--N form of the assertion along multiples of r-1. -/
@[expose] def Statement (r : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → r-1 ∣ n →
    1-ε ≤ hittingTimeProbability (Fin n) r

end LooseHamilton.HittingTimeConclusion

namespace LooseHamilton
open Filter

/-- The exact probability-one limit, as n tends to infinity through multiples
of r-1. The index q parametrizes all such vertex counts n=(r-1)*q. -/
@[expose] def Theorem11 : Prop := ∀ r : ℕ, 3 ≤ r →
  Tendsto (fun q : ℕ => hittingTimeProbability (Fin ((r-1)*q)) r) atTop (nhds 1)

end LooseHamilton
