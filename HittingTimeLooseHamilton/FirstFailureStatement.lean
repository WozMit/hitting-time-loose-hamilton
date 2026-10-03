module

public import HittingTimeLooseHamilton.UniformMarginalCapStatement

public section

/-! The all-times first-failure bootstrap in Section 11. This is the
logarithmic-baseline conclusion; conversion to the core-count benchmark is
item 39. -/
noncomputable section
namespace LooseHamilton.FirstFailure

/-- Failure of positive counts, the quantitative logarithmic lower bound,
or the marginal cap at any time in the full deletion interval. -/
@[expose] def PathFailure {N : ℕ} (r m : ℕ) (markers : Finset (Finset (Fin N)))
    (D B : ℝ) (H : ℕ → SimpleHypergraph (Fin N)) : Prop :=
  ∃ j : ℕ, m ≤ j ∧ j ≤ (completeEdges (Fin N) r).card ∧
    (cycleCount r markers (H j) (originalPorts markers) = 0 ∨
      Real.log (cycleCount r markers (H j) (originalPorts markers) : ℝ) <
        logarithmicBaseline r (ordinaryEdgeCount r markers) j markers - B ∨
      ∃ e ∈ H j, D * (ordinaryEdgeCount r markers : ℝ) / j <
        cycleMarginal r markers (H j) (originalPorts markers) e)

/-- Constants depend only on r. Size cutoffs may depend on the fixed offset
bound and probability tolerance, uniformly over all admissible instances. -/
@[expose] def Statement (r : ℕ) : Prop :=
  ∃ D : ℝ, 1 ≤ D ∧ ∃ B : ℝ, 0 < B ∧
    ∀ offset : ℝ, 0 ≤ offset → ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ m : ℕ, ∀ ell : Fin N → ℕ,
    ∀ markers : Finset (Finset (Fin N)),
    ∀ admissible : CoreAdmissible r m ell markers offset,
    letI : Nonempty (TerminalState (Fin N) r m ell) := admissible.feasible
    (extensionLaw r m ell).event (fun ω =>
      PathFailure r m markers D (B * N / Real.log N) (extensionState ω.1 ω.2)) ≤ ε

end LooseHamilton.FirstFailure

namespace LooseHamilton
/-- Section 11: simultaneous first-failure exclusion and quantitative counting. -/
@[expose] def FirstFailureBootstrap : Prop := ∀ r : ℕ, 3 ≤ r → FirstFailure.Statement r
end LooseHamilton
