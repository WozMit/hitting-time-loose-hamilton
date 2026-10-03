module

public import HittingTimeLooseHamilton.RootFreeCommonEvent
public import HittingTimeLooseHamilton.BenchmarkAlgebra

public section

/-! # Exact specification of Uniform marginal cap
The supplied manuscript's `thm:marginal` (Theorem 10.1). The strict maximum
violation is expressed by an edge in the current host attaining a violation.
The epsilon--N formulation is uniform over all admissible core instances. -/
noncomputable section
namespace LooseHamilton.UniformMarginalCap

/-- The event A_j with the exact complete-host harmonic baseline. -/
@[expose] def Eligible {N r m : ℕ} {ell : Fin N → ℕ}
    (M : Finset (Finset (Fin N))) (j : ℕ)
    (ω : CandidateBalance.Outcome (Fin N) r m ell) : Prop :=
  logarithmicBaseline r (ordinaryEdgeCount r M) j M -
    (N:ℝ)/Real.sqrt (Real.log N) ≤
      Real.log (cycleCount r M (extensionState ω.1 ω.2 j) (originalPorts M):ℝ)

/-- A failure at some eligible time and some actual host edge. No conditioning
on A_j or on any auxiliary regularity event is imposed on the path law. -/
@[expose] def Failure {N r m : ℕ} {ell : Fin N → ℕ}
    (M : Finset (Finset (Fin N))) (D : ℝ)
    (ω : CandidateBalance.Outcome (Fin N) r m ell) : Prop :=
  ∃ j : ℕ, m ≤ j ∧ j ≤ (completeEdges (Fin N) r).card ∧ Eligible M j ω ∧
    ∃ e ∈ extensionState ω.1 ω.2 j,
      D*(ordinaryEdgeCount r M:ℝ)/j <
        cycleMarginal r M (extensionState ω.1 ω.2 j) (originalPorts M) e

/-- A constant depending only on the fixed uniformity, followed by uniform
vanishing failure probability for every fixed bound on the degree offsets. -/
@[expose] def Statement (r : ℕ) : Prop :=
  ∃ D : ℝ, 0<D ∧ ∀ offset : ℝ, 0≤offset → ∀ ε : ℝ, 0<ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀≤N → ∀ m : ℕ, ∀ ell : Fin N → ℕ,
    ∀ M : Finset (Finset (Fin N)),
    ∀ admissible : CoreAdmissible r m ell M offset,
    letI : Nonempty (TerminalState (Fin N) r m ell) := admissible.feasible
    (extensionLaw r m ell).event (Failure M D) ≤ ε

end LooseHamilton.UniformMarginalCap

namespace LooseHamilton
/-- Theorem 10.1: the uniform marginal cap under the actual conditioned path law. -/
@[expose] def Theorem101 : Prop := ∀ r : ℕ, 3 ≤ r → UniformMarginalCap.Statement r
end LooseHamilton
