module

public import HittingTimeLooseHamilton.BenchmarkAlgebra
public import HittingTimeLooseHamilton.Setup
public import HittingTimeLooseHamilton.KahnLaw

public section

/-! Theorem 1.2, `thm:core`: Conditioned core count. The terminal graph is
uniform in the feasible fixed-size degree-lower-bound family. -/
noncomputable section
namespace LooseHamilton.CoreCount

/-- The precise logarithmic count lower bound, including the positive-count
domain of the manuscript's logarithm. The original ports stay fixed. -/
@[expose] def Good {N : ℕ} (r m : ℕ) (markers : Finset (Finset (Fin N)))
    (C : ℝ) (F : SimpleHypergraph (Fin N)) : Prop :=
  0 < cycleCount r markers F (originalPorts markers) ∧
    logarithmicBenchmark r N (ordinaryEdgeCount r markers) m - C*N/Real.log N ≤
      Real.log (cycleCount r markers F (originalPorts markers) : ℝ)

/-- Uniform high probability under the actual terminal law. The error
constant depends only on r, before the fixed bound on the degree offsets. -/
@[expose] def Statement (r : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ offset : ℝ, 0 ≤ offset → ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ m : ℕ, ∀ ell : Fin N → ℕ,
    ∀ markers : Finset (Finset (Fin N)),
    ∀ admissible : CoreAdmissible r m ell markers offset,
    letI : Nonempty (TerminalState (Fin N) r m ell) := admissible.feasible
    1-ε ≤ (terminalLaw r m ell).event (fun F => Good r m markers C F.val)

end LooseHamilton.CoreCount

namespace LooseHamilton
/-- Theorem 1.2 of the supplied general-r manuscript, Conditioned core count. -/
@[expose] def Theorem12 : Prop := ∀ r : ℕ, 3 ≤ r → CoreCount.Statement r
end LooseHamilton
