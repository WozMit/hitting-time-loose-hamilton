module

public import HittingTimeLooseHamilton.EnumerationStatement
public import Mathlib.Data.Nat.Factorial.Basic

public section

/-! # The explicit directed normalization factor and sparse scale -/
noncomputable section
namespace LooseHamilton

/-- The right side of equation (exactY); all divisions are in the reals. -/
@[expose] def directedNormalizationFactor (r N k s : ℕ) : ℝ :=
  ((r - 2).factorial : ℝ) * (k - s : ℕ) * (k - s - 1 : ℕ) /
    ((k - 1 : ℕ) * ((N - 2 * s).descFactorial r : ℝ))

/-- The mean degree of the complete r-uniform host. -/
@[expose] def completeMeanDegree (r N : ℕ) : ℝ := ((N - 1).choose (r - 1) : ℝ)

/-- The manuscript's sparse directed scale X(G,M)/((r-1)^2 μ). -/
@[expose] def sparseDirectedScale {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (markers host : Finset (Finset V)) : ℝ :=
  (unrestrictedCycleCount r markers host : ℝ) /
    (((r : ℝ) - 1)^2 * ((r : ℝ) * host.card / Fintype.card V))
end LooseHamilton
