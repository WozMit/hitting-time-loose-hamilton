module

public import HittingTimeLooseHamilton.BatchSelectionUniform
public import HittingTimeLooseHamilton.TerminalRegularityModels
public import HittingTimeLooseHamilton.BoundaryModels

public section

/-! The fixed-source experiment and numerical conclusion of Lemma 5.3. -/
noncomputable section
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The paper's batch size; real division precedes flooring. -/
@[expose] def noDeficitBatchSize (m k : ℕ) (ν : ℝ) : ℕ := Nat.floor (ν * m / k)

/-- Every original vertex lower bound is retained after the selected batch. -/
@[expose] def BatchRetainsLower (F : SimpleHypergraph V) (ell : V → ℕ)
    (T : SimpleHypergraph V) : Prop := ∀ v, ell v ≤ vertexDegree (F \ T) v

/-- The explicit meaning of the paper's O and Omega error terms. -/
@[expose] def noDeficitError (A c : ℝ) (n : ℕ) (ν : ℝ) : ℝ :=
  A * ν * (n : ℝ) ^ (-(3 / 4 : ℝ)) * Real.log n +
    Real.exp (-c * (Real.log n)^2)

/-- The genuine uniform batch experiment on a fixed host. The size constraint
is part of the conclusion, so no inadmissible batch is silently sampled. -/
@[expose] def NoDeficitEstimate (A c : ℝ) (F H : SimpleHypergraph V)
    (ell : V → ℕ) (k : ℕ) (ν : ℝ) : Prop :=
  let τ := noDeficitBatchSize H.card k ν
  τ ≤ H.card ∧
    1 - noDeficitError A c (Fintype.card V) ν ≤
      (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder H.card)).event
        (fun σ => BatchRetainsLower F ell (batchSelection H H.card rfl τ σ))

end LooseHamilton
