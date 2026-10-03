module

public import HittingTimeLooseHamilton.RootLinkModels
public import HittingTimeLooseHamilton.RootLinkDeficit

public section

/-! Observable root-free data and the exact occupancy event of Lemma 5.6. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Fixing root-free terminal/current data and prescribing present current root
edges. Their terminal membership is NOT part of this observation. -/
@[expose] def RootFreeObservation (y : V) (F₀ H₀ R : SimpleHypergraph V)
    (p : SimpleHypergraph V × SimpleHypergraph V) : Prop :=
  rootFreeEdges y p.1=F₀ ∧ rootFreeEdges y p.2=H₀ ∧ R ⊆ p.2

/-- Equivalent to |L(y) intersect Gamma| >= 2q/3, with no rounding ambiguity.
Gamma is a subset of the root-edge universe, identified with (r-1)-links. -/
@[expose] def RootLinkBad (Γ : SimpleHypergraph V) (q : ℕ)
    (p : SimpleHypergraph V × SimpleHypergraph V) : Prop :=
  2*q ≤ 3*(p.2∩Γ).card

/-- Density in the full link universe, before prescribed edges are removed. -/
@[expose] def rootLinkDensity (r : ℕ) (y : V) (Γ : SimpleHypergraph V) : ℝ :=
  (Γ.card:ℝ)/(rootEdgeUniverse r y).card

/-- The observable terminal/current pair under the existing Q experiment. -/
@[expose] def rootSamplingPair (r M : ℕ) (ell : V → ℕ) (m : ℕ)
    (ω : TerminalState V r M ell × MissingOrder V r M) :
    SimpleHypergraph V × SimpleHypergraph V :=
  (ω.1.val,extensionState ω.1 ω.2 m)

end LooseHamilton
