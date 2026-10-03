module

public import HittingTimeLooseHamilton.Setup
public import HittingTimeLooseHamilton.Operations

public section

/-! The three path regularity bounds and the fixed-host perturbations. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

@[expose] def junctionFraction (r : ℕ) : ℝ := 1/((r:ℝ)-1)
@[expose] def privateFraction (r : ℕ) : ℝ := ((r:ℝ)-2)/((r:ℝ)-1)
@[expose] def partitionDensity (r : ℕ) : ℝ :=
  (r.choose 2:ℝ)*(junctionFraction r)^2*(privateFraction r)^(r-2)

/-- Counts edges with exactly two vertices in A. -/
@[expose] def partitionCount (F : SimpleHypergraph V) (A : Finset V) : ℕ :=
  (F.filter (fun e => (e ∩ A).card=2)).card

/-- The fixed original-port prohibition, not recomputed from auxiliary markers. -/
@[expose] def fixedPortHost (F : SimpleHypergraph V) (U : Finset V) : SimpleHypergraph V :=
  F.filter (fun e => (e ∩ U).card ≤ 1)

@[expose] def PathPartitionRegular (r : ℕ) (C L : ℝ) (F : SimpleHypergraph V) : Prop :=
  ∀ A : Finset V, |(A.card:ℝ)-junctionFraction r*Fintype.card V| ≤
    L*(Fintype.card V:ℝ)^(1/10:ℝ) →
    |(partitionCount F A:ℝ)-partitionDensity r*F.card| ≤
      C*Fintype.card V*meanDegree (V:=V) r F.card*
        (Real.log (Fintype.card V:ℝ))^(-1/8:ℝ)

/-- The bounds that remain valid after the fixed port prohibition.
The mean is computed from the actual graph size and vertex count. -/
structure PathGraphUpperRegular (r : ℕ) (C L : ℝ) (F : SimpleHypergraph V) : Prop where
  upper_degree : ∀ v, (vertexDegree F v:ℝ) ≤ C*meanDegree (V:=V) r F.card
  codegree : ∀ u v, u ≠ v → (pairDegree F u v:ℝ) ≤
    C*meanDegree (V:=V) r F.card*(Real.log (Fintype.card V:ℝ))^(-1/4:ℝ)
  partitions : PathPartitionRegular r C L F

/-- All three displayed bounds of Proposition 4.4, with both degree inequalities. -/
structure PathGraphRegular (r : ℕ) (c C L : ℝ) (F : SimpleHypergraph V)
    extends PathGraphUpperRegular r C L F : Prop where
  lower_degree : ∀ v, c*meanDegree (V:=V) r F.card ≤ (vertexDegree F v:ℝ)

/-- Simultaneous regularity at every time of the genuine extension process Q. -/
@[expose] def PathRegularityEvent (r M : ℕ) (ell : V → ℕ) (c C L : ℝ)
    (ω : TerminalState V r M ell × MissingOrder V r M) : Prop :=
  ∀ j : ℕ, M ≤ j → j ≤ (completeEdges V r).card →
    PathGraphRegular r c C L (extensionState ω.1 ω.2 j)

/-- Simultaneous induced-deletion variant, with updated size and vertex parameters. -/
@[expose] def PathDeletionRegularityEvent (r M : ℕ) (ell : V → ℕ) (h : ℕ) (c C L : ℝ)
    (ω : TerminalState V r M ell × MissingOrder V r M) : Prop :=
  ∀ j : ℕ, M ≤ j → j ≤ (completeEdges V r).card →
    ∀ Z : Finset V, Z.card ≤ h →
      PathGraphRegular r c C L (deleteVertices Z (extensionState ω.1 ω.2 j))

/-- Only upper bounds and partition estimates are asserted after port prohibition.
Deleted vertices are removed from the original port set by restriction alone. -/
@[expose] def PathProhibitionRegularityEvent (r M : ℕ) (ell : V → ℕ)
    (markers : Finset (Finset V)) (h : ℕ) (C L : ℝ)
    (ω : TerminalState V r M ell × MissingOrder V r M) : Prop :=
  ∀ j : ℕ, M ≤ j → j ≤ (completeEdges V r).card →
    ∀ Z : Finset V, Z.card ≤ h →
      PathGraphUpperRegular r C L
        (fixedPortHost (deleteVertices Z (extensionState ω.1 ω.2 j))
          (restrictedPorts (univ \ Z) (originalPorts markers)))
end LooseHamilton
