module

public import HittingTimeLooseHamilton.CoreTrace
public import HittingTimeLooseHamilton.Operations

public section

/-! The exact terminal/current boundary data of Lemma 5.1. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All edges meeting the exposed vertex set. -/
abbrev boundaryEdges (D : Finset V) (F : SimpleHypergraph V) : SimpleHypergraph V :=
  traceOn D F

/-- Natural subtraction is max(0,ell(v)-degree_A(v)), as printed in the paper. -/
@[expose] def adjustedBoundaryLower (ell : V → ℕ) (D : Finset V) (A : SimpleHypergraph V)
    (v : ↥(univ \ D)) : ℕ := ell v.val - vertexDegree A v.val

/-- Exact observations of the terminal and current edges meeting D. -/
@[expose] def BoundaryEvent (r M : ℕ) (ell : V → ℕ) (j : ℕ)
    (D : Finset V) (A B : SimpleHypergraph V)
    (ω : TerminalState V r M ell × MissingOrder V r M) : Prop :=
  boundaryEdges D ω.1.val = A ∧ boundaryEdges D (extensionState ω.1 ω.2 j) = B

/-- A finite feasible nested pair witnessing consistency of the boundary data.
Positivity of the actual boundary event will imply this condition. -/
@[expose] def BoundaryWitness (r M : ℕ) (ell : V → ℕ) (j : ℕ)
    (D : Finset V) (A B : SimpleHypergraph V) : Prop :=
  ∃ F : TerminalState V r M ell, ∃ H : SimpleHypergraph V,
    F.val ⊆ H ∧ H ⊆ completeEdges V r ∧ H.card=j ∧
    boundaryEdges D F.val=A ∧ boundaryEdges D H=B

end LooseHamilton
