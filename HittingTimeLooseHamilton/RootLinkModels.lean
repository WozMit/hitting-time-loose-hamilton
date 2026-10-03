module

public import HittingTimeLooseHamilton.UniformNestedOuter
public import HittingTimeLooseHamilton.UniformConditionalEquivalence

public section

/-! Exact root-link observations and their residual nested-pair space. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Root edges, used as coordinates for the (r-1)-set link universe. -/
@[expose] def rootEdgeUniverse (r : ℕ) (y : V) : SimpleHypergraph V :=
  (completeEdges V r).filter (fun e => y∈e)

/-- The edges avoiding the root, retained on the original vertex type. -/
@[expose] def rootFreeEdges (y : V) (F : SimpleHypergraph V) : SimpleHypergraph V :=
  F.filter (fun e => y∉e)

/-- An arbitrary remaining root-edge universe U also permits finitely many
prescribed root edges to be removed and included in the observed fixed parts. -/
@[expose] def RootLinkObservation (U A B : SimpleHypergraph V) (F H : SimpleHypergraph V) : Prop :=
  F\U=A ∧ H\U=B

/-- A residual inner/outer pair, with the full terminal-feasibility constraint exposed. -/
@[expose] def RootLinkFeasibleState (U A : SimpleHypergraph V) (ell : V → ℕ) (b q : ℕ) :=
  {p : FiniteNestedSubsets U b q // ∀ v, ell v ≤ vertexDegree (A∪p.val.1) v}

@[expose] instance (U A : SimpleHypergraph V) (ell : V → ℕ) (b q : ℕ) :
    Fintype (RootLinkFeasibleState U A ell b q) := by
  classical
  unfold RootLinkFeasibleState
  infer_instance

@[expose] instance (U A : SimpleHypergraph V) (ell : V → ℕ) (b q : ℕ) :
    DecidableEq (RootLinkFeasibleState U A ell b q) := Classical.decEq _

abbrev RootLinkFiber (r M : ℕ) (ell : V → ℕ) (m : ℕ) (U A B : SimpleHypergraph V) :=
  {p : NestedState V r M ell m // RootLinkObservation U A B p.val.1.val p.val.2}

lemma rootFreeEdges_eq_sdiff_universe (r : ℕ) (y : V) (F : SimpleHypergraph V)
    (hF : F ⊆ completeEdges V r) : rootFreeEdges y F=F\rootEdgeUniverse r y := by
  ext e
  simp only [rootFreeEdges,rootEdgeUniverse,mem_filter,mem_sdiff]
  constructor
  · rintro ⟨he,hy⟩
    exact ⟨he,fun h=>hy h.2⟩
  · rintro ⟨he,hn⟩
    exact ⟨he,fun hy=>hn ⟨hF he,hy⟩⟩
end LooseHamilton
