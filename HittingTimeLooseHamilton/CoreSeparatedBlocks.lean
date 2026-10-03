module

public import HittingTimeLooseHamilton.CoreBlocks
public import HittingTimeLooseHamilton.CoreSeparation

public section

/-! The marked-core block family exists at every separated positive-degree anchor set. -/
noncomputable section
namespace LooseHamilton.CoreBlockFamily
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Construct all selected edges, retained ports and deleted private blocks by
choices that inspect only the exposed exceptional trace. -/
@[expose] def ofSeparated {r : ℕ} (hr : 3 ≤ r) {F : SimpleHypergraph V} {B : Finset V}
    (hF : F ⊆ completeEdges V r) (hpos : ∀ v ∈ B, 0 < vertexDegree F v)
    (hsep : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → ¬ shortBergeConnected F u v) :
    CoreBlockFamily r F B :=
  ofTrace hr hF hpos (selected_edges_pairwise_disjoint (exceptionalSelectedEdges F B hpos)
    (fun v => (exceptionalSelectedEdges_spec F B hpos v).1)
    (fun v => (exceptionalSelectedEdges_spec F B hpos v).2) hsep)

lemma ofSeparated_ports_eq_of_trace_eq {r : ℕ} (hr : 3 ≤ r) {F G : SimpleHypergraph V}
    {B : Finset V} (hF : F ⊆ completeEdges V r) (hG : G ⊆ completeEdges V r)
    (hpos : ∀ v ∈ B, 0 < vertexDegree F v) (hpos' : ∀ v ∈ B, 0 < vertexDegree G v)
    (hsep : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → ¬ shortBergeConnected F u v)
    (hsep' : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → ¬ shortBergeConnected G u v)
    (htrace : exceptionalTrace B F=exceptionalTrace B G) :
    (ofSeparated hr hF hpos hsep).ports = (ofSeparated hr hG hpos' hsep').ports :=
  ofTrace_ports_eq_of_trace_eq hr hF hG hpos hpos' _ _ htrace

lemma ofSeparated_deleted_eq_of_trace_eq {r : ℕ} (hr : 3 ≤ r) {F G : SimpleHypergraph V}
    {B : Finset V} (hF : F ⊆ completeEdges V r) (hG : G ⊆ completeEdges V r)
    (hpos : ∀ v ∈ B, 0 < vertexDegree F v) (hpos' : ∀ v ∈ B, 0 < vertexDegree G v)
    (hsep : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → ¬ shortBergeConnected F u v)
    (hsep' : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → ¬ shortBergeConnected G u v)
    (htrace : exceptionalTrace B F=exceptionalTrace B G) :
    (ofSeparated hr hF hpos hsep).deleted = (ofSeparated hr hG hpos' hsep').deleted :=
  ofTrace_deleted_eq_of_trace_eq hr hF hG hpos hpos' _ _ htrace
end LooseHamilton.CoreBlockFamily
