module

public import HittingTimeLooseHamilton.CoreBlocks
public import HittingTimeLooseHamilton.CoreTraceDegree
public import HittingTimeLooseHamilton.CoreExposureData

public section

/-! Deterministic estimates for the exact general-uniformity core. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every exposed edge can be charged to an incidence at a deleted vertex. -/
theorem trace_card_le_degree_sum (D : Finset V) (F : SimpleHypergraph V) :
    (traceOn D F).card ≤ ∑ v ∈ D, vertexDegree F v := by
  have hsub : traceOn D F ⊆ D.biUnion (fun v => F.filter (fun e => v ∈ e)) := by
    intro e he
    obtain ⟨he,hd⟩ := (mem_traceOn _ _ _).mp he
    obtain ⟨v,hve,hvD⟩ := not_disjoint_iff.mp hd
    exact mem_biUnion.mpr ⟨v,hvD,mem_filter.mpr ⟨he,hve⟩⟩
  exact (card_le_card hsub).trans card_biUnion_le

namespace CoreBlockFamily
variable {r : ℕ} {F : SimpleHypergraph V}

/-- Proposition 3.3's pointwise residual trace-degree bound on Lemma 3.2's event. -/
theorem trace_degree_bound (C : CoreBlockFamily r F (lowDegreeVertices F))
    {K : ℝ} (hgood : exceptionalSetGood r K F) (w : V) (hw : w ∈ C.coreVertices) :
    vertexDegree (traceOn C.deleted F) w ≤ 2*(r-2) := by
  exact trace_degree_le_two_private_size C.edge C.privateBlock C.edge_mem
    C.anchor_private C.privateBlock_subset hgood.separated
    (fun v => (C.privateBlock_card v).le) hgood.pair_degree (mem_sdiff.mp hw).2

/-- The total number of exposed edges is at most the deleted-vertex incidence sum. -/
theorem trace_card_bound (C : CoreBlockFamily r F (lowDegreeVertices F))
    (hgood : exceptionalSetGood r 20 F) :
    ((traceOn C.deleted F).card : ℝ) ≤
      20 * (r-2 : ℕ) * (lowDegreeVertices F).card * Real.log (Fintype.card V : ℝ) := by
  calc
    ((traceOn C.deleted F).card : ℝ) ≤ (∑ v ∈ C.deleted, vertexDegree F v : ℕ) := by
      exact_mod_cast trace_card_le_degree_sum C.deleted F
    _ = ∑ v ∈ C.deleted, (vertexDegree F v : ℝ) := by simp
    _ ≤ ∑ _v ∈ C.deleted, 20 * Real.log (Fintype.card V : ℝ) :=
      sum_le_sum (fun v _ => hgood.max_degree v)
    _ = _ := by simp only [sum_const,nsmul_eq_mul,C.deleted_card,Nat.cast_mul]; ring

/-- The actual induced core belongs to the entire degree-conditioned family. -/
theorem actual_core_mem (C : CoreBlockFamily r F (lowDegreeVertices F))
    (hF : F ⊆ completeEdges V r) (hNI : NoIsolated F) :
    coreOutside C.deleted F ∈ coreCompletionFamily r F.card C.deleted (traceOn C.deleted F) := by
  apply coreOutside_mem_completion C.anchors_deleted
  exact (mem_coreExposureFiber _ _ _ _ _ _).mpr ⟨hF,rfl,hNI,rfl,rfl⟩
end CoreBlockFamily
end LooseHamilton
