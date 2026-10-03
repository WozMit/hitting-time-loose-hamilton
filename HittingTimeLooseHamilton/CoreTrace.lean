module

public import HittingTimeLooseHamilton.ExceptionalSetModels

public section

/-! Exact trace/core decomposition after deleting a prescribed vertex set. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def traceOn (D : Finset V) (F : SimpleHypergraph V) : SimpleHypergraph V :=
  F.filter (fun e => ¬ Disjoint e D)

@[expose] def coreOutside (D : Finset V) (F : SimpleHypergraph V) : SimpleHypergraph V :=
  F.filter (fun e => Disjoint e D)

@[simp] theorem mem_traceOn (D : Finset V) (F : SimpleHypergraph V) (e : Finset V) :
    e ∈ traceOn D F ↔ e ∈ F ∧ ¬ Disjoint e D := by simp [traceOn]
@[simp] theorem mem_coreOutside (D : Finset V) (F : SimpleHypergraph V) (e : Finset V) :
    e ∈ coreOutside D F ↔ e ∈ F ∧ Disjoint e D := by simp [coreOutside]

theorem trace_core_union (D : Finset V) (F : SimpleHypergraph V) :
    traceOn D F ∪ coreOutside D F = F := by
  ext e
  simp only [mem_union, mem_traceOn, mem_coreOutside]
  tauto

theorem trace_core_disjoint (D : Finset V) (F : SimpleHypergraph V) :
    Disjoint (traceOn D F) (coreOutside D F) := by
  apply disjoint_left.mpr
  intro e he ht
  exact (mem_traceOn _ _ _).mp he |>.2 ((mem_coreOutside _ _ _).mp ht).2

theorem vertexDegree_union {T G : SimpleHypergraph V} (h : Disjoint T G) (v : V) :
    vertexDegree (T ∪ G) v = vertexDegree T v + vertexDegree G v := by
  unfold vertexDegree
  rw [filter_union, card_union_of_disjoint (h.mono (filter_subset _ _) (filter_subset _ _))]

theorem trace_degree_add_core (D : Finset V) (F : SimpleHypergraph V) (v : V) :
    vertexDegree (traceOn D F) v + vertexDegree (coreOutside D F) v = vertexDegree F v := by
  rw [← vertexDegree_union (trace_core_disjoint D F), trace_core_union]

theorem coreOutside_card (D : Finset V) (F : SimpleHypergraph V) :
    (coreOutside D F).card = F.card - (traceOn D F).card := by
  have h := card_union_of_disjoint (trace_core_disjoint D F)
  rw [trace_core_union] at h
  omega

theorem coreOutside_degree_deleted {D : Finset V} (F : SimpleHypergraph V) {v : V}
    (hv : v ∈ D) : vertexDegree (coreOutside D F) v = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he, hve⟩ := mem_filter.mp he
  exact disjoint_left.mp ((mem_coreOutside _ _ _).mp he).2 hve hv

theorem trace_degree_deleted {D : Finset V} (F : SimpleHypergraph V) {v : V}
    (hv : v ∈ D) : vertexDegree (traceOn D F) v = vertexDegree F v := by
  have h := trace_degree_add_core D F v
  rw [coreOutside_degree_deleted F hv, add_zero] at h
  exact h

theorem traceOn_mono_vertices {B D : Finset V} (hBD : B ⊆ D) (F : SimpleHypergraph V) :
    traceOn B F ⊆ traceOn D F := by
  intro e he
  obtain ⟨he,hn⟩ := (mem_traceOn _ _ _).mp he
  exact (mem_traceOn _ _ _).mpr ⟨he, fun hd => hn (hd.mono_right hBD)⟩

theorem traceOn_trace {B D : Finset V} (hBD : B ⊆ D) (F : SimpleHypergraph V) :
    traceOn B (traceOn D F) = traceOn B F := by
  ext e
  simp only [mem_traceOn]
  constructor
  · rintro ⟨⟨he,_⟩,hb⟩; exact ⟨he,hb⟩
  · rintro ⟨he,hb⟩
    exact ⟨(mem_traceOn _ _ _).mp (traceOn_mono_vertices hBD F ((mem_traceOn _ _ _).mpr ⟨he,hb⟩)),hb⟩

/-- The residual lower bound in Proposition 3.3; natural subtraction is the
paper's maximum with zero. -/
@[expose] def coreLowerBound (D : Finset V) (T : SimpleHypergraph V) (v : V) : ℕ :=
  lowerDegreeBase V + 1 - vertexDegree T v

/-- Original critical edges are determined entirely by the exposed low vertices. -/
@[expose] def exposedCriticalEdges (B : Finset V) (T : SimpleHypergraph V) : SimpleHypergraph V :=
  T.filter (fun e => ∃ v ∈ B, v ∈ e ∧ vertexDegree T v = 1)

theorem criticalEdges_eq_exposed {D B : Finset V} {F : SimpleHypergraph V}
    (hbase : 1 ≤ lowerDegreeBase V) (hB : lowDegreeVertices F = B) (hBD : B ⊆ D) :
    criticalEdges F = exposedCriticalEdges B (traceOn D F) := by
  ext e
  simp only [mem_criticalEdges, exposedCriticalEdges, mem_filter]
  constructor
  · rintro ⟨he,v,hve,hv⟩
    have hvB : v ∈ B := by
      rw [← hB, mem_lowDegreeVertices]
      omega
    have hvD := hBD hvB
    have htrace : e ∈ traceOn D F := (mem_traceOn _ _ _).mpr
      ⟨he, fun hd => disjoint_left.mp hd hve hvD⟩
    exact ⟨htrace,v,hvB,hve,by rw [trace_degree_deleted F hvD,hv]⟩
  · rintro ⟨he,v,hvB,hve,hv⟩
    exact ⟨((mem_traceOn _ _ _).mp he).1,v,hve,by
      rw [trace_degree_deleted F (hBD hvB)] at hv
      exact hv⟩
end LooseHamilton
