module

public import HittingTimeLooseHamilton.Models

public section

/-! # Elementary host operations
Vertex restriction changes the vertex type. The original port set is pulled back
along that restriction; it is never recomputed from auxiliary markers.
-/
noncomputable section
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Maximum vertex degree, with value zero on an empty vertex universe. -/
@[expose] def maxVertexDegree (H : SimpleHypergraph V) : ℕ :=
  Finset.univ.sup (vertexDegree H)

/-- Maximum pair degree over distinct vertices. -/
@[expose] def maxPairDegree (H : SimpleHypergraph V) : ℕ :=
  (Finset.univ.filter (fun p : V × V => p.1 ≠ p.2)).sup
    (fun p => pairDegree H p.1 p.2)

/-- Deleting an edge leaves the vertex type unchanged. -/
@[expose] def deleteEdge (H : SimpleHypergraph V) (e : Finset V) : SimpleHypergraph V := H.erase e

/-- Forget the subtype labels on an edge in a surviving vertex set. -/
@[expose] def ambientEdge (S : Finset V) (e : Finset ↥S) : Finset V :=
  e.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem ambientEdge_card (S : Finset V) (e : Finset ↥S) :
    (ambientEdge S e).card = e.card := Finset.card_map _

/-- Induced host on S: precisely the edges whose vertices all survive. -/
@[expose] def inducedHost (S : Finset V) (H : SimpleHypergraph V) : SimpleHypergraph ↥S :=
  Finset.univ.filter (fun e => ambientEdge S e ∈ H)

@[simp] theorem mem_inducedHost (S : Finset V) (H : SimpleHypergraph V)
    (e : Finset ↥S) : e ∈ inducedHost S H ↔ ambientEdge S e ∈ H := by
  simp [inducedHost]

/-- The surviving original ports; changing markers does not change this set. -/
@[expose] def restrictedPorts (S ports : Finset V) : Finset ↥S :=
  Finset.univ.filter (fun v => v.val ∈ ports)

@[simp] theorem mem_restrictedPorts (S ports : Finset V) (v : ↥S) :
    v ∈ restrictedPorts S ports ↔ v.val ∈ ports := by simp [restrictedPorts]

/-- Vertex deletion removes every edge incident with a deleted vertex. -/
@[expose] def deleteVertices (D : Finset V) (H : SimpleHypergraph V) :
    SimpleHypergraph ↥(Finset.univ \ D) := inducedHost (Finset.univ \ D) H

theorem inducedHost_uniform {r : ℕ} {H : SimpleHypergraph V}
    (hH : H ⊆ completeEdges V r) (S : Finset V) :
    inducedHost S H ⊆ completeEdges ↥S r := by
  intro e he
  apply (mem_completeEdges r e).mpr
  have h := (mem_completeEdges r _).mp (hH ((mem_inducedHost S H e).mp he))
  simpa using h

theorem ambientEdge_inter_ports (S ports : Finset V) (e : Finset ↥S) :
    ambientEdge S (e ∩ restrictedPorts S ports) = ambientEdge S e ∩ ports := by
  ext v
  simp only [ambientEdge, Finset.mem_map, Function.Embedding.coeFn_mk,
    Finset.mem_inter, mem_restrictedPorts]
  constructor
  · rintro ⟨x, ⟨hx, hp⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, hp⟩
  · rintro ⟨⟨x, hx, rfl⟩, hp⟩
    exact ⟨x, ⟨hx, hp⟩, rfl⟩

/-- The fixed-port prohibition commutes with restricting the vertex universe. -/
theorem inducedHost_allowed (r : ℕ) (S ports : Finset V) :
    inducedHost S (allowedEdges r ports) = allowedEdges r (restrictedPorts S ports) := by
  ext e
  simp only [mem_inducedHost, mem_allowedEdges, ambientEdge_card]
  rw [← ambientEdge_inter_ports, ambientEdge_card]

end LooseHamilton
