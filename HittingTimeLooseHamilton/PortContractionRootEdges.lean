module

public import HittingTimeLooseHamilton.PortContractionLinkSum

public section

/-! Transfer the unordered-link identity to the root-edge representation used
by the registered sampling tests. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Deleting the unique original port from an allowed incident edge yields a
link disjoint from the fixed original port set. -/
theorem port_edge_erase_mem {r : ℕ} {G : Finset (Finset V)} {U : Finset V} {y : V}
    (hy : y ∈ U) (hG : G ⊆ allowedEdges r U) {e : Finset V} (he : e ∈ G) (hye : y ∈ e) :
    e.erase y ∈ portLinkSets G U y := by
  classical
  apply mem_filter.mpr
  refine ⟨mem_univ _, by simpa only [insert_erase hye] using he, ?_⟩
  apply disjoint_left.mpr
  intro v hv hvU
  obtain ⟨hvy,hve⟩ := mem_erase.mp hv
  have hs : ({v,y} : Finset V) ⊆ e ∩ U := by
    intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact mem_inter.mpr ⟨hve,hvU⟩
    · exact mem_singleton.mp ha ▸ mem_inter.mpr ⟨hye,hy⟩
  have hcard := card_le_card hs
  rw [card_pair hvy] at hcard
  have hbound := ((mem_allowedEdges r U e).mp (hG he)).2
  omega

/-- Link sums and full root-edge sums count exactly the same objects. -/
theorem portLink_sum_rootEdges {r : ℕ} (G : Finset (Finset V)) (U : Finset V) (y : V)
    (hy : y ∈ U) (hG : G ⊆ allowedEdges r U) (f : Finset V → ℕ) :
    ∑ A ∈ portLinkSets G U y, f A = ∑ e ∈ G.filter (y ∈ ·), f (e.erase y) := by
  classical
  apply sum_bij (fun A _ => insert y A)
  · intro A hA
    obtain ⟨_,he,hd⟩ := mem_filter.mp hA
    exact mem_filter.mpr ⟨he,mem_insert_self _ _⟩
  · intro A hA B hB heq
    have hyA : y ∉ A := fun h => disjoint_left.mp (mem_filter.mp hA).2.2 h hy
    have hyB : y ∉ B := fun h => disjoint_left.mp (mem_filter.mp hB).2.2 h hy
    have hh := congrArg (fun e : Finset V => e.erase y) heq
    simpa only [erase_insert hyA, erase_insert hyB] using hh
  · intro e he
    obtain ⟨he,hye⟩ := mem_filter.mp he
    exact ⟨e.erase y,port_edge_erase_mem hy hG he hye,insert_erase hye⟩
  · intro A hA
    have hyA : y ∉ A := fun h => disjoint_left.mp (mem_filter.mp hA).2.2 h hy
    rw [erase_insert hyA]

/-- The number of port links is the actual root degree. -/
theorem portLink_card {r : ℕ} (G : Finset (Finset V)) (U : Finset V) (y : V)
    (hy : y ∈ U) (hG : G ⊆ allowedEdges r U) :
    (portLinkSets G U y).card = vertexDegree G y := by
  simpa [vertexDegree] using portLink_sum_rootEdges G U y hy hG (fun _ => 1)

/-- Equation (portidentity) expressed using the same full root edges as the
third registered link test. -/
theorem original_port_partition_rootEdges {r : ℕ} (hr : 3 ≤ r)
    (M₀ G : Finset (Finset V)) (y z : V) (hyz : y ≠ z)
    (hm : {y,z} ∈ M₀) (hM : (M₀ : Set (Finset V)).PairwiseDisjoint id)
    (hG : G ⊆ allowedEdges r (originalPorts M₀))
    (hsize : 5 * (r-1) < Fintype.card V) :
    unrestrictedCycleCount r M₀ G =
      ∑ e ∈ G.filter (y ∈ ·), rootFreePortScore r M₀ G y z (e.erase y) := by
  rw [original_port_partition hr M₀ G y z hyz hm hM hG hsize]
  exact portLink_sum_rootEdges G (originalPorts M₀) y
    (mem_biUnion.mpr ⟨{y,z},hm,by simp⟩) hG (rootFreePortScore r M₀ G y z)

end LooseHamilton
