module

public import HittingTimeLooseHamilton.CompletionModels

public section

/-! # Fixed original ports in both endpoint-cut source frames

The host's port prohibition refers to a fixed set `U`, never to changing
markers. In the ordinary source `U = originalPorts M`; in the original-marker
source the only additional surviving original port is the new endpoint `z`.
-/
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Removing one original marker leaves at most its other endpoint unmarked
once its first endpoint has been deleted. -/
theorem originalPorts_erase_marker_subset (M : Finset (Finset V)) (y z : V) :
    (originalPorts M).erase y ⊆ originalPorts (M.erase {y, z}) ∪ {z} := by
  intro v hv
  obtain ⟨hvy, hv⟩ := mem_erase.mp hv
  obtain ⟨m, hm, hvm⟩ := mem_biUnion.mp hv
  by_cases he : m = {y, z}
  · subst m
    have hvz : v = z := by
      rcases mem_insert.mp hvm with h | h
      · exact False.elim (hvy h)
      · exact mem_singleton.mp h
    exact mem_union_right _ (by simp [hvz])
  · exact mem_union_left _ (mem_biUnion.mpr ⟨m, mem_erase.mpr ⟨he, hm⟩, hvm⟩)

/-- Every surviving original port is a marked source vertex. This formulation
covers both manuscript frames and allows further fixed vertex restrictions. -/
structure EndpointSourcePorts (U : Finset V) (M : Finset (Finset V)) (y z : V) : Prop where
  old_ports : originalPorts M ⊆ U
  surviving_ports : U ⊆ originalPorts M ∪ {z}
  root_ordinary : y ∉ U

namespace EndpointSourcePorts
variable {U : Finset V} {M : Finset (Finset V)} {y z : V}

theorem marked_in_source (h : EndpointSourcePorts U M y z) :
    U ⊆ originalPorts (insert {y, z} M) := by
  intro v hv
  rcases mem_union.mp (h.surviving_ports hv) with hm | hz
  · obtain ⟨m, hm, hv⟩ := mem_biUnion.mp hm
    exact mem_biUnion.mpr ⟨m, mem_insert_of_mem hm, hv⟩
  · exact mem_biUnion.mpr ⟨{y, z}, mem_insert_self _ _, mem_insert_of_mem hz⟩

theorem ordinary_frame (M : Finset (Finset V)) (y z : V)
    (hy : y ∉ originalPorts M) : EndpointSourcePorts (originalPorts M) M y z :=
  ⟨Subset.rfl, subset_union_left, hy⟩

/-- The source obtained by deleting one endpoint of an original marker.
The deleted vertex is absent from the ambient host; the surviving fixed ports
are represented by erasing it from the original port set. -/
theorem original_marker_frame (M₀ : Finset (Finset V)) (y₀ z₀ y : V)
    (hM : (M₀ : Set (Finset V)).PairwiseDisjoint id)
    (hm : {y₀, z₀} ∈ M₀)
    (hy : y ∉ (originalPorts M₀).erase y₀) :
    EndpointSourcePorts ((originalPorts M₀).erase y₀) (M₀.erase {y₀, z₀}) y z₀ := by
  refine ⟨?_, originalPorts_erase_marker_subset M₀ y₀ z₀, hy⟩
  intro v hv
  obtain ⟨m, hm', hvm⟩ := mem_biUnion.mp hv
  have hd := hM (mem_erase.mp hm').2 hm (mem_erase.mp hm').1
  refine mem_erase.mpr ⟨?_, mem_biUnion.mpr ⟨m, (mem_erase.mp hm').2, hvm⟩⟩
  intro he
  subst v
  exact disjoint_left.mp hd hvm (by simp)

end EndpointSourcePorts
end LooseHamilton
