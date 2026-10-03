module

public import HittingTimeLooseHamilton.CoreBlocks
public import HittingTimeLooseHamilton.CoreMarkerExpansion

public section

/-! Expansion of the actual disjoint exceptional blocks constructed from a host. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CoreBlockFamily
variable {r : ℕ} {F : SimpleHypergraph V} {B : Finset V}

/-- A connected spanning mixed cycle on the retained core expands to a loose
Hamilton cycle of the original host. The expansion is the constructive sequence
of one-marker surgeries proved in `expand_all_markers`. -/
theorem looseHamilton_of_core_cycle (C : CoreBlockFamily r F B) (hr : 3 ≤ r)
    {E : SimpleHypergraph V}
    (hcycle : IsMixedCycleOn r C.coreVertices C.markers E) (hE : E ⊆ F) :
    HasLooseHamiltonCycle r F := by
  apply looseHamiltonCycle_of_expanded_markers hr C.markers C.markerPrivate hcycle
  · exact fun _ hp => C.markerPrivate_card hp
  · exact fun p _ => (C.markerPrivate_outside p).symm
  · exact C.markerPrivate_disjoint
  · exact C.markerPrivate_cover
  · exact hE
  · exact fun _ hp => C.expanded_marker_mem hp
end CoreBlockFamily
end LooseHamilton
