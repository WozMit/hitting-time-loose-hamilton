module

public import HittingTimeLooseHamilton.SequentialCompletionDecoding
public import HittingTimeLooseHamilton.BootstrapEndpointBasePorts

public section

/-! Static source gates for the original, undeleted base. -/
noncomputable section
namespace LooseHamilton.SequentialCompletion
open Finset BootstrapBases
variable {V : Type} [Fintype V] [DecidableEq V] {M : Finset (Finset V)}

theorem ordinary_fixedPorts (hM : IsPairMatching M) :
    fixedPorts (none : Base M) = originalPorts (restrictEdges (active none) (markers hM none)) := by
  ext v
  rw [mem_fixedPorts, BootstrapEndpointBasePorts.mem_ports_restrict]
  rfl

theorem ordinary_source_ports {d r : ℕ} (hM : IsPairMatching M)
    (s : State ↥(active (none : Base M)) d)
    (hs : s.Valid (r := r) (restrictEdges (active none) (markers hM none))) :
    EndpointSourcePorts (fixedPorts none) (restrictEdges (active none) (markers hM none))
      s.first s.second := BootstrapEndpointBasePorts.ordinary hM s.block s.first s.second hs.2

end LooseHamilton.SequentialCompletion
