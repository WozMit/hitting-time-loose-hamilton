module

public import HittingTimeLooseHamilton.BootstrapPrivateLinkGeometry
public import HittingTimeLooseHamilton.EndpointSourcePorts

public section

/-! The fixed-port hypotheses hold in both actual manuscript source bases. -/
noncomputable section
namespace LooseHamilton.BootstrapEndpointBasePorts
open Finset BootstrapBases
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

theorem mem_ports_restrict (A : Finset V) (markers : SimpleHypergraph V) (v : ↥A) :
    v ∈ originalPorts (restrictEdges A markers) ↔ v.val ∈ originalPorts markers := by
  simp only [originalPorts, restrictEdges, mem_biUnion, mem_image]
  constructor
  · rintro ⟨e, ⟨f,hf,rfl⟩, hv⟩
    exact ⟨f,hf,(mem_restrictEdge A f v).mp hv⟩
  · rintro ⟨f,hf,hv⟩
    exact ⟨restrictEdge A f, ⟨f,hf,rfl⟩, (mem_restrictEdge A f v).mpr hv⟩

theorem ordinary (hM : IsPairMatching M) (P : Finset ↥(active (none : Base M)))
    (y z : ↥(active (none : Base M)))
    (hs : LegalPrivateCompletion r (restrictEdges (active none) (markers hM none)) P {y,z}) :
    EndpointSourcePorts (fixedPorts none) (restrictEdges (active none) (markers hM none)) y z := by
  refine ⟨BootstrapPrivateLinkGeometry.marker_ports_subset hM none, ?_, ?_⟩
  · intro v hv
    apply mem_union_left
    exact (mem_ports_restrict _ _ v).mpr ((mem_fixedPorts none v).mp hv)
  · intro hy
    apply disjoint_left.mp hs.ports_disjoint (show y ∈ P ∪ {y,z} from by simp)
    exact (mem_ports_restrict _ _ y).mpr ((mem_fixedPorts none y).mp hy)

theorem original_port (hM : IsPairMatching M) (a : ↥(originalPorts M))
    (y z : ↥(active (some a)))
    (hz : z.val = OriginalPortPartner.partner hM a) (hy : y ∉ fixedPorts (some a)) :
    EndpointSourcePorts (fixedPorts (some a))
      (restrictEdges (active (some a)) (markers hM (some a))) y z := by
  refine ⟨BootstrapPrivateLinkGeometry.marker_ports_subset hM (some a), ?_, hy⟩
  intro v hv
  have hport := (mem_fixedPorts (some a) v).mp hv
  have hva : v.val ≠ a.val := by
    simpa only [active, deleted, mem_sdiff, mem_univ, mem_singleton, true_and] using v.property
  have hh := originalPorts_erase_marker_subset M a.val (OriginalPortPartner.partner hM a)
    (mem_erase.mpr ⟨hva,hport⟩)
  rcases mem_union.mp hh with hm | hp
  · exact mem_union_left _ ((mem_ports_restrict _ _ v).mpr hm)
  · apply mem_union_right
    apply mem_singleton.mpr
    apply Subtype.ext
    exact (mem_singleton.mp hp).trans hz.symm

end LooseHamilton.BootstrapEndpointBasePorts
