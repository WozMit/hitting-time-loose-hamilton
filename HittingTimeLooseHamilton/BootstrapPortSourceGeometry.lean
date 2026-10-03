module

public import HittingTimeLooseHamilton.BootstrapBases
public import HittingTimeLooseHamilton.EndpointSourcePorts

public section

/-! # Geometry of a completion obtained by deleting an original port
The raw source data identify the canonical deletion base and show that its
private vertices and moving endpoint avoid all original ports.
-/
noncomputable section
namespace LooseHamilton.BootstrapPortSourceGeometry
open Finset BootstrapBases
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)} {P : Finset V} {y z u : V}

omit [Fintype V] in
theorem chosen_port_mem (hm : {y,z} ∈ M) : y ∈ originalPorts M :=
  mem_biUnion.mpr ⟨{y,z}, hm, by simp⟩

omit [Fintype V] in
theorem partner_eq (hM : IsPairMatching M) (hyz : y ≠ z) (hm : {y,z} ∈ M) :
    z = OriginalPortPartner.partner hM ⟨y, chosen_port_mem hm⟩ :=
  OriginalPortPartner.partner_unique hM _ hyz.symm hm

theorem private_subset_active (hm : {y,z} ∈ M) (hy : y ∉ P ∪ {u,z}) :
    P ⊆ active (some (⟨y, chosen_port_mem hm⟩ : ↥(originalPorts M))) := by
  intro v hv
  simp only [active, deleted, mem_sdiff, mem_univ, mem_singleton, true_and]
  intro he
  subst v
  exact hy (mem_union_left _ hv)

theorem root_mem_active (hm : {y,z} ∈ M) (hy : y ∉ P ∪ {u,z}) :
    u ∈ active (some (⟨y, chosen_port_mem hm⟩ : ↥(originalPorts M))) := by
  simp only [active, deleted, mem_sdiff, mem_univ, mem_singleton, true_and]
  intro he
  subst u
  exact hy (by simp)

theorem partner_mem_active (hyz : y ≠ z) (hm : {y,z} ∈ M) :
    z ∈ active (some (⟨y, chosen_port_mem hm⟩ : ↥(originalPorts M))) := by
  simpa [active, deleted] using hyz.symm

theorem private_disjoint_originalPorts
    (hs : LegalPrivateCompletion r (M.erase {y,z}) P {u,z})
    (hy : y ∉ P ∪ {u,z}) : Disjoint P (originalPorts M) := by
  apply disjoint_left.mpr
  intro v hv hport
  have hvy : v ≠ y := by
    intro he
    subst v
    exact hy (mem_union_left _ hv)
  have hsurv := originalPorts_erase_marker_subset M y z (mem_erase.mpr ⟨hvy,hport⟩)
  rcases mem_union.mp hsurv with hrem | hz
  · exact disjoint_left.mp hs.ports_disjoint (mem_union_left _ hv) hrem
  · exact disjoint_left.mp hs.private_pair_disjoint hv (mem_insert_of_mem hz)

theorem root_not_mem_originalPorts
    (hs : LegalPrivateCompletion r (M.erase {y,z}) P {u,z})
    (hy : y ∉ P ∪ {u,z}) : u ∉ originalPorts M := by
  intro hport
  have huy : u ≠ y := by
    intro he
    subst u
    exact hy (by simp)
  have huz : u ≠ z := by
    intro he
    have := hs.pair_card
    simp [he] at this
  have hsurv := originalPorts_erase_marker_subset M y z (mem_erase.mpr ⟨huy,hport⟩)
  rcases mem_union.mp hsurv with hrem | hz
  · exact disjoint_left.mp hs.ports_disjoint (by simp) hrem
  · exact huz (mem_singleton.mp hz)

omit [Fintype V] in
theorem residual_markers_eq (hM : IsPairMatching M) (hyz : y ≠ z)
    (hm : {y,z} ∈ M) :
    markers hM (some (⟨y, chosen_port_mem hm⟩ : ↥(originalPorts M))) = M.erase {y,z} := by
  simp only [markers_some, ← partner_eq hM hyz hm]

end LooseHamilton.BootstrapPortSourceGeometry
