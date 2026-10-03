module

public import HittingTimeLooseHamilton.PortContractionCounts

public section

/-! The contraction identities in the original-marker notation of Section 10. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No deletion and reinstating the removed original pair recovers exactly X. -/
theorem port_source_count_eq {r : ℕ} (hr : 3 ≤ r) (M₀ G : Finset (Finset V))
    (y z : V) (hm : {y,z} ∈ M₀) :
    completionCount r (M₀.erase {y,z}) G ∅ {y,z} = unrestrictedCycleCount r M₀ G := by
  unfold completionCount cycleOnCount unrestrictedCycleCount FiniteFamily.count
  congr 1
  ext F
  rw [mem_cycleOnFamily, mem_unrestrictedCycleFamily _ _ _ _ hr]
  simp only [sdiff_empty, insert_erase hm, isMixedCycleOn_univ_iff]

/-- Exact original-port partition indexed by all legal edge/junction labels. -/
theorem original_port_cut_partition {r : ℕ} (hr : 3 ≤ r)
    (M₀ G : Finset (Finset V)) (y z : V) (hyz : y ≠ z)
    (hm : {y,z} ∈ M₀) (hM : (M₀ : Set (Finset V)).PairwiseDisjoint id)
    (hG : G ⊆ allowedEdges r (originalPorts M₀))
    (hsize : 5 * (r-1) < Fintype.card V) :
    unrestrictedCycleCount r M₀ G =
      ∑ l ∈ endpointCutLabelsI r (M₀.erase {y,z}) G ∅ y z,
        rootFreePortCompletion r M₀ G y z l.2 {l.1,z} := by
  rw [← port_source_count_eq hr M₀ G y z hm]
  have hd := port_pair_disjoint_remainder M₀ y z hM hm
  have hM' : ((M₀.erase {y,z} : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id :=
    (fun a ha b hb hab => hM (mem_erase.mp ha).2 (mem_erase.mp hb).2 hab)
  have hy : y ∈ originalPorts M₀ := mem_biUnion.mpr ⟨{y,z},hm,by simp⟩
  have hp : originalPorts (M₀.erase {y,z}) ⊆ originalPorts M₀ := by
    intro v hv
    obtain ⟨m,hm,hv⟩ := mem_biUnion.mp hv
    exact mem_biUnion.mpr ⟨m,(mem_erase.mp hm).2,hv⟩
  rw [port_cut_partition hr hyz hd hM' hy hp hG hsize]
  apply sum_congr rfl
  intro l hl
  exact port_core_count_eq r M₀ G y z l

/-- The fixed incident edge and other-junction count is precisely W_F(P;uz). -/
theorem original_port_incident_count {r : ℕ} (hr : 3 ≤ r)
    (M₀ G : Finset (Finset V)) (y z : V) (hyz : y ≠ z)
    (hm : {y,z} ∈ M₀) (hM : (M₀ : Set (Finset V)).PairwiseDisjoint id)
    (hG : G ⊆ allowedEdges r (originalPorts M₀))
    (hsize : 5 * (r-1) < Fintype.card V)
    (l : EndpointCutLabelI V) (hl : EndpointCutLegalI r (M₀.erase {y,z}) G ∅ y z l) :
    (portIncidentFamily r (M₀.erase {y,z}) G y z l).card =
      rootFreePortCompletion r M₀ G y z l.2 {l.1,z} := by
  rw [← port_core_count_eq]
  apply port_incident_count hr hyz (port_pair_disjoint_remainder M₀ y z hM hm)
    ((fun a ha b hb hab => hM (mem_erase.mp ha).2 (mem_erase.mp hb).2 hab))
    (show y ∈ originalPorts M₀ from mem_biUnion.mpr ⟨{y,z},hm,by simp⟩) _ hG hsize l hl
  intro v hv
  obtain ⟨m,hm,hv⟩ := mem_biUnion.mp hv
  exact mem_biUnion.mpr ⟨m,(mem_erase.mp hm).2,hv⟩

end LooseHamilton
