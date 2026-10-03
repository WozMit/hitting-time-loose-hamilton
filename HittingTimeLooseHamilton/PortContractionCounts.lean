module

public import HittingTimeLooseHamilton.PortContractionPartition

public section

/-! Exact counts for a fixed ordinary edge and its other junction at an
original port. The source family consists of actual ordinary edge sets. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G : Finset (Finset V)} {U : Finset V} {y z : V}

@[expose] def portIncidentFamily (r : ℕ) (M G : Finset (Finset V)) (y z : V)
    (l : EndpointCutLabelI V) : Finset (Finset (Finset V)) := by
  classical
  exact (completionFamily r M G ∅ {y,z}).filter (fun F =>
    l.edge y ∈ F ∧ edgeEndpointPair (insert {y,z} M) F (l.edge y) = {y,l.1})

/-- Contraction of the original pair and its incident edge is a bijection for
fixed edge/private-block and other-junction labels. -/
theorem port_incident_count (hr : 3 ≤ r) (hyz : y ≠ z)
    (hd : Disjoint ({y,z} : Finset V) (originalPorts M))
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (hy : y ∈ U) (hports : originalPorts M ⊆ U) (hG : G ⊆ allowedEdges r U)
    (hsize : 5 * (r-1) < Fintype.card V)
    (l : EndpointCutLabelI V) (hl : EndpointCutLegalI r M G ∅ y z l) :
    (portIncidentFamily r M G y z l).card = (endpointCutCoreFamilyI r M G ∅ y z l).card := by
  classical
  symm
  apply card_bij (fun F _ => insert (l.edge y) F)
  · intro F hF
    obtain ⟨hsource,hrole⟩ := portCut_expand_I hr hyz hd hM hl hF
    exact mem_filter.mpr ⟨hsource, mem_insert_self _ _, hrole⟩
  · intro F hF F' hF' heq
    exact endpointCutCoreI_output_recovery hF hF' rfl heq
  · intro F hF
    obtain ⟨hsource,hedge,hrole⟩ := mem_filter.mp hF
    have hc := portCut_contraction hr hyz hd hy hports hG hsize F hsource
    rcases hc with ⟨k,hk,F',hF',heq⟩ | ⟨k,hk,_⟩
    · obtain ⟨⟨C⟩,_⟩ := (mem_completionFamily _ _ _ _ _ _).mp hsource
      have hkrole := (portCut_expand_I hr hyz hd hM hk hF').2
      rw [heq] at hkrole
      have hke : k.edge y ∈ F := by rw [← heq]; simp
      have hlk := endpointCutLabelI_joint_recovery C hl hk hedge hke hrole hkrole
      subst k
      exact ⟨F',hF',heq⟩
    · exact False.elim (portCut_no_typeII hy hports hG hd k hk)

omit [Fintype V] in
/-- An original matching pair is disjoint from all remaining ports. -/
theorem port_pair_disjoint_remainder (M₀ : Finset (Finset V)) (y z : V)
    (hM : (M₀ : Set (Finset V)).PairwiseDisjoint id) (hm : {y,z} ∈ M₀) :
    Disjoint ({y,z} : Finset V) (originalPorts (M₀.erase {y,z})) := by
  apply disjoint_left.mpr
  intro v hv hp
  obtain ⟨m,hm',hvm⟩ := mem_biUnion.mp hp
  exact disjoint_left.mp (hM hm (mem_erase.mp hm').2 (mem_erase.mp hm').1.symm) hv hvm

/-- The contracted core is exactly the deleted-original-port completion from
item 32, including its vertex set and removed original marker. -/
theorem port_core_count_eq (r : ℕ) (M₀ G : Finset (Finset V)) (y z : V)
    (l : EndpointCutLabelI V) :
    (endpointCutCoreFamilyI r (M₀.erase {y,z}) G ∅ y z l).card =
      rootFreePortCompletion r M₀ G y z l.2 {l.1,z} := by
  rw [rootFreePortCompletion_eq]
  unfold endpointCutCoreFamilyI cycleOnCount EndpointCutLabelI.markers
  congr 2
  ext v
  simp [EndpointCutLabelI.deleted, and_assoc]

end LooseHamilton
