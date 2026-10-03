module

public import HittingTimeLooseHamilton.PortContractionGeometry

public section

/-! Exact contraction partition at an original marked port. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G : Finset (Finset V)} {U : Finset V} {y z : V}

theorem portCut_contraction (hr : 3 ≤ r) (hyz : y ≠ z)
    (hd : Disjoint ({y,z} : Finset V) (originalPorts M))
    (hy : y ∈ U) (hports : originalPorts M ⊆ U) (hG : G ⊆ allowedEdges r U)
    (hsize : 5 * (r-1) < Fintype.card V) :
    EndpointCutContractionProperty r M G ∅ y z := by
  intro F hF
  obtain ⟨⟨C⟩,hFG⟩ := (mem_completionFamily _ _ _ _ _ _).mp hF
  have hzy : z ≠ y := Ne.symm hyz
  obtain ⟨D,h₀,hz,hy'⟩ := C.exists_rooted ⟨{y,z}, mem_insert_self _ _⟩ z y
    (by simp [pair_comm]) hzy
  have hn := D.six_le_length_of_active_card hr (by simpa using hsize)
  have hyM : y ∉ originalPorts M := fun h => disjoint_left.mp hd (by simp) h
  have hports' := EndpointSourcePorts.ordinary_frame M y z hyM
  have hG' : G ⊆ allowedEdges r (originalPorts M) := by
    intro e he
    obtain ⟨hcard,hbound⟩ := (mem_allowedEdges r U e).mp (hG he)
    apply (mem_allowedEdges r (originalPorts M) e).mpr
    exact ⟨hcard, (card_le_card (inter_subset_inter_left hports)).trans hbound⟩
  obtain ⟨e,he,hcases⟩ := D.select_endpoint_cut hn (originalPorts M) G hports' hG' hFG h₀ hz hy'
  have hI : EndpointCutLegalI r M G ∅ y z (D.junction ⟨2,by omega⟩,D.privateBlock e) := by
    rcases hcases with hI | ⟨m,f,hm,hf,hII⟩
    · exact hI
    · exact False.elim (portCut_no_typeII hy hports hG hd _ hII)
  have hroot := endpoint_source_pair_fresh (portSource_geometry hyz hd)
  have hM : (M : Set (Finset V)).PairwiseDisjoint id := by
    intro m hm n hn hmn
    exact D.marked_matching (mem_insert_of_mem hm) (mem_insert_of_mem hn) hmn
  have hmatch := endpointCut_replacement_matching (portSource_geometry hyz hd) hM hI.endpoint_fresh
  have hcore := D.endpointCutOne hn e h₀ he hz hy' hroot (endpointCutI_marker_fresh hI) hmatch
  have heval : e.val = {y,D.junction ⟨2,by omega⟩} ∪ D.privateBlock e := by
    have hh := D.slot_edge ⟨1,by omega⟩
    rw [he] at hh
    simpa only [MixedCycleOnWitness.rotate_mk_succ (n := D.length) (k := 1) (by omega), hy'] using hh
  left
  refine ⟨(D.junction ⟨2,by omega⟩,D.privateBlock e),hI,F.erase e.val,?_,?_⟩
  · apply (mem_endpointCutCoreFamilyI _ _ _ _ _ _ _ _).mpr
    exact ⟨⟨hcore⟩, fun f hf => hFG (mem_erase.mp hf).2⟩
  · change insert ({y,D.junction ⟨2,by omega⟩} ∪ D.privateBlock e) (F.erase e.val) = F
    rw [← heval, insert_erase e.property]

/-- Every source cycle is counted once, by its incident ordinary edge and
other junction. No orientation multiplicity is present. -/
theorem port_cut_partition (hr : 3 ≤ r) (hyz : y ≠ z)
    (hd : Disjoint ({y,z} : Finset V) (originalPorts M))
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (hy : y ∈ U) (hports : originalPorts M ⊆ U) (hG : G ⊆ allowedEdges r U)
    (hsize : 5 * (r-1) < Fintype.card V) :
    completionCount r M G ∅ {y,z} =
      ∑ l ∈ endpointCutLabelsI r M G ∅ y z,
        (endpointCutCoreFamilyI r M G ∅ y z l).card := by
  have hx : EndpointCutExpansionProperties r M G ∅ y z := by
    constructor
    · intro l hl F hF
      exact portCut_expand_I hr hyz hd hM hl hF
    · intro l hl
      exact False.elim (portCut_no_typeII hy hports hG hd l hl)
  have h := endpointCut_partition_of_surgeries hx
    (portCut_contraction hr hyz hd hy hports hG hsize) hM
    (fun h => disjoint_left.mp hd (by simp) h)
  have hemp : endpointCutLabelsII r M G ∅ y z = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro l hl
    exact portCut_no_typeII hy hports hG hd l ((mem_endpointCutLabelsII _ _ _ _ _ _ _).mp hl)
  simpa only [hemp, sum_empty, add_zero] using h

end LooseHamilton
