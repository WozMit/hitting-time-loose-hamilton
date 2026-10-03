module

public import HittingTimeLooseHamilton.EndpointExpansionOne
public import HittingTimeLooseHamilton.EndpointExpansionThree
public import HittingTimeLooseHamilton.EndpointExpansionLegal
public import HittingTimeLooseHamilton.EndpointCutCoreFacts

public section

/-! The inverse maps on the independent, unrestricted actual-edge-set core families. -/
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G : Finset (Finset V)} {P : Finset V} {y z : V}

theorem endpointCut_expand_I (hr : 3 ≤ r)
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    {l : EndpointCutLabelI V} (hl : EndpointCutLegalI r M G P y z l)
    {F : Finset (Finset V)} (hF : F ∈ endpointCutCoreFamilyI r M G P y z l) :
    insert (l.edge y) F ∈ completionFamily r M G P {y,z} ∧
      edgeEndpointPair (insert {y,z} M) (insert (l.edge y) F) (l.edge y) = {y,l.1} := by
  obtain ⟨⟨C₀⟩,hFG⟩ := (mem_endpointCutCoreFamilyI _ _ _ _ _ _ _ _).mp hF
  have C : MixedCycleOnWitness r (univ \ (P ∪ l.deleted y)) (insert {z,l.1} M) F := by
    simpa only [EndpointCutLabelI.markers, pair_comm l.1 z] using C₀
  have hza : z ≠ l.1 := by
    intro h
    exact hl.endpoint_fresh (mem_union_right _ (by simp [h]))
  obtain ⟨D,hD0,hDz,hDa⟩ := C.exists_rooted ⟨{z,l.1},mem_insert_self _ _⟩ z l.1 rfl hza
  have hp : {z,l.1} ∉ M := by
    intro hm
    apply endpointCutI_marker_fresh hl
    exact mem_insert_of_mem (by simpa only [pair_comm z l.1] using hm)
  have hq : {z,y} ∉ M := by
    simpa only [pair_comm z y] using endpoint_source_pair_fresh hs
  have he : {y,l.1} ∪ l.2 ∉ F := endpointCutCoreI_edge_not_mem hF
  have hMM : (↑(insert {z,y} M) : Set (Finset V)).PairwiseDisjoint id := by
    simpa only [pair_comm z y] using endpoint_source_matching hs hM
  let D' := D.insertOnePath hp hq he hD0 hDz hDa hl.y_not_core
    hl.private_core_disjoint hl.y_not_private hl.private_card hMM
  constructor
  · apply (mem_completionFamily _ _ _ _ _ _).mpr
    constructor
    · refine ⟨?_⟩
      simpa only [hl.restore_active hs, pair_comm z y, EndpointCutLabelI.edge] using D'
    · exact insert_subset hl.edge_mem hFG
  · have h := D.insertOnePath_endpoint_role hr hp hq he hD0 hDz hDa hl.y_not_core
      hl.private_core_disjoint hl.y_not_private hl.private_card hMM
    simpa only [pair_comm z y, EndpointCutLabelI.edge] using h

theorem endpointCut_expand_II (hr : 3 ≤ r)
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    {l : EndpointCutLabelII V} (hl : EndpointCutLegalII r M G P y z l)
    {F : Finset (Finset V)} (hF : F ∈ endpointCutCoreFamilyII r M G P y z l) :
    insert (l.firstEdge y) (insert l.secondEdge F) ∈ completionFamily r M G P {y,z} ∧
      edgeEndpointPair (insert {y,z} M) (insert (l.firstEdge y) (insert l.secondEdge F))
        (l.firstEdge y) = {y,l.1} ∧
      edgeEndpointPair (insert {y,z} M) (insert (l.firstEdge y) (insert l.secondEdge F))
        l.secondEdge = {l.2.1,l.2.2.1} := by
  obtain ⟨⟨C₀⟩,hFG⟩ := (mem_endpointCutCoreFamilyII _ _ _ _ _ _ _ _).mp hF
  have C : MixedCycleOnWitness r (univ \ (P ∪ l.deleted y))
      (insert {z,l.2.2.1} (M.erase l.oldMarker)) F := by
    simpa only [EndpointCutLabelII.markers, pair_comm l.2.2.1 z] using C₀
  have hza : z ≠ l.2.2.1 := by
    intro h
    exact hl.endpoint_fresh (mem_union_right _ (by simp [h]))
  obtain ⟨D,hD0,hDz,hDa⟩ := C.exists_rooted ⟨{z,l.2.2.1},mem_insert_self _ _⟩ z l.2.2.1 rfl hza
  have hp : {z,l.2.2.1} ∉ M.erase l.oldMarker := by
    intro hm
    apply endpointCutII_marker_fresh hl
    exact mem_insert_of_mem (by simpa only [pair_comm z l.2.2.1] using (erase_subset _ _ hm))
  have hqM : {z,y} ∉ M := by
    simpa only [pair_comm z y] using endpoint_source_pair_fresh hs
  have hq : {z,y} ∉ M.erase l.oldMarker := fun h => hqM (erase_subset _ _ h)
  have ho : {l.1,l.2.1} ∉ insert {z,y} (M.erase l.oldMarker) := by
    intro h
    rcases mem_insert.mp h with h | h
    · exact hqM (h ▸ hl.oldMarker_mem)
    · exact notMem_erase _ _ h
  have he₂ : {l.2.1,l.2.2.1} ∪ l.2.2.2.2 ∉ F :=
    (endpointCutCoreII_edges_not_mem hF).2
  have hyv : y ≠ l.2.1 := by
    intro h
    have hh : (0 : Fin 3) = 2 := hl.added_injective hs (by simpa using h)
    have hval := congrArg Fin.val hh
    norm_num at hval
  have hya : y ≠ l.2.2.1 := by
    intro h
    exact hl.endpoint_fresh (mem_union_right _ (by simp [h]))
  have hyR₂ : y ∉ l.2.2.2.2 := by simpa using hl.added_not_private 0 1
  have he₁₂ : ({y,l.1} ∪ l.2.2.2.1 : Finset V) ≠ {l.2.1,l.2.2.1} ∪ l.2.2.2.2 := by
    intro h
    have hy : y ∈ ({l.2.1,l.2.2.1} ∪ l.2.2.2.2 : Finset V) := h ▸ (by simp)
    simpa [hyv,hya,hyR₂] using hy
  have he₁ : {y,l.1} ∪ l.2.2.2.1 ∉ insert ({l.2.1,l.2.2.1} ∪ l.2.2.2.2) F := by
    simp only [mem_insert, not_or]
    exact ⟨he₁₂,(endpointCutCoreII_edges_not_mem hF).1⟩
  have hmRestore : insert {l.1,l.2.1} (M.erase l.oldMarker) = M :=
    insert_erase hl.oldMarker_mem
  have hMM : (↑(insert {z,y} (insert {l.1,l.2.1} (M.erase l.oldMarker))) :
      Set (Finset V)).PairwiseDisjoint id := by
    simpa only [hmRestore,
      pair_comm z y] using endpoint_source_matching hs hM
  let D' := D.insertThreePath hp hq ho he₂ he₁ hD0 hDz hDa (hl.added_injective hs)
    hl.added_not_core hl.private_cards hl.private_pairwise hl.private_core_disjoint
    hl.added_not_private hMM
  constructor
  · apply (mem_completionFamily _ _ _ _ _ _).mpr
    constructor
    · refine ⟨?_⟩
      simpa only [hl.restore_active hs, hmRestore, pair_comm z y, EndpointCutLabelII.firstEdge,
        EndpointCutLabelII.secondEdge] using D'
    · exact insert_subset hl.firstEdge_mem (insert_subset hl.secondEdge_mem hFG)
  · have hh₁ := D.insertThreePath_endpoint_role_first hp hq ho he₂ he₁ hD0 hDz hDa
      (hl.added_injective hs) hl.added_not_core hl.private_cards hl.private_pairwise
      hl.private_core_disjoint hl.added_not_private hMM hr
    have hh₂ := D.insertThreePath_endpoint_role_second hp hq ho he₂ he₁ hD0 hDz hDa
      (hl.added_injective hs) hl.added_not_core hl.private_cards hl.private_pairwise
      hl.private_core_disjoint hl.added_not_private hMM hr
    constructor
    · simpa only [hmRestore,
        pair_comm z y, EndpointCutLabelII.firstEdge, EndpointCutLabelII.secondEdge] using hh₁
    · simpa only [hmRestore,
        pair_comm z y, EndpointCutLabelII.firstEdge, EndpointCutLabelII.secondEdge] using hh₂
end LooseHamilton
