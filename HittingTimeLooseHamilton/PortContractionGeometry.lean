module

public import HittingTimeLooseHamilton.EndpointCuts
public import HittingTimeLooseHamilton.RootFreePortTests

public section

/-! Original-marker contraction: unlike a private completion, its source has
no private vertices deleted. The two-slot surgery is reused directly. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G : Finset (Finset V)} {U : Finset V} {y z : V}

omit [Fintype V] in
/-- A source pair with no deletion; rank two here records just its geometry. -/
theorem portSource_geometry (hyz : y ≠ z)
    (hd : Disjoint ({y,z} : Finset V) (originalPorts M)) :
    LegalPrivateCompletion 2 M ∅ {y,z} := by
  refine ⟨by simp, card_pair hyz, by simp, ?_⟩
  simpa using hd

theorem portCut_no_typeII (hy : y ∈ U) (hports : originalPorts M ⊆ U)
    (hG : G ⊆ allowedEdges r U) (hd : Disjoint ({y,z} : Finset V) (originalPorts M))
    (l : EndpointCutLabelII V) : ¬ EndpointCutLegalII r M G ∅ y z l := by
  intro hl
  have hlM : l.1 ∈ originalPorts M := mem_biUnion.mpr ⟨l.oldMarker, hl.oldMarker_mem, by simp [EndpointCutLabelII.oldMarker]⟩
  have hlU : l.1 ∈ U := hports hlM
  have hne : y ≠ l.1 := by
    intro h
    exact disjoint_left.mp hd (by simp : y ∈ ({y,z}:Finset V)) (h.symm ▸ hlM)
  have hsub : ({y,l.1} : Finset V) ⊆ l.firstEdge y ∩ U := by
    intro a ha
    refine mem_inter.mpr ⟨mem_union_left _ ha, ?_⟩
    rcases mem_insert.mp ha with rfl | ha
    · exact hy
    · exact mem_singleton.mp ha ▸ hlU
  have hcard := card_le_card hsub
  rw [card_pair hne] at hcard
  have hbound := ((mem_allowedEdges r U _).mp (hG hl.firstEdge_mem)).2
  omega

/-- Restore the original marked pair and its one incident ordinary edge. -/
theorem portCut_expand_I (hr : 3 ≤ r) (hyz : y ≠ z)
    (hd : Disjoint ({y,z} : Finset V) (originalPorts M))
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    {l : EndpointCutLabelI V} (hl : EndpointCutLegalI r M G ∅ y z l)
    {F : Finset (Finset V)} (hF : F ∈ endpointCutCoreFamilyI r M G ∅ y z l) :
    insert (l.edge y) F ∈ completionFamily r M G ∅ {y,z} ∧
      edgeEndpointPair (insert {y,z} M) (insert (l.edge y) F) (l.edge y) = {y,l.1} := by
  have hs := portSource_geometry hyz hd
  obtain ⟨⟨C₀⟩,hFG⟩ := (mem_endpointCutCoreFamilyI _ _ _ _ _ _ _ _).mp hF
  have C : MixedCycleOnWitness r (univ \ (∅ ∪ l.deleted y)) (insert {z,l.1} M) F := by
    simpa only [EndpointCutLabelI.markers, pair_comm l.1 z] using C₀
  have hza : z ≠ l.1 := by
    intro h
    exact hl.endpoint_fresh (mem_union_right _ (by simp [h]))
  obtain ⟨D,hD0,hDz,hDa⟩ := C.exists_rooted ⟨{z,l.1},mem_insert_self _ _⟩ z l.1 rfl hza
  have hp : {z,l.1} ∉ M := by
    intro hm
    exact endpointCutI_marker_fresh hl (mem_insert_of_mem (by simpa only [pair_comm z l.1] using hm))
  have hq : {z,y} ∉ M := by simpa only [pair_comm z y] using endpoint_source_pair_fresh hs
  have he : {y,l.1} ∪ l.2 ∉ F := endpointCutCoreI_edge_not_mem hF
  have hMM : (↑(insert {z,y} M) : Set (Finset V)).PairwiseDisjoint id := by
    simpa only [pair_comm z y] using endpoint_source_matching hs hM
  have hrestore : (univ \ (∅ ∪ l.deleted y)) ∪ {y} ∪ l.2 = univ \ (∅ : Finset V) := by
    ext v
    simp only [EndpointCutLabelI.deleted, mem_union, mem_sdiff, mem_univ, true_and,
      notMem_empty, false_or, mem_insert, mem_singleton, not_false_eq_true]
    tauto
  let D' := D.insertOnePath hp hq he hD0 hDz hDa hl.y_not_core
    hl.private_core_disjoint hl.y_not_private hl.private_card hMM
  constructor
  · apply (mem_completionFamily _ _ _ _ _ _).mpr
    refine ⟨⟨?_⟩, insert_subset hl.edge_mem hFG⟩
    simpa only [hrestore, pair_comm z y, EndpointCutLabelI.edge] using D'
  · have h := D.insertOnePath_endpoint_role hr hp hq he hD0 hDz hDa hl.y_not_core
      hl.private_core_disjoint hl.y_not_private hl.private_card hMM
    simpa only [pair_comm z y, EndpointCutLabelI.edge] using h

end LooseHamilton
