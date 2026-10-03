module

public import HittingTimeLooseHamilton.PortContractionOriginal

public section

/-! Reindexing the exact port contraction by unordered root links. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Full link sets at the original port, avoiding every original port. -/
@[expose] def portLinkSets (G : Finset (Finset V)) (U : Finset V) (y : V) : Finset (Finset V) := by
  classical
  exact univ.filter (fun A => insert y A ∈ G ∧ Disjoint A U)

variable {r : ℕ} {M G : Finset (Finset V)} {y z : V}

theorem portCutLabel_to_link {l : EndpointCutLabelI V}
    (hl : EndpointCutLegalI r M G ∅ y z l) :
    insert l.1 l.2 ∈ portLinkSets G (originalPorts (insert {y,z} M)) y ∧ l.1 ∉ l.2 := by
  classical
  have hnot : l.1 ∉ l.2 := fun h => disjoint_left.mp hl.private_disjoint h (by simp)
  refine ⟨?_,hnot⟩
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_, ?_⟩
  · convert hl.edge_mem using 1
    ext v
    simp [EndpointCutLabelI.edge, or_assoc]
  · apply disjoint_left.mpr
    intro v hv hp
    have hp' : v ∈ originalPorts M ∪ {y,z} := by
      obtain ⟨e,he,hv⟩ := mem_biUnion.mp hp
      rcases mem_insert.mp he with rfl | he
      · exact mem_union_right _ hv
      · exact mem_union_left _ (mem_biUnion.mpr ⟨e,he,hv⟩)
    rcases mem_insert.mp hv with rfl | hv
    · exact hl.endpoint_fresh (by simpa using hp')
    · exact disjoint_left.mp hl.private_disjoint hv (by simpa [or_assoc, or_left_comm, or_comm] using (mem_union_left {l.1} hp'))

theorem portLink_to_cutLabel (hr : 2 ≤ r) (hG : G ⊆ completeEdges V r)
    (A : Finset V) (hA : A ∈ portLinkSets G (originalPorts (insert {y,z} M)) y)
    (v : V) (hv : v ∈ A) : EndpointCutLegalI r M G ∅ y z (v,A.erase v) := by
  classical
  obtain ⟨_,he,hdisj⟩ := mem_filter.mp hA
  have hyp : y ∈ originalPorts (insert {y,z} M) := mem_biUnion.mpr ⟨{y,z},by simp,by simp⟩
  have hzp : z ∈ originalPorts (insert {y,z} M) := mem_biUnion.mpr ⟨{y,z},by simp,by simp⟩
  have hyA : y ∉ A := fun h => disjoint_left.mp hdisj h hyp
  have hports : originalPorts M ∪ {y,z} ⊆ originalPorts (insert {y,z} M) := by
    intro a ha
    rcases mem_union.mp ha with ha | ha
    · obtain ⟨e,he,ha⟩ := mem_biUnion.mp ha
      exact mem_biUnion.mpr ⟨e,mem_insert_of_mem he,ha⟩
    · exact mem_biUnion.mpr ⟨{y,z},by simp,ha⟩
  have hcard := (mem_completeEdges r _).mp (hG he)
  rw [card_insert_of_notMem hyA] at hcard
  constructor
  · intro hp
    apply disjoint_left.mp hdisj hv
    apply hports
    simpa using hp
  · simp only [card_erase_of_mem hv]
    omega
  · apply disjoint_left.mpr
    intro a ha hb
    obtain ⟨hav,ha⟩ := mem_erase.mp ha
    simp only [empty_union, mem_union, mem_insert, mem_singleton] at hb
    rcases hb with hb | rfl | rfl | rfl
    · exact disjoint_left.mp hdisj ha (hports (mem_union_left _ hb))
    · exact disjoint_left.mp hdisj ha hyp
    · exact disjoint_left.mp hdisj ha hzp
    · exact hav rfl
  · change {y,v} ∪ A.erase v ∈ G
    convert he using 1
    rw [← insert_erase hv]
    ext a
    simp [or_assoc]

end LooseHamilton
