module

public import HittingTimeLooseHamilton.EndpointCutModels

public section

/-! # Endpoint-cut cores are actual unrestricted counts on surviving vertices -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G : Finset (Finset V)} {P : Finset V} {y z : V}

theorem endpointCutI_markers_survive
    (hs : LegalPrivateCompletion r M P {y, z})
    {l : EndpointCutLabelI V} (hl : EndpointCutLegalI r M G P y z l) :
    ∀ m ∈ l.markers M z, m ⊆ univ \ (P ∪ l.deleted y) := by
  intro m hm v hv
  have hzP : z ∉ P := fun hz => disjoint_left.mp hs.private_pair_disjoint hz (by simp)
  have hyM : y ∉ originalPorts M := fun hy =>
    disjoint_left.mp hs.ports_disjoint (mem_union_right _ (by simp)) hy
  have hR := disjoint_left.mp hl.private_disjoint
  have ha := hl.endpoint_fresh
  simp only [EndpointCutLabelI.markers, mem_insert] at hm
  refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
  intro hdel
  rcases mem_union.mp hdel with hp | hd
  · rcases hm with rfl | hm
    · simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact ha (mem_union_left _ (mem_union_left _ hp))
      · exact hzP hp
    · exact (mem_sdiff.mp (hs.marker_subset_active hm hv)).2 hp
  · simp only [EndpointCutLabelI.deleted, mem_insert] at hd
    rcases hd with hvy | hRmem
    · subst v
      rcases hm with rfl | hm
      · simp only [mem_insert, mem_singleton] at hv
        rcases hv with hv | hv
        · subst y
          exact ha (by simp)
        · have hyz : y ≠ z := by
            have hc := hs.pair_card
            intro he; simp [he] at hc
          exact hyz hv
      · exact hyM (mem_biUnion.mpr ⟨m, hm, hv⟩)
    · apply hR hRmem
      rcases hm with rfl | hm
      · simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl <;> simp
      · exact mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨m, hm, hv⟩))

theorem endpointCutCoreCountI_eq_X (hr : 3 ≤ r)
    (hs : LegalPrivateCompletion r M P {y, z})
    {l : EndpointCutLabelI V} (hl : EndpointCutLegalI r M G P y z l) :
    (endpointCutCoreFamilyI r M G P y z l).card =
      unrestrictedCycleCount r
        (restrictEdges (univ \ (P ∪ l.deleted y)) (l.markers M z))
        (inducedHost (univ \ (P ∪ l.deleted y)) G) :=
  cycleOnCount_eq_unrestricted hr _ _ _ (endpointCutI_markers_survive hs hl)

theorem endpointCutII_markers_survive
    (hs : LegalPrivateCompletion r M P {y, z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    {l : EndpointCutLabelII V} (hl : EndpointCutLegalII r M G P y z l) :
    ∀ m ∈ l.markers M z, m ⊆ univ \ (P ∪ l.deleted y) := by
  have hyM : y ∉ originalPorts M := fun hy =>
    disjoint_left.mp hs.ports_disjoint (mem_union_right _ (by simp)) hy
  have hzM : z ∉ originalPorts M := fun hz =>
    disjoint_left.mp hs.ports_disjoint (mem_union_right _ (by simp)) hz
  have huM : l.1 ∈ originalPorts M :=
    mem_biUnion.mpr ⟨l.oldMarker, hl.oldMarker_mem, by simp [EndpointCutLabelII.oldMarker]⟩
  have hu'M : l.2.1 ∈ originalPorts M :=
    mem_biUnion.mpr ⟨l.oldMarker, hl.oldMarker_mem, by simp [EndpointCutLabelII.oldMarker]⟩
  have hzP : z ∉ P := fun hz => disjoint_left.mp hs.private_pair_disjoint hz (by simp)
  have hyz : y ≠ z := by
    intro he
    have hc := hs.pair_card
    simp [he] at hc
  have ha := hl.endpoint_fresh
  have hR1 := disjoint_left.mp hl.first_private_disjoint
  have hR2 := disjoint_left.mp hl.second_private_disjoint
  intro m hm v hv
  simp only [EndpointCutLabelII.markers, mem_insert] at hm
  refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
  intro hdel
  rcases mem_union.mp hdel with hp | hd
  · rcases hm with rfl | hm
    · simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact ha (mem_union_left _ (mem_union_left _ hp))
      · exact hzP hp
    · exact (mem_sdiff.mp (hs.marker_subset_active (mem_erase.mp hm).2 hv)).2 hp
  · have hd' : v = y ∨ v ∈ l.oldMarker ∨ v ∈ l.2.2.2.1 ∨ v ∈ l.2.2.2.2 := by
      simpa only [EndpointCutLabelII.deleted, EndpointCutLabelII.oldMarker,
        mem_union, mem_insert, mem_singleton, or_assoc] using hd
    rcases hd' with hvy | hvold | hvR1 | hvR2
    · subst v
      rcases hm with rfl | hm
      · simp only [mem_insert, mem_singleton] at hv
        rcases hv with he | he
        · subst y
          exact ha (by simp)
        · exact hyz he
      · exact hyM (mem_biUnion.mpr ⟨m, (mem_erase.mp hm).2, hv⟩)
    · have hvM : v ∈ originalPorts M := mem_biUnion.mpr ⟨_, hl.oldMarker_mem, hvold⟩
      rcases hm with rfl | hm
      · simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact ha (mem_union_left _ (mem_union_right _ hvM))
        · exact hzM hvM
      · exact disjoint_left.mp (hM (mem_erase.mp hm).2 hl.oldMarker_mem (mem_erase.mp hm).1) hv hvold
    · apply hR1 hvR1
      rcases hm with rfl | hm
      · simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl <;> simp
      · exact mem_union_left _ (mem_union_right _
          (mem_biUnion.mpr ⟨m, (mem_erase.mp hm).2, hv⟩))
    · apply hR2 hvR2
      rcases hm with rfl | hm
      · simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl <;> simp
      · exact mem_union_left _ (mem_union_right _
          (mem_biUnion.mpr ⟨m, (mem_erase.mp hm).2, hv⟩))

theorem endpointCutCoreCountII_eq_X (hr : 3 ≤ r)
    (hs : LegalPrivateCompletion r M P {y, z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    {l : EndpointCutLabelII V} (hl : EndpointCutLegalII r M G P y z l) :
    (endpointCutCoreFamilyII r M G P y z l).card =
      unrestrictedCycleCount r
        (restrictEdges (univ \ (P ∪ l.deleted y)) (l.markers M z))
        (inducedHost (univ \ (P ∪ l.deleted y)) G) :=
  cycleOnCount_eq_unrestricted hr _ _ _ (endpointCutII_markers_survive hs hM hl)

end LooseHamilton
