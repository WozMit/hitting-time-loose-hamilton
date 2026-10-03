module

public import HittingTimeLooseHamilton.EndpointCutModels

public section

/-! # Fresh replacement markers for both endpoint cuts -/
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G : Finset (Finset V)} {P : Finset V} {y z a : V}

theorem endpointCut_marker_fresh (ha : a ∉ P ∪ originalPorts M ∪ {y,z}) :
    {a,z} ∉ insert {y,z} M := by
  intro hm
  rcases mem_insert.mp hm with he | hm
  · have hmem : a ∈ ({y,z} : Finset V) := he ▸ (by simp : a ∈ ({a,z} : Finset V))
    exact ha (mem_union_right _ hmem)
  · exact ha (mem_union_left _ (mem_union_right _
      (mem_biUnion.mpr ⟨{a,z},hm,by simp⟩)))

theorem endpointCut_replacement_matching
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (ha : a ∉ P ∪ originalPorts M ∪ {y,z}) :
    ((insert {a,z} M : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
  have hd : ∀ m ∈ M, Disjoint ({a,z} : Finset V) m := by
    intro m hm
    apply disjoint_left.mpr
    intro v hv hvm
    have hvM : v ∈ originalPorts M := mem_biUnion.mpr ⟨m,hm,hvm⟩
    rcases mem_insert.mp hv with rfl | hv
    · exact ha (mem_union_left _ (mem_union_right _ hvM))
    · have hvz := mem_singleton.mp hv
      subst v
      exact disjoint_left.mp hs.ports_disjoint (mem_union_right _ (by simp)) hvM
  intro m hm n hn hmn
  rcases mem_insert.mp hm with rfl | hm <;> rcases mem_insert.mp hn with rfl | hn
  · exact False.elim (hmn rfl)
  · exact hd n hn
  · exact (hd m hm).symm
  · exact hM hm hn hmn

theorem endpointCutI_marker_fresh {l : EndpointCutLabelI V}
    (hl : EndpointCutLegalI r M G P y z l) : {l.1,z} ∉ insert {y,z} M :=
  endpointCut_marker_fresh hl.endpoint_fresh

theorem endpointCutII_marker_fresh {l : EndpointCutLabelII V}
    (hl : EndpointCutLegalII r M G P y z l) : {l.2.2.1,z} ∉ insert {y,z} M :=
  endpointCut_marker_fresh hl.endpoint_fresh

theorem endpointCutI_matching
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    {l : EndpointCutLabelI V} (hl : EndpointCutLegalI r M G P y z l) :
    (l.markers M z : Set (Finset V)).PairwiseDisjoint id :=
  endpointCut_replacement_matching hs hM hl.endpoint_fresh

theorem endpointCutII_matching
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    {l : EndpointCutLabelII V} (hl : EndpointCutLegalII r M G P y z l) :
    (l.markers M z : Set (Finset V)).PairwiseDisjoint id := by
  have h := endpointCut_replacement_matching hs hM hl.endpoint_fresh
  intro m hm n hn hmn
  apply h (insert_subset_insert _ (erase_subset _ _) hm)
    (insert_subset_insert _ (erase_subset _ _) hn) hmn

end LooseHamilton
