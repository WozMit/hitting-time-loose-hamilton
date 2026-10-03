module

public import HittingTimeLooseHamilton.EndpointSpliceDirections
public import HittingTimeLooseHamilton.EndpointSpliceLegal
public import HittingTimeLooseHamilton.EndpointSpliceInnerRecovery

public section
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G F : Finset (Finset V)} {P Q : Finset V} {y z t v : V}

set_option maxHeartbeats 600000 in
theorem endpointSplice_restore_II
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    {l : EndpointCutLabelII V} (hl : EndpointCutLegalII r M G P y z l)
    (hb : EndpointSpliceLegalII r M G P y z t l (Q,v))
    (C : MixedCycleOnWitness r (univ \ (P ∪ l.deleted y ∪ Q))
      (insert {v,l.2.2.1} (insert {t,z} (M.erase l.oldMarker))) F)
    (hzero : C.slot ⟨0,by have := C.length_ge; omega⟩ = .inl ⟨{v,l.2.2.1},mem_insert_self _ _⟩)
    (hv : C.junction ⟨0,by have := C.length_ge; omega⟩ = v)
    (ha : C.junction ⟨1,by have := C.length_ge; omega⟩ = l.2.2.1)
    (ht : C.junction (C.slot.symm (.inl ⟨{t,z},mem_insert_of_mem (mem_insert_self _ _)⟩)) = t) :
    ∃ D : MixedCycleOnWitness r (univ \ P) (insert {t,z} M)
        (insert ({v,y} ∪ Q) (insert (l.firstEdge y) (insert l.secondEdge F))),
      D.junction (D.slot.symm (.inl ⟨{t,z},mem_insert_self _ _⟩)) = t ∧
      D.junction (D.slot.symm (.inr ⟨{v,y} ∪ Q,mem_insert_self _ _⟩)) = v ∧
      D.junction (finRotate D.length (D.slot.symm (.inr ⟨{v,y} ∪ Q,mem_insert_self _ _⟩))) = y ∧
      D.junction (D.slot.symm (.inr ⟨l.firstEdge y,mem_insert_of_mem (mem_insert_self _ _)⟩)) = y ∧
      D.junction (finRotate D.length (D.slot.symm (.inr ⟨l.firstEdge y,mem_insert_of_mem (mem_insert_self _ _)⟩))) = l.1 ∧
      D.junction (D.slot.symm (.inr ⟨l.secondEdge,mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _))⟩)) = l.2.1 ∧
      D.junction (finRotate D.length (D.slot.symm (.inr ⟨l.secondEdge,mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _))⟩))) = l.2.2.1 := by
  have fresh (a : V) : ({v,a} : Finset V) ∉ insert {t,z} (M.erase l.oldMarker) :=
    hb.pair_fresh_erase a l.oldMarker
  have hp := fresh l.2.2.1
  have hq := fresh y
  have ho : ({l.1,l.2.1} : Finset V) ∉ insert {v,y} (insert {t,z} (M.erase l.oldMarker)) :=
    hb.old_marker_fresh hl.oldMarker_mem
  have hyS : y ∉ univ \ (P ∪ l.deleted y ∪ Q) := hl.splice_added_not_core (Q := Q) 0
  have huS : l.2.1 ∉ univ \ (P ∪ l.deleted y ∪ Q) := hl.splice_added_not_core (Q := Q) 2
  have he₂ : {l.2.1,l.2.2.1} ∪ l.2.2.2.2 ∉ F := by
    intro h; exact huS (C.edge_subset_active h (by simp))
  have hyedge₂ : y ∉ ({l.2.1,l.2.2.1} ∪ l.2.2.2.2 : Finset V) := by
    have hyu : y ≠ l.2.1 := by
      intro h
      have hh := (hl.added_injective hs) (show ![y,l.1,l.2.1] (0 : Fin 3) = ![y,l.1,l.2.1] 2 from h)
      exact (by decide : (0 : Fin 3) ≠ 2) hh
    have hya : y ≠ l.2.2.1 := by intro h; exact hl.endpoint_fresh (by simp [← h])
    have hyr : y ∉ l.2.2.2.2 := hl.added_not_private 0 1
    simp [hyu,hya,hyr]
  have he₁ : {y,l.1} ∪ l.2.2.2.1 ∉ insert ({l.2.1,l.2.2.1} ∪ l.2.2.2.2) F := by
    intro h
    rcases mem_insert.mp h with hh | hh
    · exact hyedge₂ (hh ▸ (by simp))
    · exact hyS (C.edge_subset_active hh (by simp))
  have hmrestore : insert {l.1,l.2.1} (insert {t,z} (M.erase l.oldMarker)) = insert {t,z} M := by
    rw [insert_comm]
    exact congrArg (insert {t,z}) (insert_erase hl.oldMarker_mem)
  have hMM : (↑(insert {v,y} (insert {l.1,l.2.1} (insert {t,z} (M.erase l.oldMarker)))) : Set (Finset V)).PairwiseDisjoint id := by
    rw [hmrestore]
    exact hb.restored_matching hs hM
  let A := C.insertThreePath hp hq ho he₂ he₁ hzero hv ha (hl.added_injective hs)
    (hl.splice_added_not_core (Q := Q)) hl.private_cards hl.private_pairwise
    (hl.splice_private_core_disjoint (Q := Q)) hl.added_not_private hMM
  have hAS : (univ \ (P ∪ l.deleted y ∪ Q)) ∪ {y,l.1,l.2.1} ∪ (l.2.2.2.1 ∪ l.2.2.2.2) = univ \ (P ∪ Q) :=
    hl.splice_restore_active hs hb
  have hQS : Disjoint Q ((univ \ (P ∪ l.deleted y ∪ Q)) ∪ {y,l.1,l.2.1} ∪ (l.2.2.2.1 ∪ l.2.2.2.2)) := by
    rw [hAS]
    exact hb.private_restored_disjoint
  have hvcut₁ : v ∉ ({y,l.1} ∪ l.2.2.2.1 : Finset V) := by
    intro h
    exact hb.newEndpoint_not_deleted (by
      simp only [EndpointCutLabelII.deleted,mem_union,mem_insert,mem_singleton] at *
      tauto)
  have hvcut₂ : v ∉ ({l.2.1,l.2.2.1} ∪ l.2.2.2.2 : Finset V) := by
    intro h
    simp only [mem_union,mem_insert,mem_singleton] at h
    rcases h with (h | h) | h
    · exact hb.newEndpoint_not_deleted (by simp [EndpointCutLabelII.deleted,h])
    · exact hb.newEndpoint_ne_a h
    · exact hb.newEndpoint_not_deleted (by simp [EndpointCutLabelII.deleted,h])
  have hnew : {v,y} ∪ Q ∉ insert ({y,l.1} ∪ l.2.2.2.1) (insert ({l.2.1,l.2.2.1} ∪ l.2.2.2.2) F) := by
    intro h
    rcases mem_insert.mp h with hh | hh
    · exact hvcut₁ (hh ▸ (by simp))
    · rcases mem_insert.mp hh with hh | hh
      · exact hvcut₂ (hh ▸ (by simp))
      · exact hyS (C.edge_subset_active hh (by simp))
  let B := A.expand ⟨{v,y},mem_insert_self _ _⟩ Q hb.private_card hQS hnew
  have hlast : ((univ \ (P ∪ l.deleted y ∪ Q)) ∪ {y,l.1,l.2.1} ∪ (l.2.2.2.1 ∪ l.2.2.2.2)) ∪ Q = univ \ P := by
    rw [hAS]
    have hd := hb.private_block_disjoint
    ext w
    simp only [mem_union,mem_sdiff,mem_univ,true_and]
    have hh : w ∈ Q → w ∉ P := fun h => disjoint_left.mp hd h
    tauto
  have hqfull : {v,y} ∉ insert {l.1,l.2.1} (insert {t,z} (M.erase l.oldMarker)) := by
    rw [hmrestore]
    exact hb.pair_fresh y
  have hmarker : (insert {v,y} (insert {l.1,l.2.1} (insert {t,z} (M.erase l.oldMarker)))).erase {v,y} = insert {t,z} M := by
    rw [erase_insert hqfull,hmrestore]
  have htne : ({t,z} : Finset V) ≠ {v,y} := by
    intro h
    exact hb.pair_fresh y (h ▸ mem_insert_self {t,z} M)
  have hsA := C.insertThreePath_path_starts hp hq ho he₂ he₁ hzero hv ha (hl.added_injective hs)
    (hl.splice_added_not_core (Q := Q)) hl.private_cards hl.private_pairwise
    (hl.splice_private_core_disjoint (Q := Q)) hl.added_not_private hMM
  have heA := C.insertThreePath_path_ends hp hq ho he₂ he₁ hzero hv ha (hl.added_injective hs)
    (hl.splice_added_not_core (Q := Q)) hl.private_cards hl.private_pairwise
    (hl.splice_private_core_disjoint (Q := Q)) hl.added_not_private hMM
  have htA : A.junction (A.slot.symm (.inl ⟨{t,z},mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _))⟩)) = t :=
    (C.insertThreePath_old_marker_start hp hq ho he₂ he₁ hzero hv ha (hl.added_injective hs)
      (hl.splice_added_not_core (Q := Q)) hl.private_cards hl.private_pairwise
      (hl.splice_private_core_disjoint (Q := Q)) hl.added_not_private hMM
      ⟨{t,z},mem_insert_self _ _⟩).trans ht
  have htB := (A.expand_old_marker_start ⟨{v,y},mem_insert_self _ _⟩ Q hb.private_card hQS hnew
    ⟨{t,z},mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _))⟩ htne).trans htA
  have hvB := (A.expand_new_ordinary_start ⟨{v,y},mem_insert_self _ _⟩ Q hb.private_card hQS hnew).trans hsA.1
  have hyB := (A.expand_new_ordinary_end ⟨{v,y},mem_insert_self _ _⟩ Q hb.private_card hQS hnew).trans heA.1
  have hycut := (A.expand_old_ordinary_start ⟨{v,y},mem_insert_self _ _⟩ Q hb.private_card hQS hnew
    ⟨{y,l.1} ∪ l.2.2.2.1,mem_insert_self _ _⟩).trans hsA.2.1
  have hucut := (A.expand_old_ordinary_end ⟨{v,y},mem_insert_self _ _⟩ Q hb.private_card hQS hnew
    ⟨{y,l.1} ∪ l.2.2.2.1,mem_insert_self _ _⟩).trans heA.2.1
  have hvc := (A.expand_old_ordinary_start ⟨{v,y},mem_insert_self _ _⟩ Q hb.private_card hQS hnew
    ⟨{l.2.1,l.2.2.1} ∪ l.2.2.2.2,mem_insert_of_mem (mem_insert_self _ _)⟩).trans hsA.2.2.2
  have hac := (A.expand_old_ordinary_end ⟨{v,y},mem_insert_self _ _⟩ Q hb.private_card hQS hnew
    ⟨{l.2.1,l.2.2.1} ∪ l.2.2.2.2,mem_insert_of_mem (mem_insert_self _ _)⟩).trans heA.2.2.2
  have hfinal : ∃ D : MixedCycleOnWitness r
      (((univ \ (P ∪ l.deleted y ∪ Q)) ∪ {y,l.1,l.2.1} ∪ (l.2.2.2.1 ∪ l.2.2.2.2)) ∪ Q)
      ((insert {v,y} (insert {l.1,l.2.1} (insert {t,z} (M.erase l.oldMarker)))).erase {v,y})
      (insert ({v,y} ∪ Q) (insert ({y,l.1} ∪ l.2.2.2.1) (insert ({l.2.1,l.2.2.1} ∪ l.2.2.2.2) F))),
      ∀ hroot : {t,z} ∈ ((insert {v,y} (insert {l.1,l.2.1} (insert {t,z} (M.erase l.oldMarker)))).erase {v,y}),
      D.junction (D.slot.symm (.inl ⟨{t,z},hroot⟩)) = t ∧
      D.junction (D.slot.symm (.inr ⟨{v,y} ∪ Q,mem_insert_self _ _⟩)) = v ∧
      D.junction (finRotate D.length (D.slot.symm (.inr ⟨{v,y} ∪ Q,mem_insert_self _ _⟩))) = y ∧
      D.junction (D.slot.symm (.inr ⟨{y,l.1} ∪ l.2.2.2.1,mem_insert_of_mem (mem_insert_self _ _)⟩)) = y ∧
      D.junction (finRotate D.length (D.slot.symm (.inr ⟨{y,l.1} ∪ l.2.2.2.1,mem_insert_of_mem (mem_insert_self _ _)⟩))) = l.1 ∧
      D.junction (D.slot.symm (.inr ⟨{l.2.1,l.2.2.1} ∪ l.2.2.2.2,mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _))⟩)) = l.2.1 ∧
      D.junction (finRotate D.length (D.slot.symm (.inr ⟨{l.2.1,l.2.2.1} ∪ l.2.2.2.2,mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _))⟩))) = l.2.2.1 :=
    ⟨B,fun _ => ⟨htB,hvB,hyB,hycut,hucut,hvc,hac⟩⟩
  rw [hlast,hmarker] at hfinal
  obtain ⟨D,hD⟩ := hfinal
  exact ⟨D,hD (mem_insert_self _ _)⟩
end LooseHamilton
