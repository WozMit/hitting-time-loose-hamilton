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

theorem endpointSplice_restore_I
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    {l : EndpointCutLabelI V} (hl : EndpointCutLegalI r M G P y z l)
    (hb : EndpointSpliceLegalI r M G P y z t l (Q,v))
    (C : MixedCycleOnWitness r (univ \ (P ∪ l.deleted y ∪ Q))
      (insert {v,l.1} (insert {t,z} M)) F)
    (hzero : C.slot ⟨0,by have := C.length_ge; omega⟩ = .inl ⟨{v,l.1},mem_insert_self _ _⟩)
    (hv : C.junction ⟨0,by have := C.length_ge; omega⟩ = v)
    (ha : C.junction ⟨1,by have := C.length_ge; omega⟩ = l.1)
    (ht : C.junction (C.slot.symm (.inl ⟨{t,z},mem_insert_of_mem (mem_insert_self _ _)⟩)) = t) :
    ∃ D : MixedCycleOnWitness r (univ \ P) (insert {t,z} M)
        (insert ({v,y} ∪ Q) (insert (l.edge y) F)),
      D.junction (D.slot.symm (.inl ⟨{t,z},mem_insert_self _ _⟩)) = t ∧
      D.junction (D.slot.symm (.inr ⟨{v,y} ∪ Q,mem_insert_self _ _⟩)) = v ∧
      D.junction (finRotate D.length (D.slot.symm (.inr ⟨{v,y} ∪ Q,mem_insert_self _ _⟩))) = y ∧
      D.junction (D.slot.symm (.inr ⟨l.edge y,mem_insert_of_mem (mem_insert_self _ _)⟩)) = y ∧
      D.junction (finRotate D.length (D.slot.symm (.inr ⟨l.edge y,mem_insert_of_mem (mem_insert_self _ _)⟩))) = l.1 := by
  have fresh (a : V) : ({v,a} : Finset V) ∉ insert {t,z} M := by
    intro hm
    rcases mem_insert.mp hm with hh | hh
    · have hvm : v ∈ ({t,z} : Finset V) := hh ▸ (by simp)
      simpa [hb.newEndpoint_ne_t,hb.newEndpoint_ne_z] using hvm
    · exact hb.newEndpoint_not_ports (mem_biUnion.mpr ⟨{v,a},hh,by simp⟩)
  have hp := fresh l.1
  have hq := fresh y
  have hyS : y ∉ univ \ (P ∪ l.deleted y ∪ Q) := by simp [EndpointCutLabelI.deleted]
  have hsmall : univ \ (P ∪ l.deleted y ∪ Q) ⊆ univ \ (P ∪ l.deleted y) := by
    intro w hw
    exact mem_sdiff.mpr ⟨mem_univ _,fun h => (mem_sdiff.mp hw).2 (mem_union_left _ h)⟩
  have hRS := hl.private_core_disjoint.mono_left hsmall
  have he : {y,l.1} ∪ l.2 ∉ F := by
    intro he
    exact hyS (C.edge_subset_active he (by simp))
  have hMM := hb.restored_matching hs hM
  let A := C.insertOnePath hp hq he hzero hv ha hyS hRS hl.y_not_private hl.private_card hMM
  have hAS : (univ \ (P ∪ l.deleted y ∪ Q)) ∪ {y} ∪ l.2 = univ \ (P ∪ Q) :=
    hl.splice_restore_active hs hb
  have hQS : Disjoint Q ((univ \ (P ∪ l.deleted y ∪ Q)) ∪ {y} ∪ l.2) := by
    rw [hAS]
    exact disjoint_left.mpr (by intro w hw h; exact (mem_sdiff.mp h).2 (mem_union_right _ hw))
  have hvcut : v ∉ ({y,l.1} ∪ l.2 : Finset V) := by
    have hvr : v ∉ l.2 := fun h => hb.newEndpoint_not_deleted (mem_insert_of_mem h)
    simp [hb.newEndpoint_ne_y,hb.newEndpoint_ne_a,hvr]
  have hnew : {v,y} ∪ Q ∉ insert ({y,l.1} ∪ l.2) F := by
    intro hm
    rcases mem_insert.mp hm with hh | hh
    · exact hvcut (hh ▸ (by simp))
    · exact hyS (C.edge_subset_active hh (by simp))
  let B := A.expand ⟨{v,y},mem_insert_self _ _⟩ Q hb.private_card hQS hnew
  have hlast : ((univ \ (P ∪ l.deleted y ∪ Q)) ∪ {y} ∪ l.2) ∪ Q = univ \ P := by
    rw [hAS]
    have hd := hb.private_block_disjoint
    ext w
    simp only [mem_union,mem_sdiff,mem_univ,true_and]
    have hh : w ∈ Q → w ∉ P := fun h => disjoint_left.mp hd h
    tauto
  have hmarker : (insert {v,y} (insert {t,z} M)).erase {v,y} = insert {t,z} M := erase_insert hq
  have htne : ({t,z} : Finset V) ≠ {v,y} := by
    intro h
    exact hq (h ▸ mem_insert_self {t,z} M)
  have hsA := C.insertOnePath_path_starts hp hq he hzero hv ha hyS hRS hl.y_not_private hl.private_card hMM
  have heA := C.insertOnePath_path_ends hp hq he hzero hv ha hyS hRS hl.y_not_private hl.private_card hMM
  have htA : A.junction (A.slot.symm (.inl ⟨{t,z},mem_insert_of_mem (mem_insert_self _ _)⟩)) = t :=
    (C.insertOnePath_old_marker_start hp hq he hzero hv ha hyS hRS hl.y_not_private hl.private_card hMM
      ⟨{t,z},mem_insert_self _ _⟩).trans ht
  have htB := (A.expand_old_marker_start ⟨{v,y},mem_insert_self _ _⟩ Q hb.private_card hQS hnew
    ⟨{t,z},mem_insert_of_mem (mem_insert_self _ _)⟩ htne).trans htA
  have hvB := (A.expand_new_ordinary_start ⟨{v,y},mem_insert_self _ _⟩ Q hb.private_card hQS hnew).trans hsA.1
  have hyB := (A.expand_new_ordinary_end ⟨{v,y},mem_insert_self _ _⟩ Q hb.private_card hQS hnew).trans heA.1
  have hycut := (A.expand_old_ordinary_start ⟨{v,y},mem_insert_self _ _⟩ Q hb.private_card hQS hnew
    ⟨{y,l.1} ∪ l.2,mem_insert_self _ _⟩).trans hsA.2
  have hacut := (A.expand_old_ordinary_end ⟨{v,y},mem_insert_self _ _⟩ Q hb.private_card hQS hnew
    ⟨{y,l.1} ∪ l.2,mem_insert_self _ _⟩).trans heA.2
  have hresult := And.intro htB (And.intro hvB (And.intro hyB (And.intro hycut hacut)))
  have hfinal : ∃ D : MixedCycleOnWitness r
      (((univ \ (P ∪ l.deleted y ∪ Q)) ∪ {y} ∪ l.2) ∪ Q)
      ((insert {v,y} (insert {t,z} M)).erase {v,y})
      (insert ({v,y} ∪ Q) (insert ({y,l.1} ∪ l.2) F)),
      ∀ hroot : {t,z} ∈ ((insert {v,y} (insert {t,z} M)).erase {v,y}),
      D.junction (D.slot.symm (.inl ⟨{t,z},hroot⟩)) = t ∧
      D.junction (D.slot.symm (.inr ⟨{v,y} ∪ Q,mem_insert_self _ _⟩)) = v ∧
      D.junction (finRotate D.length (D.slot.symm (.inr ⟨{v,y} ∪ Q,mem_insert_self _ _⟩))) = y ∧
      D.junction (D.slot.symm (.inr ⟨{y,l.1} ∪ l.2,mem_insert_of_mem (mem_insert_self _ _)⟩)) = y ∧
      D.junction (finRotate D.length (D.slot.symm (.inr ⟨{y,l.1} ∪ l.2,mem_insert_of_mem (mem_insert_self _ _)⟩))) = l.1 :=
    ⟨B,fun _ => hresult⟩
  rw [hlast, hmarker] at hfinal
  obtain ⟨D,hD⟩ := hfinal
  exact ⟨D,hD (mem_insert_self _ _)⟩
end LooseHamilton
