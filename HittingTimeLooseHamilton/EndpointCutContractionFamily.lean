module

public import HittingTimeLooseHamilton.EndpointCutContraction
public import HittingTimeLooseHamilton.EndpointCutMatching

public section

/-! Endpoint cuts land in the independent actual core families. -/
noncomputable section
set_option maxHeartbeats 800000
namespace LooseHamilton.MixedCycleOnWitness
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {P : Finset V} {M G F : Finset (Finset V)} {y z : V}

theorem endpointCut_coreI (C : MixedCycleOnWitness r (univ \ P) (insert {y,z} M) F)
    (hn : 6 ≤ C.length) (e : ↥F)
    (h₀ : C.slot ⟨0, by omega⟩ = .inl ⟨{y,z}, mem_insert_self _ _⟩)
    (h₁ : C.slot ⟨1, by omega⟩ = .inr e)
    (hz : C.junction ⟨0, by omega⟩ = z) (hy : C.junction ⟨1, by omega⟩ = y)
    (hs : LegalPrivateCompletion r M P {y,z}) (hF : F ⊆ G)
    (hl : EndpointCutLegalI r M G P y z
      (C.junction ⟨2, by omega⟩, C.privateBlock e)) :
    F.erase e.val ∈ endpointCutCoreFamilyI r M G P y z
      (C.junction ⟨2, by omega⟩, C.privateBlock e) := by
  have hroot : {y,z} ∉ M := by
    intro h
    exact disjoint_left.mp hs.ports_disjoint (mem_union_right _ (by simp : y ∈ ({y,z}:Finset V)))
      (mem_biUnion.mpr ⟨{y,z},h,by simp⟩)
  have hM : (M : Set (Finset V)).PairwiseDisjoint id := by
    intro m hm n hn hmn
    exact C.marked_matching (mem_insert_of_mem hm) (mem_insert_of_mem hn) hmn
  rw [mem_endpointCutCoreFamilyI]
  refine ⟨⟨?_⟩, fun f hf => hF ((mem_erase.mp hf).2)⟩
  exact C.endpointCutOne hn e h₀ h₁ hz hy hroot (endpointCutI_marker_fresh hl)
    (endpointCutI_matching hs hM hl)

theorem endpointCut_coreII (C : MixedCycleOnWitness r (univ \ P) (insert {y,z} M) F)
    (hn : 6 ≤ C.length) (m : ↥(insert {y,z} M)) (e f : ↥F)
    (h₀ : C.slot ⟨0, by omega⟩ = .inl ⟨{y,z}, mem_insert_self _ _⟩)
    (h₁ : C.slot ⟨1, by omega⟩ = .inr e)
    (h₂ : C.slot ⟨2, by omega⟩ = .inl m)
    (h₃ : C.slot ⟨3, by omega⟩ = .inr f)
    (hz : C.junction ⟨0, by omega⟩ = z) (hy : C.junction ⟨1, by omega⟩ = y)
    (hs : LegalPrivateCompletion r M P {y,z}) (hF : F ⊆ G)
    (hl : EndpointCutLegalII r M G P y z
      (C.junction ⟨2, by omega⟩, C.junction ⟨3, by omega⟩,
        C.junction ⟨4, by omega⟩, C.privateBlock e, C.privateBlock f)) :
    (F.erase e.val).erase f.val ∈ endpointCutCoreFamilyII r M G P y z
      (C.junction ⟨2, by omega⟩, C.junction ⟨3, by omega⟩,
        C.junction ⟨4, by omega⟩, C.privateBlock e, C.privateBlock f) := by
  have hroot : {y,z} ∉ M := by
    intro h
    exact disjoint_left.mp hs.ports_disjoint (mem_union_right _ (by simp : y ∈ ({y,z}:Finset V)))
      (mem_biUnion.mpr ⟨{y,z},h,by simp⟩)
  have hM : (M : Set (Finset V)).PairwiseDisjoint id := by
    intro m hm n hn hmn
    exact C.marked_matching (mem_insert_of_mem hm) (mem_insert_of_mem hn) hmn
  have hmval : m.val = {C.junction ⟨2, by omega⟩, C.junction ⟨3, by omega⟩} := by
    have hh := C.slot_edge ⟨2, by omega⟩
    rw [h₂] at hh
    have hi : finRotate C.length ⟨2, by omega⟩ = ⟨3, by omega⟩ := by
      apply Fin.ext
      rw [finRotate_val_eq C.length (by omega)]
      norm_num [show 2+1 < C.length by omega]
    simpa only [hi] using hh
  have hmatch := endpointCutII_matching hs hM hl
  change ((insert {C.junction ⟨4, by omega⟩, z}
    (M.erase {C.junction ⟨2, by omega⟩, C.junction ⟨3, by omega⟩}) :
    Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id at hmatch
  rw [← hmval] at hmatch
  have D := C.endpointCutThree hn m e f h₀ h₁ h₂ h₃ hz hy hroot
    (endpointCutII_marker_fresh hl) hmatch
  rw [hmval] at D
  rw [mem_endpointCutCoreFamilyII]
  exact ⟨⟨D⟩, fun g hg => hF ((mem_erase.mp (mem_erase.mp hg).2).2)⟩

end LooseHamilton.MixedCycleOnWitness
