module

public import HittingTimeLooseHamilton.EndpointCutDeleted
public import HittingTimeLooseHamilton.EndpointCutModels

public section

/-! Concrete endpoint-cut contractions. The conclusions are actual cycle
witnesses on exactly the labelled surviving vertex sets. -/
noncomputable section
namespace LooseHamilton.MixedCycleOnWitness
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {P : Finset V} {M F : Finset (Finset V)} {y z : V}

/-- Replace the normalized root and first ordinary edge by the marker `az`. -/
@[expose] def endpointCutOne (C : MixedCycleOnWitness r (univ \ P) (insert {y,z} M) F)
    (hn : 6 ≤ C.length) (e : ↥F)
    (h₀ : C.slot ⟨0, by omega⟩ = .inl ⟨{y,z}, mem_insert_self _ _⟩)
    (h₁ : C.slot ⟨1, by omega⟩ = .inr e)
    (hz : C.junction ⟨0, by omega⟩ = z)
    (hy : C.junction ⟨1, by omega⟩ = y)
    (hroot : {y,z} ∉ M)
    (hfresh : {C.junction ⟨2, by omega⟩, z} ∉ insert {y,z} M)
    (hmatch : ((insert {C.junction ⟨2, by omega⟩,z} M : Finset (Finset V)) :
      Set (Finset V)).PairwiseDisjoint id) :
    MixedCycleOnWitness r (univ \ (P ∪ insert y (C.privateBlock e)))
      (insert {C.junction ⟨2, by omega⟩,z} M) (F.erase e.val) := by
  have hm : 3 ≤ C.length-1 := by omega
  have hlen : C.length = (C.length-1)+1 := by omega
  have hM := C.prefixMarkers_one ⟨{y,z}, mem_insert_self _ _⟩ e h₀ h₁
  have hE := C.prefixEdges_one ⟨{y,z}, mem_insert_self _ _⟩ e h₀ h₁
  rw [erase_insert hroot] at hM
  have hA := C.prefixActive_eq_sdiff (C.length-1) 1 (by omega) hlen
  rw [C.prefixInterior_one, C.prefixRemovedPrivate_one _ e h₀ h₁, hy] at hA
  have hA' : C.prefixActive (C.length-1) 1 hlen =
      univ \ (P ∪ insert y (C.privateBlock e)) := by
    rw [hA]
    ext v
    simp only [mem_sdiff, mem_univ, true_and, mem_union, mem_singleton, mem_insert]
    tauto
  have hqedge : ({C.junction ⟨2, by omega⟩,z} : Finset V) =
      {C.junction (C.prefixKeep (C.length-1) 1 hlen ⟨0, by omega⟩),
       C.junction (C.prefixKeep (C.length-1) 1 hlen
         (finRotate (C.length-1) ⟨0, by omega⟩))} := by
    have h0 : C.prefixKeep (C.length-1) 1 hlen ⟨0, by omega⟩ = ⟨0, by omega⟩ := Fin.ext rfl
    have h2 : C.prefixKeep (C.length-1) 1 hlen
        (finRotate (C.length-1) ⟨0, by omega⟩) = ⟨2, by omega⟩ := by
      apply Fin.ext
      simp only [prefixKeep_val]
      rw [finRotate_val_eq (C.length-1) (by omega)]
      norm_num [show 1 < C.length-1 by omega]
    rw [h0, h2, hz, pair_comm]
  have hh : ((insert {C.junction ⟨2, by omega⟩,z} (C.prefixMarkers 1) :
      Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by simpa [hM] using hmatch
  have D := C.contractPrefix (C.length-1) 1 hm hlen _ hfresh hh hqedge
  rw [hA', hM, hE] at D
  exact D

/-- Replace root, ordinary edge, old marker, ordinary edge by the marker `az`. -/
@[expose] def endpointCutThree (C : MixedCycleOnWitness r (univ \ P) (insert {y,z} M) F)
    (hn : 6 ≤ C.length) (m : ↥(insert {y,z} M)) (e f : ↥F)
    (h₀ : C.slot ⟨0, by omega⟩ = .inl ⟨{y,z}, mem_insert_self _ _⟩)
    (h₁ : C.slot ⟨1, by omega⟩ = .inr e)
    (h₂ : C.slot ⟨2, by omega⟩ = .inl m)
    (h₃ : C.slot ⟨3, by omega⟩ = .inr f)
    (hz : C.junction ⟨0, by omega⟩ = z)
    (hy : C.junction ⟨1, by omega⟩ = y)
    (hroot : {y,z} ∉ M)
    (hfresh : {C.junction ⟨4, by omega⟩, z} ∉ insert {y,z} M)
    (hmatch : ((insert {C.junction ⟨4, by omega⟩,z} (M.erase m.val) :
      Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id) :
    MixedCycleOnWitness r
      (univ \ (P ∪ ({y, C.junction ⟨2, by omega⟩, C.junction ⟨3, by omega⟩} ∪
        C.privateBlock e ∪ C.privateBlock f)))
      (insert {C.junction ⟨4, by omega⟩,z} (M.erase m.val))
      ((F.erase e.val).erase f.val) := by
  have hm : 3 ≤ C.length-3 := by omega
  have hlen : C.length = (C.length-3)+3 := by omega
  have hM := C.prefixMarkers_three (by omega) ⟨{y,z}, mem_insert_self _ _⟩ m e f h₀ h₁ h₂ h₃
  have hE := C.prefixEdges_three (by omega) ⟨{y,z}, mem_insert_self _ _⟩ m e f h₀ h₁ h₂ h₃
  rw [erase_insert hroot] at hM
  have hA := C.prefixActive_eq_sdiff (C.length-3) 3 (by omega) hlen
  rw [C.prefixInterior_three (by omega),
    C.prefixRemovedPrivate_three (by omega) _ m e f h₀ h₁ h₂ h₃, hy] at hA
  have hA' : C.prefixActive (C.length-3) 3 hlen =
      univ \ (P ∪ ({y, C.junction ⟨2, by omega⟩, C.junction ⟨3, by omega⟩} ∪
        C.privateBlock e ∪ C.privateBlock f)) := by
    rw [hA]
    ext v
    simp only [mem_sdiff, mem_univ, true_and, mem_union]
    tauto
  have hqedge : ({C.junction ⟨4, by omega⟩,z} : Finset V) =
      {C.junction (C.prefixKeep (C.length-3) 3 hlen ⟨0, by omega⟩),
       C.junction (C.prefixKeep (C.length-3) 3 hlen
         (finRotate (C.length-3) ⟨0, by omega⟩))} := by
    have h0 : C.prefixKeep (C.length-3) 3 hlen ⟨0, by omega⟩ = ⟨0, by omega⟩ := Fin.ext rfl
    have h4 : C.prefixKeep (C.length-3) 3 hlen
        (finRotate (C.length-3) ⟨0, by omega⟩) = ⟨4, by omega⟩ := by
      apply Fin.ext
      simp only [prefixKeep_val]
      rw [finRotate_val_eq (C.length-3) (by omega)]
      norm_num [show 1 < C.length-3 by omega]
    rw [h0, h4, hz, pair_comm]
  have hh : ((insert {C.junction ⟨4, by omega⟩,z} (C.prefixMarkers 3) :
      Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by simpa [hM] using hmatch
  have D := C.contractPrefix (C.length-3) 3 hm hlen _ hfresh hh hqedge
  rw [hA', hM, hE] at D
  exact D

end LooseHamilton.MixedCycleOnWitness
