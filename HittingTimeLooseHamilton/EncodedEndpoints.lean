module

public import HittingTimeLooseHamilton.WitnessEncoding
public import HittingTimeLooseHamilton.ContractedEndpoints
public import HittingTimeLooseHamilton.PairOrientations

public section
noncomputable section
open Finset
namespace LooseHamilton.MixedCycleWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}

theorem encoded_markerFirst (C : MixedCycleWitness r markers edges)
    (hM : IsPairMatching markers) (root : ↥markers)
    (hroot : C.markerStart root = rootEndpoint hM root.val root.property) (e : ↥markers) :
    markerFirst hM root.val root.property (C.markerDirections root.val) e = C.markerStart e := by
  by_cases he : e.val = root.val
  · have h : e = root := Subtype.ext he
    subst e
    rw [markerFirst_root, hroot]
  · let f : ↥(markers.erase root.val) := ⟨e.val, mem_erase.mpr ⟨he, e.property⟩⟩
    exact markerFirst_nonroot hM root.val root.property (C.markerDirections root.val) f

theorem encoded_markerLast (C : MixedCycleWitness r markers edges)
    (hM : IsPairMatching markers) (root : ↥markers)
    (hroot : C.markerStart root = rootEndpoint hM root.val root.property) (e : ↥markers) :
    (markerLast hM root.val root.property (C.markerDirections root.val) e).val =
      C.blockEnd (.inl e) := by
  have hs := C.slot_edge (C.slot.symm (.inl e))
  rw [C.slot.apply_symm_apply] at hs
  simp only at hs
  have hm := (markerLast hM root.val root.property (C.markerDirections root.val) e).property
  let x : V := (markerLast hM root.val root.property (C.markerDirections root.val) e).val
  change x ∈ e.val at hm
  rw [hs] at hm
  simp only [mem_insert, mem_singleton] at hm
  rcases hm with hm | hm
  · have hn := markerLast_ne_first hM root.val root.property (C.markerDirections root.val) e
    rw [C.encoded_markerFirst hM root hroot e] at hn
    exact False.elim (hn hm)
  · exact hm

end LooseHamilton.MixedCycleWitness
