module

public import HittingTimeLooseHamilton.PermutationTransport
public import HittingTimeLooseHamilton.CycleNormalization

public section
noncomputable section
open Finset
namespace LooseHamilton.MixedCycleWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}

/-- Every cyclic slot is reached by iterating rotation from any chosen slot. -/
theorem exists_rotate_iterate (C : MixedCycleWitness r markers edges)
    (i j : Fin C.length) : ∃ n : ℕ, (finRotate C.length)^[n] i = j := by
  have hc (n : ℕ) (hn : 0 < n) : (finRotate n).IsCycleOn Set.univ := by
    cases n with
    | zero => omega
    | succ n => exact BlockEnumeration.finRotate_isCycleOn n
  have h := (hc C.length (by have := C.length_ge; omega)).2
    (Set.mem_univ i) (Set.mem_univ j)
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  exact ⟨n, by simpa only [Equiv.Perm.coe_pow] using hn⟩

/-- Fixing the direction of one marked edge determines the start of every
labelled mixed edge, regardless of the chosen cyclic parametrisation. -/
theorem slot_start_eq_of_root (C D : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (root : ↥markers) (hroot : C.markerStart root = D.markerStart root)
    (e : ↥markers ⊕ ↥edges) :
    C.junction (C.slot.symm e) = D.junction (D.slot.symm e) := by
  let i := C.slot.symm (.inl root)
  let j := D.slot.symm (.inl root)
  have hs : C.slotSet i = D.slotSet j := by simp [slotSet, i, j]
  have hv : C.junction i = D.junction j := congrArg Subtype.val hroot
  obtain ⟨n, hn⟩ := C.exists_rotate_iterate i (C.slot.symm e)
  obtain ⟨he, hj⟩ := C.iterate_eq D hr i j hs hv n
  rw [hn] at he hj
  have hd : (finRotate D.length)^[n] j = D.slot.symm e := by
    apply D.slotSet_injective hr
    rw [← he]
    simp [slotSet]
  rwa [hd] at hj

/-- All marker directions agree in two presentations oriented by the same root. -/
theorem markerDirections_eq_of_root (C D : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (root : ↥markers) (hroot : C.markerStart root = D.markerStart root) :
    C.markerDirections root.val = D.markerDirections root.val := by
  funext e
  apply Subtype.ext
  exact C.slot_start_eq_of_root D hr root hroot (.inl ⟨e.val, mem_of_mem_erase e.property⟩)

/-- In particular normalization removes the orientation ambiguity completely. -/
theorem normalized_slot_start_eq (C D : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (root : ↥markers) (a : ↥root.val) (e : ↥markers ⊕ ↥edges) :
    (C.normalize root a).junction ((C.normalize root a).slot.symm e) =
      (D.normalize root a).junction ((D.normalize root a).slot.symm e) := by
  apply slot_start_eq_of_root _ _ hr root
  rw [C.normalize_markerStart, D.normalize_markerStart]

theorem slot_end_eq_of_root (C D : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (root : ↥markers) (hroot : C.markerStart root = D.markerStart root)
    (e : ↥markers ⊕ ↥edges) :
    C.junction (finRotate C.length (C.slot.symm e)) =
      D.junction (finRotate D.length (D.slot.symm e)) := by
  apply C.next_junction_eq D hr
  · simp [slotSet]
  · exact C.slot_start_eq_of_root D hr root hroot e

/-- Normalized orientation fixes the entire successor permutation of mixed labels. -/
theorem mixedSuccessor_eq_of_root (C D : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (root : ↥markers) (hroot : C.markerStart root = D.markerStart root) :
    C.mixedSuccessor = D.mixedSuccessor := by
  ext e
  let a := e.swap
  let c := C.slot (finRotate C.length (C.slot.symm a))
  let d := D.slot (finRotate D.length (D.slot.symm a))
  have hv : C.junction (C.slot.symm c) = D.junction (D.slot.symm d) := by
    simpa only [c, d, Equiv.symm_apply_apply] using C.slot_end_eq_of_root D hr root hroot a
  have hd := C.slot_start_eq_of_root D hr root hroot d
  have he : c = d := C.slot.symm.injective (C.junction_injective (hv.trans hd.symm))
  exact congrArg Sum.swap he

/-- Contracted ordinary-edge successor also is independent of parametrisation. -/
theorem ordinarySuccessor_eq_of_root (C D : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (root : ↥markers) (hroot : C.markerStart root = D.markerStart root) :
    C.ordinarySuccessor = D.ordinarySuccessor := by
  unfold ordinarySuccessor
  congr 1
  exact C.mixedSuccessor_eq_of_root D hr root hroot

end LooseHamilton.MixedCycleWitness
