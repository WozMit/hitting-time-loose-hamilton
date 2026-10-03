module

public import HittingTimeLooseHamilton.EnumerationBridge
public import HittingTimeLooseHamilton.CycleReversal

public section
noncomputable section
namespace LooseHamilton.MixedCycleWitness
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}
/-- Choose the direction of traversal so a prescribed marker starts at its prescribed port. -/
@[expose] def normalize (C : MixedCycleWitness r markers edges) (root : ↥markers) (a : ↥root.val) :
    MixedCycleWitness r markers edges :=
  if C.markerStart root = a then C else C.reverse

theorem normalize_markerStart (C : MixedCycleWitness r markers edges)
    (root : ↥markers) (a : ↥root.val) : (C.normalize root a).markerStart root = a := by
  unfold normalize
  split_ifs with h
  · exact h
  · apply Subtype.ext
    change C.reverse.junction (C.reverse.slot.symm (.inl root)) = a.val
    rw [C.reverse_slot_start]
    have hs := C.slot_edge (C.slot.symm (.inl root))
    rw [C.slot.apply_symm_apply] at hs
    simp only at hs
    have ha := a.property
    simp only [hs] at ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with ha | ha
    · exact False.elim (h (Subtype.ext ha.symm))
    · exact ha.symm
end LooseHamilton.MixedCycleWitness
