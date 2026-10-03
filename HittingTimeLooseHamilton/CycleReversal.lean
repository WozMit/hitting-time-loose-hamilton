module

public import HittingTimeLooseHamilton.Cycles

public section
noncomputable section
open Finset
namespace LooseHamilton.MixedCycleWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}

lemma negate_rotate {n : ℕ} [NeZero n] (i : Fin n) :
    -(finRotate n i) = (finRotate n).symm (-i) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [finRotate_succ_apply, finRotate_succ_symm_apply]
  abel

/-- Reverse the traversal while preserving all unoriented edge sets. -/
@[expose] def reverse (C : MixedCycleWitness r markers edges) : MixedCycleWitness r markers edges := by
  letI : NeZero C.length := ⟨by have := C.length_ge; omega⟩
  let ρ : Equiv.Perm (Fin C.length) := Equiv.neg _
  let θ : Equiv.Perm (Fin C.length) := ρ.trans (finRotate C.length).symm
  have hθ (i) : θ i = -(finRotate C.length i) := (negate_rotate i).symm
  refine {
    length := C.length
    length_ge := C.length_ge
    junction := fun i => C.junction (ρ i)
    junction_injective := C.junction_injective.comp ρ.injective
    junction_next_ne := ?_
    slot := θ.trans C.slot
    privateBlock := C.privateBlock
    private_card := C.private_card
    private_disjoint := C.private_disjoint
    junction_private_disjoint := ?_
    cover := ?_
    marked_matching := C.marked_matching
    slot_edge := ?_ }
  · intro i h
    have he := C.junction_injective h
    have hi := ρ.injective he
    exact C.junction_next_ne i (congrArg C.junction hi)
  · intro e
    apply (C.junction_private_disjoint e).mono_left
    intro v hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    exact mem_image_of_mem _ (mem_univ _)
  · rw [C.cover]
    congr 1
    ext v
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨ρ.symm i, by simp⟩
    · rintro ⟨i, rfl⟩
      exact ⟨ρ i, rfl⟩
  · intro i
    have hs := C.slot_edge (θ i)
    have hn : finRotate C.length (θ i) = ρ i := (finRotate C.length).apply_symm_apply _
    have hp : ρ (finRotate C.length i) = θ i := negate_rotate i
    simp only [Equiv.trans_apply]
    rw [hn] at hs
    rw [hp]
    simpa [pair_comm] using hs

@[simp] theorem reverse_length (C : MixedCycleWitness r markers edges) :
    C.reverse.length = C.length := rfl

theorem reverse_slot_start (C : MixedCycleWitness r markers edges)
    (e : {e // e ∈ markers} ⊕ {e // e ∈ edges}) :
    C.reverse.junction (C.reverse.slot.symm e) =
      C.junction (finRotate C.length (C.slot.symm e)) := by
  letI : NeZero C.length := ⟨by have := C.length_ge; omega⟩
  change C.junction (-(-(finRotate C.length (C.slot.symm e)))) = _
  rw [neg_neg]

theorem reverse_slot_end (C : MixedCycleWitness r markers edges)
    (e : {e // e ∈ markers} ⊕ {e // e ∈ edges}) :
    C.reverse.junction (finRotate C.reverse.length (C.reverse.slot.symm e)) =
      C.junction (C.slot.symm e) := by
  letI : NeZero C.length := ⟨by have := C.length_ge; omega⟩
  change C.junction (-(finRotate C.length
    (-finRotate C.length (C.slot.symm e)))) = _
  rw [negate_rotate]
  simp

end LooseHamilton.MixedCycleWitness
