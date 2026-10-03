module

public import HittingTimeLooseHamilton.ActiveCycleRoles
public import HittingTimeLooseHamilton.CycleReversal

public section
noncomputable section
open Finset
namespace LooseHamilton.MixedCycleOnWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset V)}

/-- Reverse the traversal while preserving all unoriented edge sets. -/
@[expose] def reverse (C : MixedCycleOnWitness r S markers edges) : MixedCycleOnWitness r S markers edges := by
  letI : NeZero C.length := ⟨by have := C.length_ge; omega⟩
  let ρ : Equiv.Perm (Fin C.length) := Equiv.neg _
  let θ : Equiv.Perm (Fin C.length) := ρ.trans (finRotate C.length).symm
  have hθ (i) : θ i = -(finRotate C.length i) := (MixedCycleWitness.negate_rotate i).symm
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
  · apply C.cover.trans
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
    have hp : ρ (finRotate C.length i) = θ i := MixedCycleWitness.negate_rotate i
    simp only [Equiv.trans_apply]
    rw [hn] at hs
    rw [hp]
    simpa [pair_comm] using hs

@[simp] theorem reverse_length (C : MixedCycleOnWitness r S markers edges) :
    C.reverse.length = C.length := rfl

theorem reverse_slot_start (C : MixedCycleOnWitness r S markers edges)
    (e : {e // e ∈ markers} ⊕ {e // e ∈ edges}) :
    C.reverse.junction (C.reverse.slot.symm e) =
      C.junction (finRotate C.length (C.slot.symm e)) := by
  letI : NeZero C.length := ⟨by have := C.length_ge; omega⟩
  change C.junction (-(-(finRotate C.length (C.slot.symm e)))) = _
  rw [neg_neg]

theorem reverse_slot_end (C : MixedCycleOnWitness r S markers edges)
    (e : {e // e ∈ markers} ⊕ {e // e ∈ edges}) :
    C.reverse.junction (finRotate C.reverse.length (C.reverse.slot.symm e)) =
      C.junction (C.slot.symm e) := by
  letI : NeZero C.length := ⟨by have := C.length_ge; omega⟩
  change C.junction (-(finRotate C.length
    (-finRotate C.length (C.slot.symm e)))) = _
  rw [MixedCycleWitness.negate_rotate]
  simp

/-- Orient a marked root by its prescribed first endpoint. -/
@[expose] def orient (C : MixedCycleOnWitness r S markers edges) (root : ↥markers) (a : ↥root.val) :
    MixedCycleOnWitness r S markers edges :=
  if C.junction (C.slot.symm (.inl root)) = a.val then C else C.reverse

theorem orient_start (C : MixedCycleOnWitness r S markers edges)
    (root : ↥markers) (a : ↥root.val) :
    (C.orient root a).junction ((C.orient root a).slot.symm (.inl root)) = a.val := by
  by_cases h : C.junction (C.slot.symm (.inl root)) = a.val
  · have ho : C.orient root a = C := if_pos h
    rw [ho]
    exact h
  · have ho : C.orient root a = C.reverse := if_neg h
    rw [ho]
    rw [C.reverse_slot_start]
    have hs := C.slot_edge (C.slot.symm (.inl root))
    rw [C.slot.apply_symm_apply] at hs
    simp only at hs
    have ha := a.property
    simp only [hs] at ha
    rcases mem_insert.mp ha with ha | ha
    · exact False.elim (h ha.symm)
    · exact (mem_singleton.mp ha).symm

/-- Move an arbitrary cyclic position to position zero. -/
@[expose] def shift (C : MixedCycleOnWitness r S markers edges) (a : Fin C.length) :
    MixedCycleOnWitness r S markers edges := by
  letI : NeZero C.length := ⟨by have := C.length_ge; omega⟩
  let ρ : Equiv.Perm (Fin C.length) := Equiv.addRight a
  have hρ (i) : ρ (finRotate C.length i) = finRotate C.length (ρ i) := by
    change (finRotate C.length i) + a = finRotate C.length (i + a)
    have aux {n : ℕ} [NeZero n] (i a : Fin n) :
        (finRotate n i) + a = finRotate n (i + a) := by
      cases n with
      | zero => exact Fin.elim0 i
      | succ n => simp only [finRotate_succ_apply]; ac_rfl
    exact aux i a
  refine {
    length := C.length
    length_ge := C.length_ge
    junction := fun i => C.junction (ρ i)
    junction_injective := C.junction_injective.comp ρ.injective
    junction_next_ne := ?_
    slot := ρ.trans C.slot
    privateBlock := C.privateBlock
    private_card := C.private_card
    private_disjoint := C.private_disjoint
    junction_private_disjoint := ?_
    cover := ?_
    marked_matching := C.marked_matching
    slot_edge := ?_ }
  · intro i h
    rw [hρ] at h
    exact C.junction_next_ne _ h
  · intro e
    apply (C.junction_private_disjoint e).mono_left
    intro v hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    exact mem_image_of_mem _ (mem_univ _)
  · apply C.cover.trans
    congr 1
    ext v
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨ρ.symm i, by simp⟩
    · rintro ⟨i, rfl⟩
      exact ⟨ρ i, rfl⟩
  · intro i
    simpa only [Equiv.trans_apply, hρ] using C.slot_edge (ρ i)

@[simp] theorem shift_length (C : MixedCycleOnWitness r S markers edges) (a : Fin C.length) :
    (C.shift a).length = C.length := rfl

theorem shift_zero (C : MixedCycleOnWitness r S markers edges) (a : Fin C.length) :
    (C.shift a).junction ⟨0, by have := C.length_ge; change 0 < C.length; omega⟩ = C.junction a := by
  letI : NeZero C.length := ⟨by have := C.length_ge; omega⟩
  change C.junction ((0 : Fin C.length) + a) = C.junction a
  rw [zero_add]

theorem shift_slot_zero (C : MixedCycleOnWitness r S markers edges) (a : Fin C.length) :
    (C.shift a).slot ⟨0, by have := C.length_ge; change 0 < C.length; omega⟩ = C.slot a := by
  letI : NeZero C.length := ⟨by have := C.length_ge; omega⟩
  change C.slot ((0 : Fin C.length) + a) = C.slot a
  rw [zero_add]

/-- Rotation is the usual successor before the last cyclic position. -/
theorem rotate_mk_succ {n k : ℕ} (hk : k + 1 < n) :
    finRotate n ⟨k, by omega⟩ = ⟨k + 1, hk⟩ := by
  cases n with
  | zero => omega
  | succ n => exact finRotate_of_lt (by omega)

/-- Every marked cycle admits the prescribed rooted direction. -/
theorem exists_rooted (C : MixedCycleOnWitness r S markers edges)
    (root : ↥markers) (z y : V) (hroot : root.val = {z,y}) (hzy : z ≠ y) :
    ∃ D : MixedCycleOnWitness r S markers edges,
      D.slot ⟨0, by have := D.length_ge; omega⟩ = .inl root ∧
      D.junction ⟨0, by have := D.length_ge; omega⟩ = z ∧
      D.junction ⟨1, by have := D.length_ge; omega⟩ = y := by
  have hz : z ∈ root.val := by simp [hroot]
  let E := C.orient root ⟨z,hz⟩
  let i := E.slot.symm (.inl root)
  let D := E.shift i
  have hslot : D.slot ⟨0, by have := D.length_ge; omega⟩ = .inl root := by
    change (E.shift i).slot _ = _
    rw [E.shift_slot_zero]
    exact E.slot.apply_symm_apply _
  have hzero : D.junction ⟨0, by have := D.length_ge; omega⟩ = z := by
    change (E.shift i).junction _ = _
    rw [E.shift_zero]
    exact C.orient_start root ⟨z,hz⟩
  refine ⟨D,hslot,hzero,?_⟩
  have hs := D.slot_edge ⟨0, by have := D.length_ge; omega⟩
  rw [hslot] at hs
  simp only at hs
  rw [rotate_mk_succ (by have := D.length_ge; omega), hzero, hroot] at hs
  have hy : y ∈ ({z,y} : Finset V) := by simp
  rw [hs] at hy
  rcases mem_insert.mp hy with hy | hy
  · exact False.elim (hzy hy.symm)
  · exact (mem_singleton.mp hy).symm

end LooseHamilton.MixedCycleOnWitness
