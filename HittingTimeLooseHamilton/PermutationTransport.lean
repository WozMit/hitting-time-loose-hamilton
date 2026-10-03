module

public import HittingTimeLooseHamilton.RootedPermutation
public import HittingTimeLooseHamilton.Contraction
public import HittingTimeLooseHamilton.SkipPermutation

public section
noncomputable section
namespace LooseHamilton

/-- Relabel a permutation by an arbitrary equivalence. -/
@[expose] def permutationTransport {A B : Type*} (e : A ≃ B) : Equiv.Perm A →* Equiv.Perm B where
  toFun := e.permCongr
  map_one' := by ext x; simp
  map_mul' σ τ := by ext x; simp [Equiv.Perm.mul_apply]

@[simp] theorem permutationTransport_apply {A B : Type*} (e : A ≃ B)
    (σ : Equiv.Perm A) (x : B) : permutationTransport e σ x = e (σ (e.symm x)) := rfl

/-- Being a full cyclic permutation is invariant under relabelling. -/
theorem permutationTransport_cycle {A B : Type*} (e : A ≃ B)
    (σ : Equiv.Perm A) (h : σ.IsCycleOn Set.univ) :
    (permutationTransport e σ).IsCycleOn Set.univ := by
  refine ⟨(permutationTransport e σ).bijective.bijOn_univ, ?_⟩
  intro x _ y _
  obtain ⟨n, hn⟩ := h.2 (Set.mem_univ (e.symm x)) (Set.mem_univ (e.symm y))
  refine ⟨n, ?_⟩
  rw [← map_zpow]
  change e ((σ ^ n) (e.symm x)) = y
  rw [hn, e.apply_symm_apply]

namespace MixedCycleWitness
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}

/-- Successor of mixed edge labels, with ordinary edges in the left summand. -/
@[expose] def mixedSuccessor (C : MixedCycleWitness r markers edges) : Equiv.Perm (↥edges ⊕ ↥markers) :=
  permutationTransport (C.slot.trans (Equiv.sumComm _ _)) (finRotate C.length)

theorem mixedSuccessor_cycle (C : MixedCycleWitness r markers edges) :
    C.mixedSuccessor.IsCycleOn Set.univ := by
  apply permutationTransport_cycle
  have h (n : ℕ) (hn : 0 < n) : (finRotate n).IsCycleOn Set.univ := by
    cases n with
    | zero => omega
    | succ n => exact BlockEnumeration.finRotate_isCycleOn n
  exact h C.length (by have := C.length_ge; omega)

theorem mixedSuccessor_separated (C : MixedCycleWitness r markers edges) :
    BlockEnumeration.Separated C.mixedSuccessor := by
  intro e
  obtain ⟨f, hf⟩ := C.ordinary_after_marker (C.slot.symm (Sum.inl e)) e
    (C.slot.apply_symm_apply _)
  refine ⟨f, ?_⟩
  change (C.slot (finRotate C.length (C.slot.symm (Sum.inl e)))).swap = Sum.inl f
  rw [hf]
  rfl

/-- The cyclic order on ordinary edges after contracting the marked slots. -/
@[expose] def ordinarySuccessor (C : MixedCycleWitness r markers edges) : Equiv.Perm ↥edges :=
  BlockEnumeration.skipPermutation C.mixedSuccessor C.mixedSuccessor_separated

theorem ordinarySuccessor_cycle (C : MixedCycleWitness r markers edges) :
    C.ordinarySuccessor.IsCycleOn Set.univ :=
  BlockEnumeration.skipPermutation_isCycleOn _ _ C.mixedSuccessor_cycle

/-- The full cyclic order of contracted blocks. -/
@[expose] def blockSuccessor (C : MixedCycleWitness r markers edges) : Equiv.Perm C.ContractedBlock :=
  permutationTransport C.blockEdgeEquiv.symm C.ordinarySuccessor

theorem blockSuccessor_cycle (C : MixedCycleWitness r markers edges) :
    C.blockSuccessor.IsCycleOn Set.univ :=
  permutationTransport_cycle _ _ C.ordinarySuccessor_cycle

end MixedCycleWitness
end LooseHamilton
