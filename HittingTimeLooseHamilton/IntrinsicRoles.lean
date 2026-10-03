module

public import HittingTimeLooseHamilton.EnumerationBridge

public section

/-! # Intrinsic junction and private-vertex sets
These definitions use only the unoriented edge sets, not a selected presentation.
-/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices lying in at least two distinct mixed edges. -/
@[expose] def cycleJunctions (markers edges : Finset (Finset V)) : Finset V :=
  univ.filter fun v => ∃ e ∈ markers ∪ edges, ∃ f ∈ markers ∪ edges,
    e ≠ f ∧ v ∈ e ∧ v ∈ f

/-- The ordinary junctions exclude all originally prescribed marker endpoints. -/
@[expose] def ordinaryJunctions (markers edges : Finset (Finset V)) : Finset V :=
  cycleJunctions markers edges \ originalPorts markers

/-- The private part of an ordinary edge, recovered from the whole cycle. -/
@[expose] def cyclePrivateBlock (markers edges : Finset (Finset V)) (e : Finset V) : Finset V :=
  e \ cycleJunctions markers edges

namespace MixedCycleWitness
variable {r : ℕ} {markers edges : Finset (Finset V)}

theorem cycleJunctions_eq (C : MixedCycleWitness r markers edges) (hr : 3 ≤ r) :
    cycleJunctions markers edges = univ.image C.junction := by
  ext v
  simp only [cycleJunctions, mem_filter, mem_univ, true_and]
  exact (C.mem_junctions_iff hr v).symm

theorem cyclePrivateBlock_eq (C : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (e : ↥edges) : cyclePrivateBlock markers edges e.val = C.privateBlock e := by
  rw [cyclePrivateBlock, C.cycleJunctions_eq hr, C.private_eq_sdiff_junctions]

end MixedCycleWitness

namespace IsMixedCycle
variable {r : ℕ} {markers edges : Finset (Finset V)}

/-- Intrinsic ordinary junctions have exactly the required cardinality and avoid
all marked ports, so they determine the binomial-choice component of an encoding. -/
theorem ordinaryJunctions_mem (h : IsMixedCycle r markers edges) (hr : 3 ≤ r) :
    ordinaryJunctions markers edges ∈ ordinaryJunctionChoices markers edges.card := by
  obtain ⟨C⟩ := h
  simpa only [ordinaryJunctions, C.cycleJunctions_eq hr, MixedCycleWitness.ordinaryJunctionChoice, originalPorts]
    using C.ordinaryJunctionChoice.property

theorem cycleJunctions_card (h : IsMixedCycle r markers edges) (hr : 3 ≤ r) :
    (cycleJunctions markers edges).card = edges.card + markers.card := by
  obtain ⟨C⟩ := h
  rw [C.cycleJunctions_eq hr, C.junction_card, C.length_eq, Nat.add_comm]

theorem cyclePrivateBlock_card (h : IsMixedCycle r markers edges) (hr : 3 ≤ r)
    (e : ↥edges) : (cyclePrivateBlock markers edges e.val).card = r - 2 := by
  obtain ⟨C⟩ := h
  rw [C.cyclePrivateBlock_eq hr e, C.private_card]

end IsMixedCycle
end LooseHamilton
