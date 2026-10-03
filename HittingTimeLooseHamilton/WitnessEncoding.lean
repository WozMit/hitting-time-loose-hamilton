module

public import HittingTimeLooseHamilton.CycleAllocation
public import HittingTimeLooseHamilton.PermutationTransport
public import HittingTimeLooseHamilton.CycleNormalization

public section

/-! Extraction of the finite complete-host data from an actual directed cycle. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Canonical labels shared by the encoder and decoder; no cyclic presentation
is involved in this choice. -/
@[expose] def codeBlockLabels (markers : Finset (Finset V)) (k : ℕ) (hsk : markers.card ≤ k)
    (J : ↥(ordinaryJunctionChoices markers k)) :
    (↥markers ⊕ ↥J.val) ≃ Fin k :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, Fintype.card_fin]
    rw [((mem_ordinaryJunctionChoices _ _ _).mp J.property).2]
    exact Nat.add_sub_of_le hsk)

/-- Arbitrary positive-cardinality version of the rooted permutation equivalence. -/
@[expose] def rootedOrderCycleEquiv (k : ℕ) (hk : 0 < k) :
    BlockEnumeration.RootedOrder k ≃ BlockEnumeration.FullCycle (Fin k) := by
  let h : k - 1 + 1 = k := Nat.sub_add_cancel hk
  let e : Fin (k - 1 + 1) ≃ Fin k := finCongr h
  let f : BlockEnumeration.FullCycle (Fin (k - 1 + 1)) ≃
      BlockEnumeration.FullCycle (Fin k) := {
    toFun := fun σ => ⟨permutationTransport e σ.val, permutationTransport_cycle _ _ σ.property⟩
    invFun := fun σ => ⟨permutationTransport e.symm σ.val,
      permutationTransport_cycle _ _ σ.property⟩
    left_inv := by intro σ; apply Subtype.ext; ext x; simp
    right_inv := by intro σ; apply Subtype.ext; ext x; simp }
  exact (BlockEnumeration.rootedOrderFullCycleEquiv (k - 1)).trans f

namespace MixedCycleWitness
variable {r : ℕ} {markers edges : Finset (Finset V)}

/-- A directed presentation determines complete-host enumeration data. To encode
unoriented edge sets uniquely, first orient a fixed marked pair. -/
@[expose] def toCompleteHostCode (C : MixedCycleWitness r markers edges) (root : Finset V) :
    CompleteHostCode r edges.card markers root := by
  let J := C.ordinaryJunctionChoice
  let labels : C.ContractedBlock ≃ Fin edges.card :=
    codeBlockLabels markers edges.card C.markers_card_le_edges_card J
  let σ : BlockEnumeration.FullCycle (Fin edges.card) :=
    ⟨permutationTransport labels C.blockSuccessor,
      permutationTransport_cycle _ _ C.blockSuccessor_cycle⟩
  exact ⟨J, C.markerDirections root,
    (rootedOrderCycleEquiv edges.card C.edges_card_pos).symm σ,
    C.privateAllocation labels⟩

@[simp] theorem toCompleteHostCode_junctions (C : MixedCycleWitness r markers edges)
    (root : Finset V) : (C.toCompleteHostCode root).1 = C.ordinaryJunctionChoice := rfl

@[simp] theorem toCompleteHostCode_directions (C : MixedCycleWitness r markers edges)
    (root : Finset V) : (C.toCompleteHostCode root).2.1 = C.markerDirections root := rfl

end MixedCycleWitness

/-- Encode an actual unoriented cycle after fixing the first endpoint of one
marked pair. No arbitrary orientation choice remains in the construction. -/
@[expose] def IsMixedCycle.encode {r : ℕ} {markers edges : Finset (Finset V)}
    (h : IsMixedCycle r markers edges) (root : ↥markers) (a : ↥root.val) :
    CompleteHostCode r edges.card markers root.val :=
  (h.some.normalize root a).toCompleteHostCode root.val

end LooseHamilton
