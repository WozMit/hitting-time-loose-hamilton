module

public import HittingTimeLooseHamilton.CoreBlockLifting
public import HittingTimeLooseHamilton.CycleOnCounting

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

namespace CoreBlockFamily
variable {r : ℕ} {F : SimpleHypergraph V} {B : Finset V}

theorem looseHamilton_of_induced_cycle (C : CoreBlockFamily r F B) (hr : 3 ≤ r)
    {E : SimpleHypergraph ↥C.coreVertices}
    (hcycle : IsMixedCycle r (restrictEdges C.coreVertices C.markers) E)
    (hE : E ⊆ inducedHost C.coreVertices F) : HasLooseHamiltonCycle r F := by
  obtain ⟨W⟩ := hcycle
  have hM : ∀ p ∈ C.markers, p ⊆ C.coreVertices := by
    intro p hp
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hp
    exact C.ports_core v
  have hw := W.lift
  rw [liftEdges_restrictEdges C.coreVertices C.markers hM] at hw
  exact C.looseHamilton_of_core_cycle hr ⟨hw⟩
    (liftEdges_subset_host C.coreVertices E F hE)

theorem looseHamilton_of_positive_core_count (C : CoreBlockFamily r F B) (hr : 3 ≤ r)
    (ports : Finset ↥C.coreVertices)
    (h : 0 < cycleCount r (restrictEdges C.coreVertices C.markers)
      (inducedHost C.coreVertices F) ports) : HasLooseHamiltonCycle r F := by
  obtain ⟨E,hcycle,hE,_⟩ := (cycleCount_pos_iff _ _ _ _).mp h
  exact C.looseHamilton_of_induced_cycle hr hcycle hE

/-- Disjoint retained pairs provide a deterministic lower bound on core size. -/
theorem twice_anchors_le_core (C : CoreBlockFamily r F B) :
    2 * B.card ≤ C.coreVertices.card := by
  have hc : ((univ : Finset ↥B).biUnion C.ports).card = 2 * B.card := by
    rw [card_biUnion (by intro u _ v _ h; exact C.ports_disjoint h)]
    simp [C.ports_card,Nat.mul_comm]
  rw [← hc]
  apply card_le_card
  intro v hv
  obtain ⟨b,hb,hv⟩ := mem_biUnion.mp hv
  exact C.ports_core b hv

/-- No exceptional-set estimate is required to pass a large original order to
a large core: every deleted block retains two disjoint vertices. -/
theorem ambient_card_le_mul_core (C : CoreBlockFamily r F B) (hr : 3 ≤ r) :
    Fintype.card V ≤ r * C.coreVertices.card := by
  have hd : C.deleted.card ≤ Fintype.card V := card_le_univ _
  have he : C.coreVertices.card + (r-2)*B.card = Fintype.card V := by
    rw [C.coreVertices_card]
    rw [C.deleted_card] at hd
    exact Nat.sub_add_cancel hd
  have hb : B.card ≤ C.coreVertices.card := by have := C.twice_anchors_le_core; omega
  have hm := Nat.mul_le_mul_left (r-2) hb
  have hr' : r-2+1 ≤ r := by omega
  calc
    Fintype.card V = C.coreVertices.card+(r-2)*B.card := he.symm
    _ ≤ C.coreVertices.card+(r-2)*C.coreVertices.card := Nat.add_le_add_left hm _
    _ = (r-2+1)*C.coreVertices.card := by ring
    _ ≤ r*C.coreVertices.card := Nat.mul_le_mul_right _ hr'

theorem core_card_ge_of_ambient_large (C : CoreBlockFamily r F B) (hr : 3 ≤ r)
    (N₀ : ℕ) (hn : r*N₀ ≤ Fintype.card V) : N₀ ≤ C.coreVertices.card := by
  have h := hn.trans (C.ambient_card_le_mul_core hr)
  exact Nat.le_of_mul_le_mul_left h (by omega)
end CoreBlockFamily

/-- Expanding a cycle in the actual induced core at the disappearance of the
last isolated vertex proves exact equality of the two finite hitting times. -/
theorem hittingTimeEvent_of_core_count {r t : ℕ} (hr : 3 ≤ r)
    (σ : EdgeOrder V r) (ht : tauOne σ = (t : WithTop ℕ))
    {B : Finset V} (C : CoreBlockFamily r (processState σ t) B)
    (ports : Finset ↥C.coreVertices)
    (h : 0 < cycleCount r (restrictEdges C.coreVertices C.markers)
      (inducedHost C.coreVertices (processState σ t)) ports) : hittingTimeEvent σ := by
  have hs := firstTime_spec (completeEdges V r).card (processState σ) NoIsolated ht
  have hcycle := C.looseHamilton_of_positive_core_count hr ports h
  apply le_antisymm
  · rw [ht]
    exact firstTime_le _ _ _ hs.1 hcycle
  · exact tauOne_le_tauLooseHamilton σ
end LooseHamilton
