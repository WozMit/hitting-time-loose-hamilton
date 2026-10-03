module

public import HittingTimeLooseHamilton.BiasedCloneConditionalKahn

public section

/-! A common Kahn vertex count for every attained role fibre. -/
noncomputable section
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers G : SimpleHypergraph V}

theorem biasedCloneUniverse_card (hr : 3 ≤ r) (root : ↥markers) (a : ↥root.val)
    (C₀ : BiasedCycleState r markers G) :
    (biasedCloneUniverse root a C₀).card =
      r * ((Fintype.card V - markers.card) / (r-1)) := by
  rw [biasedCloneUniverse, MixedCycleWitness.cloneVertices_card _ hr]
  congr 1
  exact (biasedConnectedCycle C₀).property.edge_card hr

/-- Canonical relabelling to the same `r*k` vertices for all role fibres. -/
@[expose] def biasedCloneSlotEquiv (hr : 3 ≤ r) (root : ↥markers) (a : ↥root.val)
    (C₀ : BiasedCycleState r markers G) :
    ↥(biasedCloneUniverse root a C₀) ≃
      Fin (r * ((Fintype.card V - markers.card) / (r-1))) :=
  (Fintype.equivFin _).trans (finCongr (by simpa using biasedCloneUniverse_card hr root a C₀))

end LooseHamilton
