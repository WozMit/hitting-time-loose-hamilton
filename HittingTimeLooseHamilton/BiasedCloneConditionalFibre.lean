module

public import HittingTimeLooseHamilton.BiasedRoleProjection
public import HittingTimeLooseHamilton.BiasedCloneConditionalLaw
public import HittingTimeLooseHamilton.BiasedCloneKahnLaw

public section

/-! Actual role fibres of the host's connected-cycle sample space. -/
noncomputable section
open Finset FiniteEntropy
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers G : SimpleHypergraph V}

@[expose] def biasedCloneRole (root : ↥markers) (a : ↥root.val) (C : BiasedCycleState r markers G) :=
  ConnectedCloneCycle.role root a (biasedConnectedCycle C)

@[expose] def biasedCloneLift (root : ↥markers) (a : ↥root.val) (C : BiasedCycleState r markers G) :=
  ConnectedCloneCycle.lift root a (biasedConnectedCycle C)

abbrev BiasedCloneFibre (root : ↥markers) (a : ↥root.val)
    (C₀ : BiasedCycleState r markers G) :=
  {C : BiasedCycleState r markers G // biasedCloneRole root a C = biasedCloneRole root a C₀}

@[expose] def biasedCloneUniverse (root : ↥markers) (a : ↥root.val)
    (C₀ : BiasedCycleState r markers G) :=
  ((biasedConnectedCycle C₀).directedWitness root a).cloneVertices

theorem biasedCloneLift_injective (root : ↥markers) (a : ↥root.val) :
    Function.Injective (biasedCloneLift root a : BiasedCycleState r markers G → _) :=
  (ConnectedCloneCycle.lift_injective root a).comp biasedConnectedCycle_injective

theorem biasedCloneFibre_universe (root : ↥markers) (a : ↥root.val)
    (C₀ : BiasedCycleState r markers G) (C : BiasedCloneFibre root a C₀) :
    ((biasedConnectedCycle C.val).directedWitness root a).cloneVertices =
      biasedCloneUniverse root a C₀ :=
  ConnectedCloneCycle.cloneVertices_eq_of_role root a C.property

theorem biasedCloneFibre_partition (hr : 3 ≤ r) (root : ↥markers) (a : ↥root.val)
    (C₀ : BiasedCycleState r markers G) (C : BiasedCloneFibre root a C₀) :
    (∀ B ∈ biasedCloneLift root a C.val, B.card = r) ∧
      ∀ v ∈ biasedCloneUniverse root a C₀,
        ∃! B, B ∈ biasedCloneLift root a C.val ∧ v ∈ B := by
  have h := (biasedConnectedCycle C.val).lift_partition hr root a
  rw [biasedCloneFibre_universe root a C₀ C] at h
  exact h

theorem biasedCloneFibre_subset (root : ↥markers) (a : ↥root.val)
    (C₀ : BiasedCycleState r markers G) (C : BiasedCloneFibre root a C₀)
    (B : Finset (V × Fin 3)) (hB : B ∈ biasedCloneLift root a C.val) :
    B ⊆ biasedCloneUniverse root a C₀ := by
  rw [← biasedCloneFibre_universe root a C₀ C]
  obtain ⟨e, _, rfl⟩ := mem_image.mp hB
  intro v hv
  exact mem_biUnion.mpr ⟨e, mem_univ _, hv⟩

end LooseHamilton
