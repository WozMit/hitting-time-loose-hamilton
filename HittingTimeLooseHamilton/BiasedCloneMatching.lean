module

public import HittingTimeLooseHamilton.BiasedCloneRepresentation

public section

/-! The connected cycle lift is an actual partition into uniform clone edges,
with exactly `r * k` active clone slots. -/
noncomputable section
open Finset
namespace LooseHamilton.MixedCycleWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}

@[expose] def cloneVertices (C : MixedCycleWitness r markers edges) : Finset (V × Fin 3) :=
  univ.biUnion C.cloneEdge

theorem cloneVertices_card (C : MixedCycleWitness r markers edges) (hr : 3 ≤ r) :
    C.cloneVertices.card = r * edges.card := by
  rw [cloneVertices, card_biUnion]
  · simp [C.cloneEdge_card hr, Nat.mul_comm]
  · intro e _ f _ hef
    exact C.cloneEdge_disjoint hef

/-- Every active slot belongs to a unique lifted ordinary edge. -/
theorem cloneMatching_unique_incident (C : MixedCycleWitness r markers edges)
    (v : V × Fin 3) (hv : v ∈ C.cloneVertices) :
    ∃! B, B ∈ C.cloneMatching ∧ v ∈ B := by
  obtain ⟨e, _, he⟩ := mem_biUnion.mp hv
  refine ⟨C.cloneEdge e, ⟨mem_image_of_mem _ (mem_univ _), he⟩, ?_⟩
  intro B hB
  obtain ⟨f, _, rfl⟩ := mem_image.mp hB.1
  by_cases h : f = e
  · exact congrArg C.cloneEdge h
  · exact False.elim (disjoint_left.mp (C.cloneEdge_disjoint h) hB.2 he)

/-- Uniformity and exact coverage, the defining properties of a perfect matching. -/
theorem cloneMatching_is_partition (C : MixedCycleWitness r markers edges) (hr : 3 ≤ r) :
    (∀ B ∈ C.cloneMatching, B.card = r) ∧
      (∀ v ∈ C.cloneVertices, ∃! B, B ∈ C.cloneMatching ∧ v ∈ B) := by
  constructor
  · intro B hB
    obtain ⟨e, _, rfl⟩ := mem_image.mp hB
    exact C.cloneEdge_card hr e
  · exact C.cloneMatching_unique_incident

/-- Forgetting slot tags recovers the original connected cycle exactly. -/
theorem cloneMatching_recovers {edges' : Finset (Finset V)}
    (C : MixedCycleWitness r markers edges) (D : MixedCycleWitness r markers edges')
    (h : C.cloneMatching = D.cloneMatching) : edges = edges' := by
  have hp := congrArg (fun F : Finset (Finset (V × Fin 3)) =>
    F.image (fun B => B.image Prod.fst)) h
  simpa only [C.cloneMatching_project, D.cloneMatching_project] using hp

/-- The canonical root-normalised lift is independent of all presentation choices. -/
theorem normalized_cloneMatching_eq (C D : MixedCycleWitness r markers edges)
    (hr : 3 ≤ r) (root : ↥markers) (a : ↥root.val) :
    (C.normalize root a).cloneMatching = (D.normalize root a).cloneMatching := by
  apply cloneMatching_eq_of_root _ _ hr root
  rw [C.normalize_markerStart, D.normalize_markerStart]

end LooseHamilton.MixedCycleWitness
