module

public import HittingTimeLooseHamilton.BiasedCloneUniverse
public import HittingTimeLooseHamilton.KahnConditioning

public section

/-! Exact entropy chain rule for the injective connected-cycle clone lift. -/
noncomputable section
open Finset FiniteEntropy
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual unoriented connected edge sets, with no presentation multiplicities. -/
@[expose] def ConnectedCloneCycle (r : ℕ) (markers : Finset (Finset V)) :=
  {E : Finset (Finset V) // IsMixedCycle r markers E}

@[expose] instance (r : ℕ) (markers : Finset (Finset V)) : Fintype (ConnectedCloneCycle r markers) := by
  classical
  unfold ConnectedCloneCycle
  infer_instance

namespace ConnectedCloneCycle
variable {r : ℕ} {markers : Finset (Finset V)}

@[expose] def directedWitness (C : ConnectedCloneCycle r markers)
    (root : ↥markers) (a : ↥root.val) : MixedCycleWitness r markers C.val :=
  C.property.some.normalize root a

@[expose] def lift (root : ↥markers) (a : ↥root.val) (C : ConnectedCloneCycle r markers) :
    Finset (Finset (V × Fin 3)) := (C.directedWitness root a).cloneMatching

theorem lift_injective (root : ↥markers) (a : ↥root.val) :
    Function.Injective (lift root a : ConnectedCloneCycle r markers → _) := by
  intro C D h
  apply Subtype.ext
  exact MixedCycleWitness.cloneMatching_recovers _ _ h

/-- Ordinary junctions and marker directions. The root coordinate is constant,
so retaining it introduces no extra role information. -/
@[expose] def role (root : ↥markers) (a : ↥root.val) (C : ConnectedCloneCycle r markers) :
    Finset V × (↥markers → V) :=
  let D := C.directedWitness root a
  (univ.image D.junction \ markers.biUnion id, fun e => (D.markerStart e).val)

/-- Conditioning on the role fixes the complete active clone universe. -/
theorem cloneVertices_eq_of_role (root : ↥markers) (a : ↥root.val)
    {C D : ConnectedCloneCycle r markers} (h : role root a C = role root a D) :
    (C.directedWitness root a).cloneVertices = (D.directedWitness root a).cloneVertices := by
  apply MixedCycleWitness.cloneVertices_eq_of_junction_marker_starts
  · have hj := congrArg Prod.fst h
    change _ \ markers.biUnion id = _ \ markers.biUnion id at hj
    have hc := (C.directedWitness root a).marked_vertices_subset_junctions
    have hd := (D.directedWitness root a).marked_vertices_subset_junctions
    ext v
    by_cases hv : v ∈ markers.biUnion id
    · exact ⟨fun _ => hd hv, fun _ => hc hv⟩
    · have he := congrArg (fun s : Finset V => v ∈ s) hj
      simpa [mem_sdiff, hv] using iff_of_eq he
  · intro e
    apply Subtype.ext
    exact congrFun (congrArg Prod.snd h) e

/-- Every sampled object lifts to a partition with exactly the original edges
on projection; disconnected perfect matchings never enter this law. -/
theorem lift_partition (C : ConnectedCloneCycle r markers) (hr : 3 ≤ r)
    (root : ↥markers) (a : ↥root.val) :
    (∀ B ∈ lift root a C, B.card = r) ∧
      (∀ v ∈ (C.directedWitness root a).cloneVertices,
        ∃! B, B ∈ lift root a C ∧ v ∈ B) :=
  (C.directedWitness root a).cloneMatching_is_partition hr

/-- The entropy identity holds for any distribution on actual connected cycles,
without introducing any additional matching mass. -/
theorem entropy_chain (root : ↥markers) (a : ↥root.val)
    (p : Law (ConnectedCloneCycle r markers)) :
    entropy p.mass = entropy (p.map (role root a)).mass +
      p.conditionalMapEntropy (lift root a) (role root a) := by
  have hi : Function.Injective (fun C : ConnectedCloneCycle r markers =>
      (lift root a C, role root a C)) := by
    intro C D h
    exact lift_injective root a (congrArg Prod.fst h)
  rw [← p.entropy_map_of_injective _ hi]
  exact p.entropy_map_pair _ _

end ConnectedCloneCycle
end LooseHamilton
