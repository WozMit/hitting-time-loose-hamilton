module

public import HittingTimeLooseHamilton.BiasedRoleModels
public import HittingTimeLooseHamilton.BiasedCloneEntropy
public import HittingTimeLooseHamilton.BiasedCloneHost

public section

/-! Directed role probabilities are genuine marginals of the connected clone lift. -/
noncomputable section
namespace LooseHamilton
open Finset FiniteEntropy
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma MixedCycleWitness.cloneEdge_eq_directedCloneEdge {r : ℕ}
    {markers edges : SimpleHypergraph V} (C : MixedCycleWitness r markers edges)
    (hr : 3 ≤ r) (e : ↥edges) :
    C.cloneEdge e = directedCloneEdge e.val
      (C.junction (C.slot.symm (.inr e)))
      (C.junction (finRotate C.length (C.slot.symm (.inr e)))) := by
  unfold MixedCycleWitness.cloneEdge directedCloneEdge
  congr 1
  congr 1
  rw [C.private_eq_sdiff_endpointPair hr, C.edgeEndpointPair_eq hr]

lemma rootedOrdinaryRole_iff_clone {r : ℕ} {markers edges : SimpleHypergraph V}
    (hr : 3 ≤ r) (C : MixedCycleWitness r markers edges)
    (root : ↥markers) (a : ↥root.val) (hC : C.markerStart root=a)
    (e : Finset V) (u v : V) (hu : u∈e) (hv : v∈e) :
    rootedOrdinaryRole r markers edges root a e u v ↔
      directedCloneEdge e u v ∈ C.cloneMatching := by
  constructor
  · rintro ⟨D,hD,he,hdU,hdV⟩
    have hu' := C.slot_start_eq_of_root D hr root (hC.trans hD.symm) (.inr ⟨e,he⟩)
    have hv' := C.slot_end_eq_of_root D hr root (hC.trans hD.symm) (.inr ⟨e,he⟩)
    have hh : C.cloneEdge ⟨e,he⟩ = directedCloneEdge e u v := by
      rw [C.cloneEdge_eq_directedCloneEdge hr, hu'.trans hdU, hv'.trans hdV]
    exact mem_image.mpr ⟨⟨e,he⟩, mem_univ _, hh⟩
  · intro h
    obtain ⟨f,_,hf⟩ := mem_image.mp h
    have hp := congrArg (fun B : Finset (V × Fin 3) => B.image Prod.fst) hf
    rw [C.cloneEdge_project, directedCloneEdge_project e hu hv] at hp
    have he : e∈edges := hp ▸ f.property
    have hf' : f=⟨e,he⟩ := Subtype.ext hp
    subst f
    refine ⟨C,hC,he,?_,?_⟩
    · have hm : (u,(0:Fin 3)) ∈ C.cloneEdge ⟨e,he⟩ := by
        rw [hf]
        simp [directedCloneEdge]
      have hm' : u=C.junction (C.slot.symm (.inr ⟨e,he⟩)) := by
        simpa [MixedCycleWitness.mem_cloneEdge] using hm
      exact hm'.symm
    · have hm : (v,(1:Fin 3)) ∈ C.cloneEdge ⟨e,he⟩ := by
        rw [hf]
        simp [directedCloneEdge]
      have hm' : v=C.junction (finRotate C.length (C.slot.symm (.inr ⟨e,he⟩))) := by
        simpa [MixedCycleWitness.mem_cloneEdge] using hm
      exact hm'.symm

/-- Forgetting only the host restriction preserves the sampled connected cycles. -/
@[expose] def biasedConnectedCycle {r : ℕ} {markers host : SimpleHypergraph V}
    (C : BiasedCycleState r markers host) : ConnectedCloneCycle r markers :=
  ⟨C.val, ((mem_cycleFamily _ _ _ _ _).mp C.property).1⟩

lemma biasedConnectedCycle_injective {r : ℕ} {markers host : SimpleHypergraph V} :
    Function.Injective (biasedConnectedCycle : BiasedCycleState r markers host → _) := by
  intro C D h
  exact Subtype.ext (congrArg (fun E : ConnectedCloneCycle r markers => E.val) h)

/-- No orientation choices or extra disconnected matching mass affect p_rho. -/
theorem directedRoleProbability_eq_clone_event {r : ℕ} {markers host : SimpleHypergraph V}
    (hr : 3 ≤ r) (root : ↥markers) (a : ↥root.val)
    (p : Law (BiasedCycleState r markers host))
    (e : Finset V) (u v : V) (hu : u∈e) (hv : v∈e) :
    directedRoleProbability r markers host root a p e u v =
      (p.map biasedConnectedCycle).event (fun C =>
        directedCloneEdge e u v ∈ ConnectedCloneCycle.lift root a C) := by
  rw [Law.event_map]
  unfold directedRoleProbability
  congr 1
  funext E
  apply propext
  exact rootedOrdinaryRole_iff_clone hr _ root a
    ((biasedConnectedCycle E).property.some.normalize_markerStart root a) e u v hu hv
end LooseHamilton
