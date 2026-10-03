module

public import HittingTimeLooseHamilton.BiasedCloneConditionalFibre
public import HittingTimeLooseHamilton.BiasedCloneHostCompatibility

public section

/-! The actual connected-cycle law on one role fibre is a Kahn matching law
on the full compatible clone host, with exactly preserved entropy. -/
noncomputable section
open Finset FiniteEntropy
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r n : ℕ} {markers G : SimpleHypergraph V}
variable (hr : 3 ≤ r) (hG : ∀ B ∈ G, B.card = r)
variable (root : ↥markers) (a : ↥root.val) (C₀ : BiasedCycleState r markers G)
variable (e : ↥(biasedCloneUniverse root a C₀) ≃ Fin n)

theorem biasedCloneFibre_host (C : BiasedCloneFibre root a C₀) :
    biasedCloneLift root a C.val ⊆ cloneHost G (biasedCloneUniverse root a C₀) := by
  apply MixedCycleWitness.cloneMatching_subset_host
  · exact ((mem_cycleFamily _ _ _ _ _).mp C.val.property).2.1
  · rw [biasedCloneFibre_universe root a C₀ C]

/-- Full compatible clone host, relabelled to the fixed finite vertex set. -/
@[expose] def biasedCloneKahnHost : Kahn.Hypergraph n r :=
  CloneRelabel.host (biasedCloneUniverse root a C₀) e
    (cloneHost G (biasedCloneUniverse root a C₀))
    (cloneHost_subset_slots _ _) (cloneHost_uniform _ _ r hG)

/-- An actual cycle in this role fibre, as a perfect matching of the full host. -/
@[expose] def biasedCloneKahnMatching (C : BiasedCloneFibre root a C₀) :
    Kahn.MatchingIn (biasedCloneKahnHost hG root a C₀ e) :=
  CloneRelabel.sampleMatching (biasedCloneUniverse root a C₀) e
    (cloneHost G (biasedCloneUniverse root a C₀))
    (cloneHost_subset_slots _ _) (cloneHost_uniform _ _ r hG)
    (fun C : BiasedCloneFibre root a C₀ => biasedCloneLift root a C.val)
    (biasedCloneFibre_host root a C₀)
    (fun C => (biasedCloneFibre_partition hr root a C₀ C).2) C

theorem biasedCloneKahnMatching_injective :
    Function.Injective (biasedCloneKahnMatching hr hG root a C₀ e) := by
  apply CloneRelabel.sampleMatching_injective
  intro C D h
  apply Subtype.ext
  exact biasedCloneLift_injective root a h

/-- No entropy is lost when converting the genuine conditional connected-cycle
law to the matching law needed by Kahn's theorem. -/
theorem biasedCloneKahn_entropy (p : Law (BiasedCloneFibre root a C₀)) :
    entropy (p.map (biasedCloneKahnMatching hr hG root a C₀ e)).mass = entropy p.mass :=
  p.entropy_map_of_injective _ (biasedCloneKahnMatching_injective hr hG root a C₀ e)

/-- All clone-edge incidence probabilities are preserved exactly. -/
theorem biasedCloneKahn_edge_event (p : Law (BiasedCloneFibre root a C₀))
    (B : Finset (V × Fin 3)) (hB : B ⊆ biasedCloneUniverse root a C₀) :
    (p.map (biasedCloneKahnMatching hr hG root a C₀ e)).event
      (fun M => CloneRelabel.edge (biasedCloneUniverse root a C₀) e B ∈ M.val.val) =
        p.event (fun C => B ∈ biasedCloneLift root a C.val) := by
  apply CloneRelabel.event_sampleMatching_edge
  exact hB

end LooseHamilton
