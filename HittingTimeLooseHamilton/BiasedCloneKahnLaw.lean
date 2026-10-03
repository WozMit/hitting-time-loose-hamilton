module

public import HittingTimeLooseHamilton.BiasedCloneKahnRelabel

public section

/-! Transport of arbitrary laws of connected clone lifts into Kahn's matching
space preserves entropy and every edge-incidence probability. -/
noncomputable section
open Finset FiniteEntropy
namespace LooseHamilton.CloneRelabel
variable {A S : Type*} [DecidableEq A] [Fintype S] {n r : ℕ}
variable (U : Finset A) (e : ↥U ≃ Fin n)
variable (G : Finset (Finset A))
variable (hGsub : ∀ B ∈ G, B ⊆ U) (hGunif : ∀ B ∈ G, B.card = r)
variable (F : S → Finset (Finset A)) (hFG : ∀ s, F s ⊆ G)
variable (hpart : ∀ s v, v ∈ U → ∃! B, B ∈ F s ∧ v ∈ B)

@[expose] def sampleMatching (s : S) : Kahn.MatchingIn (host U e G hGsub hGunif) :=
  matchingIn U e G (F s) hGsub hGunif (hFG s) (hpart s)

theorem sampleMatching_injective (hF : Function.Injective F) :
    Function.Injective (sampleMatching U e G hGsub hGunif F hFG hpart) := by
  intro s t h
  apply hF
  apply family_injective_on U e
    (fun B hB => hGsub B (hFG s hB)) (fun B hB => hGsub B (hFG t hB))
  exact congrArg (fun M : Kahn.MatchingIn (host U e G hGsub hGunif) => M.val.val) h

theorem entropy_sampleMatching (p : Law S) (hF : Function.Injective F) :
    entropy (p.map (sampleMatching U e G hGsub hGunif F hFG hpart)).mass =
      entropy p.mass :=
  p.entropy_map_of_injective _ (sampleMatching_injective U e G hGsub hGunif F hFG hpart hF)

theorem sampleMatching_edge_mem (s : S) (B : Finset A) (hB : B ⊆ U) :
    edge U e B ∈ (sampleMatching U e G hGsub hGunif F hFG hpart s).val.val ↔
      B ∈ F s := by
  change edge U e B ∈ family U e (F s) ↔ _
  constructor
  · intro h
    obtain ⟨D, hD, he⟩ := mem_image.mp h
    have heq := edge_injective_on U e (hGsub D (hFG s hD)) hB he
    exact heq ▸ hD
  · exact mem_image_of_mem _

/-- Relabelling changes neither clone-edge marginals nor the law's support. -/
theorem event_sampleMatching_edge (p : Law S) (B : Finset A) (hB : B ⊆ U) :
    (p.map (sampleMatching U e G hGsub hGunif F hFG hpart)).event
      (fun M => edge U e B ∈ M.val.val) = p.event (fun s => B ∈ F s) := by
  rw [Law.event_map]
  congr 1
  funext s
  exact propext (sampleMatching_edge_mem U e G hGsub hGunif F hFG hpart s B hB)

end LooseHamilton.CloneRelabel
