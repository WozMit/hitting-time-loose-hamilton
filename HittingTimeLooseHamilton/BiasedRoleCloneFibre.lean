module

public import HittingTimeLooseHamilton.BiasedRoleCloneCoordinates
public import HittingTimeLooseHamilton.BiasedCloneConditionalKahn

public section

/-! Eligible directed roles form an injective subfamily of each conditional
clone host, so their local L1 error is at most the full clone-host error. -/
noncomputable section
open Finset FiniteEntropy
open scoped BigOperators
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r n : ℕ} {markers G : SimpleHypergraph V}

lemma roleCloneFibre_event_zero (root : ↥markers) (a : ↥root.val)
    (C₀ : BiasedCycleState r markers G) (p : Law (BiasedCloneFibre root a C₀))
    (B : Finset (V × Fin 3)) (hB : ¬B ⊆ biasedCloneUniverse root a C₀) :
    p.event (fun C => B ∈ biasedCloneLift root a C.val) = 0 :=
  p.event_eq_zero_of_false (fun C h => hB (biasedCloneFibre_subset root a C₀ C B h))

theorem roleCloneFibre_l1_le (hr : 3≤r) (hG : ∀ B∈G,B.card=r)
    (root : ↥markers) (a : ↥root.val) (C₀ : BiasedCycleState r markers G)
    (e : ↥(biasedCloneUniverse root a C₀) ≃ Fin n)
    (p : Law (BiasedCloneFibre root a C₀)) (lam : ℝ) :
    (∑ i : EligibleRoleCoordinate markers G,
      |p.event (fun C => roleCloneEdge i ∈ biasedCloneLift root a C.val) -
        (if roleCloneEdge i ⊆ biasedCloneUniverse root a C₀ then 1/lam else 0)|) ≤
    ∑ f ∈ (biasedCloneKahnHost hG root a C₀ e).edges,
      |(p.map (biasedCloneKahnMatching hr hG root a C₀ e)).event (fun M => f∈M.val.val)-1/lam| := by
  classical
  let U := biasedCloneUniverse root a C₀
  let g := fun B => |p.event (fun C => B∈biasedCloneLift root a C.val)-1/lam|
  have hlocal := roleCloneEdge_sum_le (markers:=markers) (G:=G) U g (fun _ _ => abs_nonneg _)
  have hleft : (∑ i : EligibleRoleCoordinate markers G,
      |p.event (fun C => roleCloneEdge i∈biasedCloneLift root a C.val) -
        (if roleCloneEdge i ⊆ U then 1/lam else 0)|) =
      ∑ i : EligibleRoleCoordinate markers G, if roleCloneEdge i ⊆ U then g (roleCloneEdge i) else 0 := by
    apply sum_congr rfl
    intro i _
    by_cases hi : roleCloneEdge i ⊆ U
    · simp only [hi, if_true, g]
    · rw [if_neg hi, roleCloneFibre_event_zero root a C₀ p _ hi]
      simp [hi]
  rw [hleft]
  apply hlocal.trans_eq
  change (∑ B∈cloneHost G U,g B) =
    ∑ f ∈ (cloneHost G U).image (CloneRelabel.edge U e), _
  rw [sum_image]
  · apply sum_congr rfl
    intro B hB
    rw [biasedCloneKahn_edge_event hr hG root a C₀ e p B
      (cloneHost_subset_slots G U B hB)]
  · intro B hB D hD h
    exact CloneRelabel.edge_injective_on U e (cloneHost_subset_slots G U B hB)
      (cloneHost_subset_slots G U D hD) h

end LooseHamilton
