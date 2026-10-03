module

public import HittingTimeLooseHamilton.AssociationLayerModels

public section

/-! Cardinality bounds for the actual forward and reverse incidence spaces. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma associationReverseIncidence_card (r : ℕ) (d : V → ℕ) (y : V) (B : Finset V) (t : ℕ) :
    Fintype.card (associationReverseIncidence r d y B t) =
      associationLayerCount r d y B t * associationNumerator r d y B := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe,fixed_associationReverseLabels_card,sum_const,card_univ,
    nsmul_eq_mul,associationLayerCount,Nat.cast_id]

lemma associationForwardIncidence_card_lower {r : ℕ} (hr : 3 ≤ r)
    (d : V → ℕ) (y : V) (B : Finset V) (t : ℕ) :
    degreeSum d*t*associationLayerCount r d y B t ≤
      Fintype.card (associationForwardIncidence r d y B t) +
        associationBadBudget r d B*t*associationLayerCount r d y B t := by
  have hlocal (F : associationLayer r d y B t) :
      t*degreeSum d ≤ (∑ s : ↥(associationSources F.val.val y B),
        (associationGoodTargets F.val.val B s.val.1 s.val.2).card) + t*associationBadBudget r d B := by
    have hs (s : ↥(associationSources F.val.val y B)) :
        degreeSum d ≤ (associationGoodTargets F.val.val B s.val.1 s.val.2).card +
          associationBadBudget r d B := by
      obtain ⟨he,hz,hy,hB⟩ := (mem_associationSources _ _ _ _).mp s.property
      have h := association_good_targets_fixed hr F.val B he hz
      rw [fixed_graphIncidences_card] at h
      exact h
    have h := sum_le_sum (fun s (_ : s ∈ univ) => hs s)
    simpa only [sum_const,card_univ,Fintype.card_coe,associationSources_card,F.property,
      nsmul_eq_mul,sum_add_distrib, Nat.cast_id] using h
  have h := sum_le_sum (fun F (_ : F ∈ univ) => hlocal F)
  have hc : Fintype.card (associationForwardIncidence r d y B t) =
      ∑ F : associationLayer r d y B t, ∑ s : ↥(associationSources F.val.val y B),
        (associationGoodTargets F.val.val B s.val.1 s.val.2).card := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_sigma,Fintype.card_coe]
  simp only [sum_const,card_univ,nsmul_eq_mul,sum_add_distrib,← hc] at h
  change associationLayerCount r d y B t*(t*degreeSum d) ≤
    Fintype.card (associationForwardIncidence r d y B t) +
      associationLayerCount r d y B t*(t*associationBadBudget r d B) at h
  convert h using 1 <;> ring
end LooseHamilton
