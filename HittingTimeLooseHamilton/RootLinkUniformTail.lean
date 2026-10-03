module

public import HittingTimeLooseHamilton.KahnOrdering
public import HittingTimeLooseHamilton.HypergeometricInclusionBounds
public import HittingTimeLooseHamilton.FiniteMomentBounds

public section

/-! Density-based occupancy tails for a uniform fixed-size root link. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {α : Type*} [DecidableEq α]

lemma uniform_subset_contains_probability (U T : Finset α) (hT : T ⊆ U)
    (q : ℕ) (hTq : T.card ≤ q) [Nonempty ↥(U.powersetCard q)] :
    (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard q)).event
      (fun B => T ⊆ B.val) =
      ((U.card-T.card).choose (q-T.card):ℝ)/(U.card.choose q:ℝ) := by
  classical
  rw [FiniteEntropy.Law.uniform_event,Fintype.card_coe,card_powersetCard]
  have he : (univ.filter (fun B : ↥(U.powersetCard q) => T ⊆ B.val)).card =
      ((U.powersetCard q).filter (fun B => T ⊆ B)).card := by
    apply card_bij (fun B _ => B.val)
    · intro B hB
      exact mem_filter.mpr ⟨B.property,(mem_filter.mp hB).2⟩
    · intro A hA B hB he
      exact Subtype.ext he
    · intro B hB
      exact ⟨⟨B,(mem_filter.mp hB).1⟩,
        mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hB).2⟩,rfl⟩
  rw [he,Kahn.Ordering.card_subsets_containing U T hT q hTq]

/-- The union bound over marked subfamilies, retaining the exact containment
probability, gives the binomial occupancy bound in terms of population density. -/
theorem uniform_subset_occupancy_tail (U Γ : Finset α) (q a : ℕ)
    (hΓ : Γ ⊆ U) (hq : q ≤ U.card) (hU : 0 < U.card)
    [Nonempty ↥(U.powersetCard q)] :
    (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard q)).event
      (fun B => a ≤ (B.val ∩ Γ).card) ≤
      (q.choose a:ℝ)*((Γ.card:ℝ)/U.card)^a := by
  classical
  let p : FiniteEntropy.Law ↥(U.powersetCard q) := FiniteEntropy.uniform
  by_cases ha : a ≤ q
  · let E : ↥(Γ.powersetCard a) → ↥(U.powersetCard q) → Prop :=
      fun T B => T.val ⊆ B.val
    have hm : p.event (fun B => a ≤ (B.val ∩ Γ).card) ≤
        p.event (fun B => ∃ T, E T B) := by
      apply p.event_mono
      intro B hB
      obtain ⟨T,hT,hc⟩ := exists_subset_card_eq hB
      exact ⟨⟨T,mem_powersetCard.mpr ⟨hT.trans inter_subset_right,hc⟩⟩,
        hT.trans inter_subset_left⟩
    have ht (T : ↥(Γ.powersetCard a)) : p.event (E T) =
        (q.choose a:ℝ)/(U.card.choose a:ℝ) := by
      obtain ⟨hTG,hTa⟩ := mem_powersetCard.mp T.property
      dsimp [p,E]
      rw [uniform_subset_contains_probability U T.val (hTG.trans hΓ) q (by omega),hTa]
      exact Hypergeometric.inclusion_ratio_dual hq ha
    calc
      _ ≤ ∑ T, p.event (E T) := hm.trans (p.finite_union_bound E)
      _ = (Γ.card.choose a:ℝ)*((q.choose a:ℝ)/(U.card.choose a:ℝ)) := by
        simp only [ht,sum_const,card_univ,Fintype.card_coe,card_powersetCard,nsmul_eq_mul]
      _ = (q.choose a:ℝ)*((Γ.card.choose a:ℝ)/(U.card.choose a:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Hypergeometric.choose_ratio_le_pow (card_le_card hΓ) hU (ha.trans hq))
        (by positivity)
  · change p.event _ ≤ _
    rw [p.event_eq_zero_of_false (by
      intro B hB
      have hc := card_le_card (inter_subset_left : B.val ∩ Γ ⊆ B.val)
      have hBq := (mem_powersetCard.mp B.property).2
      omega)]
    positivity
end LooseHamilton
