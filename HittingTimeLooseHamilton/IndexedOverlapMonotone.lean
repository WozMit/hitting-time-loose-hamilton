module

public import HittingTimeLooseHamilton.IndexedSurvivalOverlapLaw

public section

noncomputable section
namespace LooseHamilton.IndexedSurvival
open Finset
variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

/-- Restricting the sampled support can only reduce independent overlap;
object labels, multiplicities and diagonal terms remain unchanged. -/
theorem uniformOverlap_mono (F : Finset ι) (s t : ι → Finset α)
    (h : ∀ i∈F, s i ⊆ t i) : uniformOverlap F s ≤ uniformOverlap F t := by
  unfold uniformOverlap
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply sum_le_sum
  intro i hi
  apply sum_le_sum
  intro j hj
  exact_mod_cast card_le_card (inter_subset_inter (h i hi) (h j hj))

theorem uniformOverlap_inter_le (F : Finset (Finset α)) (H : Finset α) :
    uniformOverlap F (fun E => E∩H) ≤ uniformOverlap F id :=
  uniformOverlap_mono F _ _ (fun _ _ => inter_subset_left)
end LooseHamilton.IndexedSurvival
