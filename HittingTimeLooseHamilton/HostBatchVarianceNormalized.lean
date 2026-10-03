module

public import HittingTimeLooseHamilton.HostBatchVarianceMoments

public section

/-! Normalized exact second moment and centered variance for batch survival. -/
noncomputable section
namespace LooseHamilton.FrameSurvival
open Finset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]

@[expose] def variance {H : Finset α} {τ : ℕ} (hτ : τ ≤ H.card) (F : Finset (Finset α)) : ℝ :=
  ∑ T, (hostBatchLaw hτ).mass T * ((survivorCount F T.val : ℝ) - mean hτ F)^2

lemma variance_eq {H : Finset α} {τ : ℕ} (hτ : τ ≤ H.card) (F : Finset (Finset α)) :
    variance hτ F = secondMoment hτ F - (mean hτ F)^2 := by
  have h (T : HostBatch H τ) :
      (hostBatchLaw hτ).mass T * ((survivorCount F T.val : ℝ) - mean hτ F)^2 =
      (hostBatchLaw hτ).mass T * (survivorCount F T.val : ℝ)^2 -
      2 * mean hτ F * ((hostBatchLaw hτ).mass T * (survivorCount F T.val : ℝ)) +
      (hostBatchLaw hτ).mass T * (mean hτ F)^2 := by ring
  unfold variance
  simp_rw [h]
  rw [sum_add_distrib,sum_sub_distrib,←mul_sum,←sum_mul,(hostBatchLaw hτ).total]
  change secondMoment hτ F - 2 * mean hτ F * mean hτ F + 1 * mean hτ F ^ 2 = _
  ring

lemma mean_pos {H : Finset α} {k τ : ℕ} (hτ : τ ≤ H.card) (F : Finset (Finset α))
    (hF : ∀ A ∈ F, A ⊆ H ∧ A.card = k) (hFn : F.Nonempty) (htk : τ ≤ H.card-k) :
    0 < mean hτ F := by
  rw [mean_eq hτ F hF]
  exact div_pos (mul_pos (by exact_mod_cast hFn.card_pos)
    (by exact_mod_cast Nat.choose_pos htk)) (by exact_mod_cast Nat.choose_pos hτ)

lemma normalized_secondMoment {H : Finset α} {k τ : ℕ} (hτ : τ ≤ H.card)
    (F : Finset (Finset α)) (hF : ∀ A ∈ F, A ⊆ H ∧ A.card = k)
    (hFn : F.Nonempty) (htk : τ ≤ H.card-k) :
    secondMoment hτ F / (mean hτ F)^2 =
      (∑ A ∈ F, ∑ B ∈ F,
        ((H.card-(2*k-(A ∩ B).card)).choose τ : ℝ) * (H.card.choose τ : ℝ) /
          (((H.card-k).choose τ : ℝ)^2)) / (F.card : ℝ)^2 := by
  have hM : (H.card.choose τ : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hτ).ne'
  have hK : ((H.card-k).choose τ : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos htk).ne'
  have hN : (F.card : ℝ) ≠ 0 := by exact_mod_cast hFn.card_pos.ne'
  rw [secondMoment_overlap hτ F hF,mean_eq hτ F hF]
  simp_rw [←sum_div,←sum_mul]
  field_simp <;> ring

lemma normalized_variance {H : Finset α} {k τ : ℕ} (hτ : τ ≤ H.card)
    (F : Finset (Finset α)) (hF : ∀ A ∈ F, A ⊆ H ∧ A.card = k)
    (hFn : F.Nonempty) (htk : τ ≤ H.card-k) :
    variance hτ F / (mean hτ F)^2 =
      (∑ A ∈ F, ∑ B ∈ F,
        ((H.card-(2*k-(A ∩ B).card)).choose τ : ℝ) * (H.card.choose τ : ℝ) /
          (((H.card-k).choose τ : ℝ)^2)) / (F.card : ℝ)^2 - 1 := by
  rw [variance_eq,sub_div,div_self (pow_ne_zero _ (mean_pos hτ F hF hFn htk).ne'),
    normalized_secondMoment hτ F hF hFn htk]
end LooseHamilton.FrameSurvival
