module

public import HittingTimeLooseHamilton.BatchVarianceCounting

public section

/-! Normalized exact second moment and centered variance for batch survival. -/
noncomputable section
namespace LooseHamilton.BatchVariance
open Finset
open scoped BigOperators

@[expose] def variance {m τ : ℕ} (hτ : τ ≤ m) (F : Finset (Finset (Fin m))) : ℝ :=
  ∑ T, (batchLaw hτ).mass T * ((survivors F T : ℝ) - mean hτ F)^2

lemma variance_eq {m τ : ℕ} (hτ : τ ≤ m) (F : Finset (Finset (Fin m))) :
    variance hτ F = secondMoment hτ F - (mean hτ F)^2 := by
  have h (T : Batch m τ) :
      (batchLaw hτ).mass T * ((survivors F T : ℝ) - mean hτ F)^2 =
      (batchLaw hτ).mass T * (survivors F T : ℝ)^2 -
      2 * mean hτ F * ((batchLaw hτ).mass T * (survivors F T : ℝ)) +
      (batchLaw hτ).mass T * (mean hτ F)^2 := by ring
  unfold variance
  simp_rw [h]
  rw [sum_add_distrib,sum_sub_distrib,←mul_sum,←sum_mul,(batchLaw hτ).total]
  change secondMoment hτ F - 2 * mean hτ F * mean hτ F + 1 * mean hτ F ^ 2 = _
  ring

lemma mean_pos {m k τ : ℕ} (hτ : τ ≤ m) (F : Finset (Finset (Fin m)))
    (hF : ∀ A ∈ F, A.card = k) (hFn : F.Nonempty) (htk : τ ≤ m-k) :
    0 < mean hτ F := by
  rw [mean_eq hτ F hF]
  exact div_pos (mul_pos (by exact_mod_cast hFn.card_pos)
    (by exact_mod_cast Nat.choose_pos htk)) (by exact_mod_cast Nat.choose_pos hτ)

lemma normalized_secondMoment {m k τ : ℕ} (hτ : τ ≤ m)
    (F : Finset (Finset (Fin m))) (hF : ∀ A ∈ F, A.card = k)
    (hFn : F.Nonempty) (htk : τ ≤ m-k) :
    secondMoment hτ F / (mean hτ F)^2 =
      (∑ A ∈ F, ∑ B ∈ F,
        ((m-(2*k-(A ∩ B).card)).choose τ : ℝ) * (m.choose τ : ℝ) /
          (((m-k).choose τ : ℝ)^2)) / (F.card : ℝ)^2 := by
  have hM : (m.choose τ : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hτ).ne'
  have hK : ((m-k).choose τ : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos htk).ne'
  have hN : (F.card : ℝ) ≠ 0 := by exact_mod_cast hFn.card_pos.ne'
  rw [secondMoment_overlap hτ F hF,mean_eq hτ F hF]
  simp_rw [←sum_div,←sum_mul]
  field_simp <;> ring

lemma normalized_variance {m k τ : ℕ} (hτ : τ ≤ m)
    (F : Finset (Finset (Fin m))) (hF : ∀ A ∈ F, A.card = k)
    (hFn : F.Nonempty) (htk : τ ≤ m-k) :
    variance hτ F / (mean hτ F)^2 =
      (∑ A ∈ F, ∑ B ∈ F,
        ((m-(2*k-(A ∩ B).card)).choose τ : ℝ) * (m.choose τ : ℝ) /
          (((m-k).choose τ : ℝ)^2)) / (F.card : ℝ)^2 - 1 := by
  rw [variance_eq,sub_div,div_self (pow_ne_zero _ (mean_pos hτ F hF hFn htk).ne'),
    normalized_secondMoment hτ F hF hFn htk]
end LooseHamilton.BatchVariance
