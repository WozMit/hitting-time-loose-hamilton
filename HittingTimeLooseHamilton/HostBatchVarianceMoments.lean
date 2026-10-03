module

public import HittingTimeLooseHamilton.FrameSurvivalCounting

public section

noncomputable section
namespace LooseHamilton.FrameSurvival
open Finset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]

@[expose] def mean {H : Finset α} {τ : ℕ} (hτ : τ ≤ H.card) (F : Finset (Finset α)) : ℝ :=
  ∑ T, (hostBatchLaw hτ).mass T * (survivorCount F T.val : ℝ)

@[expose] def secondMoment {H : Finset α} {τ : ℕ} (hτ : τ ≤ H.card) (F : Finset (Finset α)) : ℝ :=
  ∑ T, (hostBatchLaw hτ).mass T * (survivorCount F T.val : ℝ)^2

lemma survivors_eq_sum {H : Finset α} {τ : ℕ}
    (F : Finset (Finset α)) (T : HostBatch H τ) :
    (survivorCount F T.val : ℝ) = ∑ A ∈ F, if Disjoint T.val A then (1:ℝ) else 0 := by
  classical
  simp [survivorCount, ← sum_filter]

lemma mean_eq {H : Finset α} {k τ : ℕ} (hτ : τ ≤ H.card)
    (F : Finset (Finset α)) (hF : ∀ A ∈ F, A ⊆ H ∧ A.card = k) :
    mean hτ F = (F.card : ℝ) * ((H.card-k).choose τ : ℝ) / (H.card.choose τ : ℝ) :=
  host_survival_mean hτ F hF

lemma secondMoment_eq {H : Finset α} {τ : ℕ} (hτ : τ ≤ H.card) (F : Finset (Finset α)) (hsub : ∀ A ∈ F, A ⊆ H) :
    secondMoment hτ F = ∑ A ∈ F, ∑ B ∈ F,
      ((H.card-(A ∪ B).card).choose τ : ℝ) / (H.card.choose τ : ℝ) := by
  classical
  have hs (T : HostBatch H τ) : (survivorCount F T.val : ℝ)^2 =
      ∑ A ∈ F, ∑ B ∈ F, if Disjoint T.val (A ∪ B) then (1:ℝ) else 0 := by
    rw [survivors_eq_sum,pow_two,sum_mul]
    apply sum_congr rfl
    intro A hA
    rw [mul_sum]
    apply sum_congr rfl
    intro B hB
    simp only [disjoint_union_right]
    split_ifs <;> simp_all
  unfold secondMoment
  simp_rw [hs,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro A hA
  rw [sum_comm]
  apply sum_congr rfl
  intro B hB
  rw [← host_avoidance_probability hτ (A ∪ B) (union_subset (hsub A hA) (hsub B hB))]
  unfold FiniteEntropy.Law.event
  apply sum_congr rfl
  intro T _
  split_ifs <;> simp

lemma union_card {k : ℕ} {A B : Finset α} (hA : A.card=k) (hB : B.card=k) :
    (A ∪ B).card = 2*k-(A ∩ B).card := by
  have h := card_union_add_card_inter A B
  omega

lemma secondMoment_overlap {H : Finset α} {k τ : ℕ} (hτ : τ ≤ H.card) (F : Finset (Finset α))
    (hF : ∀ A ∈ F, A ⊆ H ∧ A.card = k) :
    secondMoment hτ F = ∑ A ∈ F, ∑ B ∈ F,
      ((H.card-(2*k-(A ∩ B).card)).choose τ : ℝ) / (H.card.choose τ : ℝ) := by
  rw [secondMoment_eq hτ F (fun A hA => (hF A hA).1)]
  apply sum_congr rfl
  intro A hA
  apply sum_congr rfl
  intro B hB
  rw [union_card (hF A hA).2 (hF B hB).2]
end LooseHamilton.FrameSurvival
