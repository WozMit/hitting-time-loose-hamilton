module

public import HittingTimeLooseHamilton.HostBatchVarianceNormalized

public section

/-! Survival moments for labelled objects. Equal supports remain distinct objects. -/
noncomputable section
namespace LooseHamilton.IndexedSurvival
open Finset FrameSurvival
open scoped BigOperators
variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

/-- Objects, rather than their distinct supports, are counted. -/
@[expose] def count (F : Finset ι) (support : ι → Finset α) (T : Finset α) : ℕ :=
  (F.filter fun i => Disjoint T (support i)).card

@[expose] def mean {H : Finset α} {τ : ℕ} (hτ : τ ≤ H.card)
    (F : Finset ι) (support : ι → Finset α) : ℝ :=
  ∑ T, (hostBatchLaw hτ).mass T * (count F support T.val : ℝ)

@[expose] def secondMoment {H : Finset α} {τ : ℕ} (hτ : τ ≤ H.card)
    (F : Finset ι) (support : ι → Finset α) : ℝ :=
  ∑ T, (hostBatchLaw hτ).mass T * (count F support T.val : ℝ)^2

@[expose] def variance {H : Finset α} {τ : ℕ} (hτ : τ ≤ H.card)
    (F : Finset ι) (support : ι → Finset α) : ℝ :=
  ∑ T, (hostBatchLaw hτ).mass T *
    ((count F support T.val : ℝ) - mean hτ F support)^2

lemma count_eq_sum (F : Finset ι) (support : ι → Finset α) (T : Finset α) :
    (count F support T : ℝ) = ∑ i ∈ F, if Disjoint T (support i) then (1:ℝ) else 0 := by
  classical
  simp [count, ← sum_filter]

lemma mean_eq {H : Finset α} {τ : ℕ} (hτ : τ ≤ H.card)
    (F : Finset ι) (support : ι → Finset α) (hsub : ∀ i ∈ F, support i ⊆ H) :
    mean hτ F support = ∑ i ∈ F,
      ((H.card - (support i).card).choose τ : ℝ) / (H.card.choose τ : ℝ) := by
  classical
  unfold mean
  simp_rw [count_eq_sum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [← host_avoidance_probability hτ (support i) (hsub i hi)]
  unfold FiniteEntropy.Law.event
  apply sum_congr rfl
  intro T _
  split_ifs <;> simp

lemma secondMoment_eq {H : Finset α} {τ : ℕ} (hτ : τ ≤ H.card)
    (F : Finset ι) (support : ι → Finset α) (hsub : ∀ i ∈ F, support i ⊆ H) :
    secondMoment hτ F support = ∑ i ∈ F, ∑ j ∈ F,
      ((H.card - (support i ∪ support j).card).choose τ : ℝ) /
        (H.card.choose τ : ℝ) := by
  classical
  have hs (T : HostBatch H τ) : (count F support T.val : ℝ)^2 =
      ∑ i ∈ F, ∑ j ∈ F, if Disjoint T.val (support i ∪ support j) then (1:ℝ) else 0 := by
    rw [count_eq_sum, pow_two, sum_mul]
    apply sum_congr rfl
    intro i hi
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    simp only [disjoint_union_right]
    split_ifs <;> simp_all
  unfold secondMoment
  simp_rw [hs, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [← host_avoidance_probability hτ (support i ∪ support j)
    (union_subset (hsub i hi) (hsub j hj))]
  unfold FiniteEntropy.Law.event
  apply sum_congr rfl
  intro T _
  split_ifs <;> simp

lemma variance_eq {H : Finset α} {τ : ℕ} (hτ : τ ≤ H.card)
    (F : Finset ι) (support : ι → Finset α) :
    variance hτ F support = secondMoment hτ F support - (mean hτ F support)^2 := by
  have h (T : HostBatch H τ) :
      (hostBatchLaw hτ).mass T * ((count F support T.val : ℝ) - mean hτ F support)^2 =
      (hostBatchLaw hτ).mass T * (count F support T.val : ℝ)^2 -
      2 * mean hτ F support * ((hostBatchLaw hτ).mass T * (count F support T.val : ℝ)) +
      (hostBatchLaw hτ).mass T * (mean hτ F support)^2 := by ring
  unfold variance
  simp_rw [h]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, (hostBatchLaw hτ).total]
  change secondMoment hτ F support - 2 * mean hτ F support * mean hτ F support +
    1 * mean hτ F support ^ 2 = _
  ring

/-- The empty deletion batch preserves every label, including repeated supports. -/
lemma count_empty (F : Finset ι) (support : ι → Finset α) :
    count F support ∅ = F.card := by simp [count]

/-- Pointwise bounds on individual survival probabilities give bounds on the
mean without requiring distinct or equal-sized supports. -/
lemma mean_bounds {H : Finset α} {τ : ℕ} (hτ : τ ≤ H.card)
    (F : Finset ι) (support : ι → Finset α) (hsub : ∀ i ∈ F, support i ⊆ H)
    (lo hi : ℝ)
    (hlo : ∀ i ∈ F, lo ≤
      ((H.card - (support i).card).choose τ : ℝ) / (H.card.choose τ : ℝ))
    (hhi : ∀ i ∈ F,
      ((H.card - (support i).card).choose τ : ℝ) / (H.card.choose τ : ℝ) ≤ hi) :
    (F.card : ℝ) * lo ≤ mean hτ F support ∧
      mean hτ F support ≤ (F.card : ℝ) * hi := by
  rw [mean_eq hτ F support hsub]
  constructor
  · simpa using sum_le_sum hlo
  · simpa using sum_le_sum hhi

lemma mean_pos {H : Finset α} {τ : ℕ} (hτ : τ ≤ H.card)
    (F : Finset ι) (support : ι → Finset α) (hsub : ∀ i ∈ F, support i ⊆ H)
    (hne : F.Nonempty) (hsize : ∀ i ∈ F, τ ≤ H.card - (support i).card) :
    0 < mean hτ F support := by
  rw [mean_eq hτ F support hsub]
  apply sum_pos
  · intro i hi
    exact div_pos (by exact_mod_cast Nat.choose_pos (hsize i hi))
      (by exact_mod_cast Nat.choose_pos hτ)
  · exact hne

end LooseHamilton.IndexedSurvival
