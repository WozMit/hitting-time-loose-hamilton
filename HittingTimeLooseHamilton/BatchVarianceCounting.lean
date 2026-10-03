module

public import HittingTimeLooseHamilton.UniformSubtypeProbability
public import Mathlib.Data.Finset.Powerset

public section

/-! Exact moments of the number of surviving members under uniform batch deletion. -/
noncomputable section
namespace LooseHamilton.BatchVariance
open Finset
open scoped BigOperators

abbrev Batch (m τ : ℕ) := ↥((univ : Finset (Fin m)).powersetCard τ)

lemma batch_nonempty {m τ : ℕ} (hτ : τ ≤ m) : Nonempty (Batch m τ) := by
  apply Fintype.card_pos_iff.mp
  simpa using Nat.choose_pos hτ

@[expose] def batchLaw {m τ : ℕ} (hτ : τ ≤ m) : FiniteEntropy.Law (Batch m τ) :=
  @FiniteEntropy.uniform _ inferInstance (batch_nonempty hτ)

@[expose] def survivors {m τ : ℕ} (F : Finset (Finset (Fin m))) (T : Batch m τ) : ℕ :=
  (F.filter fun A => Disjoint T.val A).card

@[expose] def mean {m τ : ℕ} (hτ : τ ≤ m) (F : Finset (Finset (Fin m))) : ℝ :=
  ∑ T, (batchLaw hτ).mass T * (survivors F T : ℝ)

@[expose] def secondMoment {m τ : ℕ} (hτ : τ ≤ m) (F : Finset (Finset (Fin m))) : ℝ :=
  ∑ T, (batchLaw hτ).mass T * (survivors F T : ℝ)^2

lemma avoidance_probability {m τ : ℕ} (hτ : τ ≤ m) (A : Finset (Fin m)) :
    (batchLaw hτ).event (fun T => Disjoint T.val A) =
      ((m - A.card).choose τ : ℝ) / (m.choose τ : ℝ) := by
  classical
  letI := batch_nonempty hτ
  change (FiniteEntropy.uniform : FiniteEntropy.Law (Batch m τ)).event _ = _
  rw [FiniteEntropy.Law.uniform_event, ← Fintype.card_subtype]
  have hc : Fintype.card {T : Batch m τ // Disjoint T.val A} =
      (((univ : Finset (Fin m)) \ A).powersetCard τ).card := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    refine ⟨(fun T => ⟨T.val.val, ?_⟩), (fun T => ⟨⟨T.val, ?_⟩, ?_⟩),
      (fun T => rfl), (fun T => rfl)⟩
    · rcases mem_powersetCard.mp T.val.property with ⟨hsub,hcard⟩
      exact mem_powersetCard.mpr ⟨subset_sdiff.mpr ⟨hsub,T.property⟩,hcard⟩
    · rcases mem_powersetCard.mp T.property with ⟨hsub,hcard⟩
      exact mem_powersetCard.mpr ⟨subset_univ _,hcard⟩
    · exact (subset_sdiff.mp (mem_powersetCard.mp T.property).1).2
  rw [hc]
  simp [Batch,card_powersetCard,card_sdiff_of_subset (subset_univ A)]

lemma survivors_eq_sum {m τ : ℕ} (F : Finset (Finset (Fin m))) (T : Batch m τ) :
    (survivors F T : ℝ) = ∑ A ∈ F, if Disjoint T.val A then (1:ℝ) else 0 := by
  classical
  simp [survivors, ← sum_filter]

lemma mean_eq {m k τ : ℕ} (hτ : τ ≤ m) (F : Finset (Finset (Fin m)))
    (hF : ∀ A ∈ F, A.card = k) :
    mean hτ F = (F.card : ℝ) * ((m-k).choose τ : ℝ) / (m.choose τ : ℝ) := by
  classical
  unfold mean
  simp_rw [survivors_eq_sum, mul_sum]
  rw [sum_comm]
  have he (A : Finset (Fin m)) :
      (∑ T, (batchLaw hτ).mass T * (if Disjoint T.val A then (1:ℝ) else 0)) =
        (batchLaw hτ).event (fun T => Disjoint T.val A) := by
    unfold FiniteEntropy.Law.event
    apply sum_congr rfl
    intro T _
    split_ifs <;> simp
  simp_rw [he,avoidance_probability]
  calc
    _ = ∑ _A ∈ F, ((m-k).choose τ : ℝ) / (m.choose τ : ℝ) := by
      apply sum_congr rfl
      intro A hA
      rw [hF A hA]
    _ = _ := by simp [mul_div_assoc]

lemma secondMoment_eq {m τ : ℕ} (hτ : τ ≤ m) (F : Finset (Finset (Fin m))) :
    secondMoment hτ F = ∑ A ∈ F, ∑ B ∈ F,
      ((m-(A ∪ B).card).choose τ : ℝ) / (m.choose τ : ℝ) := by
  classical
  have hs (T : Batch m τ) : (survivors F T : ℝ)^2 =
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
  rw [← avoidance_probability hτ]
  unfold FiniteEntropy.Law.event
  apply sum_congr rfl
  intro T _
  split_ifs <;> simp

lemma union_card {m k : ℕ} {A B : Finset (Fin m)} (hA : A.card=k) (hB : B.card=k) :
    (A ∪ B).card = 2*k-(A ∩ B).card := by
  have h := card_union_add_card_inter A B
  omega

lemma secondMoment_overlap {m k τ : ℕ} (hτ : τ ≤ m) (F : Finset (Finset (Fin m)))
    (hF : ∀ A ∈ F, A.card = k) :
    secondMoment hτ F = ∑ A ∈ F, ∑ B ∈ F,
      ((m-(2*k-(A ∩ B).card)).choose τ : ℝ) / (m.choose τ : ℝ) := by
  rw [secondMoment_eq]
  apply sum_congr rfl
  intro A hA
  apply sum_congr rfl
  intro B hB
  rw [union_card (hF A hA) (hF B hB)]
end LooseHamilton.BatchVariance
