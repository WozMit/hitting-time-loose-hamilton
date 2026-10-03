module

public import HittingTimeLooseHamilton.HostBatchVarianceNormalized
public import HittingTimeLooseHamilton.BatchVarianceProduct
public import HittingTimeLooseHamilton.BatchVarianceScalar

public section

/-! The batch-variance inequality for the actual uniform deletion experiment. -/
noncomputable section
namespace LooseHamilton.FrameSurvival
open Finset
open scoped BigOperators
open LooseHamilton.BatchVariance
variable {α : Type*} [DecidableEq α]

/-- Expected intersection size for two independent uniform members of the family. -/
@[expose] def averageOverlap (F : Finset (Finset α)) : ℝ :=
  (∑ A ∈ F, ∑ B ∈ F, ((A ∩ B).card : ℝ))/(F.card:ℝ)^2

/-- Lemma 7.1, variance branch. The variance and mean refer to the actual number
of surviving family members under a uniformly chosen batch. -/
theorem host_batch_variance_bound {H : Finset α} {k τ : ℕ} (F : Finset (Finset α))
    (hFn : F.Nonempty) (hF : ∀ A ∈ F, A ⊆ H ∧ A.card=k)
    (hk4 : 4*k≤H.card) (ht4 : 4*τ≤H.card) :
    variance (show τ≤H.card by omega) F / (mean (show τ≤H.card by omega) F)^2 ≤
      (averageOverlap F/(k:ℝ))*Real.exp (4*(τ:ℝ)*k/H.card) := by
  have hτ : τ≤H.card := by omega
  have htk : τ≤H.card-k := by omega
  have hn : (0:ℝ)<F.card := by exact_mod_cast hFn.card_pos
  rw [normalized_variance hτ F hF hFn htk]
  by_cases hm : H.card=0
  · have hk : k=0 := by omega
    have ht : τ=0 := by omega
    subst k
    subst τ
    simp [hm, div_self (mul_ne_zero hn.ne' hn.ne'),sq]
  have hmpos : 0<H.card := Nat.pos_of_ne_zero hm
  let I : Finset α → Finset α → ℝ := fun A B => (A∩B).card
  let Q : Finset α → Finset α → ℝ := fun A B =>
    ((H.card-(2*k-(A∩B).card)).choose τ:ℝ)*(H.card.choose τ:ℝ)/((H.card-k).choose τ:ℝ)^2
  have hi : ∀ A∈F, ∀ B∈F, I A B≤k := by
    intro A hA B _
    dsimp [I]
    exact_mod_cast (show (A∩B).card≤k by rw [←(hF A hA).2]; exact card_le_card inter_subset_left)
  have hq : ∀ A∈F, ∀ B∈F, Q A B≤Real.exp ((4*(τ:ℝ)/H.card)*I A B) := by
    intro A hA B hB
    have hiN : (A∩B).card≤k := by
      have h := hi A hA B hB
      dsimp [I] at h
      exact_mod_cast h
    have he : H.card-(2*k-(A∩B).card)=H.card-2*k+(A∩B).card := by omega
    dsimp [Q,I]
    rw [he,batch_joint_choose_eq_product H.card k τ (A∩B).card hk4 ht4]
    convert batch_joint_product_le_exp H.card k τ (A∩B).card hmpos hk4 ht4 using 1
    congr 1
    ring
  have hh := batch_sum_factor_bound F I Q (4*(τ:ℝ)/H.card) k (by positivity) (by positivity)
    (fun A _ B _ => by dsimp [I]; positivity) hi hq
  have hden : (0:ℝ)<(F.card:ℝ)^2 := sq_pos_of_pos hn
  have hs : (∑ A∈F, ∑ B∈F, I A B/(k:ℝ)) =
      (∑ A∈F, ∑ B∈F, I A B)/(k:ℝ) := by simp_rw [sum_div]
  rw [hs] at hh
  have hdiv := (div_le_div_iff_of_pos_right hden).2 hh
  change (∑ A∈F, ∑ B∈F, Q A B)/(F.card:ℝ)^2-1≤_
  unfold averageOverlap
  have he : Real.exp ((4*(τ:ℝ)/H.card)*(k:ℝ)) = Real.exp (4*(τ:ℝ)*k/H.card) := by congr 1; ring
  rw [he] at hdiv
  dsimp [I] at hdiv
  rw [add_div,div_self hden.ne'] at hdiv
  calc
    _ ≤ Real.exp (4*(τ:ℝ)*k/H.card) *
      ((∑ A∈F, ∑ B∈F, ((A∩B).card:ℝ))/(k:ℝ))/(F.card:ℝ)^2 := by linarith
    _ = _ := by ring

end LooseHamilton.FrameSurvival
