module

public import HittingTimeLooseHamilton.UniformOrderCounting
public import Mathlib.Tactic

public section
noncomputable section
namespace LooseHamilton.StoppedDeletion
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

@[expose] def History (j : ℕ) (σ : FiniteOrder A) : A → Option (Fin (Fintype.card A)) :=
  fun a => if j ≤ (σ a).val then some (σ a) else none

lemma history_rank_eq {j : ℕ} {σ τ : FiniteOrder A}
    (h : History j σ = History j τ) (a : A) (ha : j ≤ (σ a).val) : σ a = τ a := by
  have he := congrFun h a
  simp only [History,if_pos ha] at he
  split_ifs at he with hb
  · exact Option.some.inj he

lemma history_prefix_eq {j : ℕ} {σ τ : FiniteOrder A}
    (h : History j σ = History j τ) : orderPrefix σ j = orderPrefix τ j := by
  ext a
  simp only [mem_orderPrefix]
  constructor
  · intro ha
    by_contra hn
    have he := history_rank_eq h.symm a (Nat.le_of_not_gt hn)
    have hh : j ≤ (σ a).val := by rw [← he]; omega
    omega
  · intro ha
    by_contra hn
    have he := history_rank_eq h a (Nat.le_of_not_gt hn)
    have hh : j ≤ (τ a).val := by rw [← he]; omega
    omega

lemma history_mono {j l : ℕ} (hjl : j ≤ l) {σ τ : FiniteOrder A}
    (h : History j σ = History j τ) : History l σ = History l τ := by
  funext a
  by_cases ha : j ≤ (σ a).val
  · simp only [History,history_rank_eq h a ha]
  · have hb : ¬ j ≤ (τ a).val := by
      intro hb
      have he := history_rank_eq h.symm a hb
      apply ha; simpa only [← he] using hb
    simp only [History,if_neg (show ¬l ≤ (σ a).val by omega),
      if_neg (show ¬l ≤ (τ a).val by omega)]

@[expose] def rankSwap (j : ℕ) (hj : j ≤ Fintype.card A) (hpos : 0 < j) (i : Fin j) :
    FiniteOrder A ≃ FiniteOrder A :=
  Equiv.equivCongr (Equiv.refl A)
    (Equiv.swap ⟨j-1,by omega⟩ ⟨i.val,lt_of_lt_of_le i.isLt hj⟩)

lemma rankSwap_apply (j : ℕ) (hj : j ≤ Fintype.card A) (hpos : 0 < j)
    (i : Fin j) (σ : FiniteOrder A) (a : A) :
    rankSwap j hj hpos i σ a = Equiv.swap ⟨j-1,by omega⟩
      ⟨i.val,lt_of_lt_of_le i.isLt hj⟩ (σ a) := rfl

lemma rankSwap_prefix (j : ℕ) (hj : j ≤ Fintype.card A) (hpos : 0 < j)
    (i : Fin j) (σ : FiniteOrder A) :
    orderPrefix (rankSwap j hj hpos i σ) j = orderPrefix σ j := by
  ext a
  simp only [mem_orderPrefix,rankSwap_apply]
  by_cases h₁ : σ a = ⟨j-1,by omega⟩
  · rw [h₁,Equiv.swap_apply_left]; exact iff_of_true i.isLt (by simp; omega)
  by_cases h₂ : σ a = ⟨i.val,lt_of_lt_of_le i.isLt hj⟩
  · rw [h₂,Equiv.swap_apply_right]; exact iff_of_true (by simp; omega) i.isLt
  rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂]

lemma rankSwap_history (j : ℕ) (hj : j ≤ Fintype.card A) (hpos : 0 < j)
    (i : Fin j) (σ : FiniteOrder A) :
    History j (rankSwap j hj hpos i σ) = History j σ := by
  funext a
  simp only [History,rankSwap_apply]
  by_cases h₁ : σ a = ⟨j-1,by omega⟩
  · simp only [h₁,Equiv.swap_apply_left]; simp [Nat.not_le.mpr i.isLt, show ¬j ≤ j-1 by omega]
  by_cases h₂ : σ a = ⟨i.val,lt_of_lt_of_le i.isLt hj⟩
  · simp only [h₂,Equiv.swap_apply_right]; simp [Nat.not_le.mpr i.isLt, show ¬j ≤ j-1 by omega]
  simp only [Equiv.swap_apply_of_ne_of_ne h₁ h₂]

lemma rankSwap_boundary (j : ℕ) (hj : j ≤ Fintype.card A) (hpos : 0 < j)
    (i : Fin j) (σ : FiniteOrder A) :
    orderBoundary (rankSwap j hj hpos i σ) j hj hpos =
      σ.symm ⟨i.val,lt_of_lt_of_le i.isLt hj⟩ := by
  simp [orderBoundary,rankSwap,Equiv.equivCongr]

lemma sum_prefix_values (j : ℕ) (hj : j ≤ Fintype.card A)
    (σ : FiniteOrder A) (f : A → ℝ) :
    ∑ i : Fin j, f (σ.symm ⟨i.val,lt_of_lt_of_le i.isLt hj⟩) =
      ∑ a ∈ orderPrefix σ j, f a := by
  apply Finset.sum_bij (fun i _ => σ.symm ⟨i.val,lt_of_lt_of_le i.isLt hj⟩)
  · intro i hi; simp
  · intro i hi l hl he
    exact Fin.ext (congrArg (fun x : Fin (Fintype.card A) => x.val) (σ.symm.injective he))
  · intro a ha
    refine ⟨⟨(σ a).val, (mem_orderPrefix σ j a).mp ha⟩,mem_univ _,?_⟩
    simp
  · intro i hi; rfl

/-- Exact conditional centering for uniform deletion, tested against any
weight determined by the complete ordered deleted suffix. -/
theorem weighted_centering_of (j : ℕ) (hj : j ≤ Fintype.card A) (hpos : 0 < j)
    (W : FiniteOrder A → ℝ) (q : Finset A → A → ℝ)
    (hW : ∀ σ τ, History j σ = History j τ → W σ = W τ)
    (hq : ∀ σ : FiniteOrder A, W σ ≠ 0 →
      ∑ a ∈ orderPrefix σ j, q (orderPrefix σ j) a = 0) :
    ∑ σ : FiniteOrder A, W σ * q (orderPrefix σ j) (orderBoundary σ j hj hpos) = 0 := by
  let B : ℝ := ∑ σ : FiniteOrder A,
    W σ * q (orderPrefix σ j) (orderBoundary σ j hj hpos)
  have hi (i : Fin j) :
      (∑ σ : FiniteOrder A, W σ * q (orderPrefix σ j)
        (σ.symm ⟨i.val,lt_of_lt_of_le i.isLt hj⟩)) = B := by
    have he := Equiv.sum_comp (rankSwap j hj hpos i)
      (fun σ => W σ * q (orderPrefix σ j) (orderBoundary σ j hj hpos))
    simpa only [rankSwap_prefix,rankSwap_boundary,
      hW _ _ (rankSwap_history j hj hpos i _)] using he
  have hz : (j : ℝ) * B = 0 := by
    calc
      (j : ℝ) * B = ∑ i : Fin j, B := by simp
      _ = ∑ i : Fin j, ∑ σ : FiniteOrder A, W σ * q (orderPrefix σ j)
          (σ.symm ⟨i.val,lt_of_lt_of_le i.isLt hj⟩) := by simp only [hi]
      _ = ∑ σ : FiniteOrder A, W σ * ∑ i : Fin j,
          q (orderPrefix σ j) (σ.symm ⟨i.val,lt_of_lt_of_le i.isLt hj⟩) := by
            rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro σ hσ
        by_cases hw : W σ = 0
        · simp [hw]
        · rw [sum_prefix_values j hj, hq σ hw,mul_zero]
  exact (mul_eq_zero.mp hz).resolve_left (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos))
theorem weighted_centering (j : ℕ) (hj : j ≤ Fintype.card A) (hpos : 0 < j)
    (W : FiniteOrder A → ℝ) (q : Finset A → A → ℝ)
    (hW : ∀ σ τ, History j σ = History j τ → W σ = W τ)
    (hq : ∀ S : Finset A, S.card = j → ∑ a ∈ S, q S a = 0) :
    ∑ σ : FiniteOrder A, W σ * q (orderPrefix σ j) (orderBoundary σ j hj hpos) = 0 :=
  weighted_centering_of j hj hpos W q hW (fun σ _ => hq _ (orderPrefix_card σ j hj))

end LooseHamilton.StoppedDeletion
