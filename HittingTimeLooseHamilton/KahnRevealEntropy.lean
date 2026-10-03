module

public import HittingTimeLooseHamilton.KahnConditioning
public import HittingTimeLooseHamilton.KahnLogSum

public section

open scoped BigOperators
noncomputable section
namespace FiniteEntropy
namespace Law
variable {Y Z : Type*} [Fintype Y] [Fintype Z]

lemma map_snd_eq (p : Law (Y × Z)) : p.map Prod.snd = p.snd := by
  classical
  apply ext_mass
  intro z
  simp [map, event, snd, Fintype.sum_prod_type]

/-- When an observation identifies the value, its fiber contributes zero entropy. -/
lemma known_mass_eq_marginal (p : Law (Y × (Y ⊕ Z)))
    (hknown : ∀ y y', y ≠ y' → p.mass (y, Sum.inl y') = 0) (y : Y) :
    p.mass (y, Sum.inl y) = p.snd.mass (Sum.inl y) := by
  classical
  change _ = ∑ a, p.mass (a, Sum.inl y)
  symm
  exact Finset.sum_eq_single y (fun a _ ha => hknown a y ha) (by simp)

/-- Exact entropy decomposition for an observation that either identifies the value
or supplies partial information. The unknown branch has conditional mass `c`.
This is the abstract finite form of equations (31)--(32) of Kahn's paper. -/
lemma reveal_entropy_eq (p : Law (Y × (Y ⊕ Z)))
    (u : Y → Z → ℝ) (c : ℝ)
    (hu : ∀ y z, 0 ≤ u y z)
    (hknown : ∀ y y', y ≠ y' → p.mass (y, Sum.inl y') = 0)
    (hunknown : ∀ y z, p.mass (y, Sum.inr z) = p.fst.mass y * u y z)
    (hsum : ∀ y, ∑ z, u y z = c) :
    p.conditionalEntropy Prod.snd =
      c * entropy p.fst.mass +
        ∑ y, p.fst.mass y * ∑ z, u y z * Real.log (p.snd.mass (Sum.inr z) / u y z) := by
  classical
  have hk (y y' : Y) :
      p.mass (y, Sum.inl y') *
        Real.log (p.mass (y, Sum.inl y') / p.snd.mass (Sum.inl y')) = 0 := by
    by_cases he : y = y'
    · subst y'
      rw [p.known_mass_eq_marginal hknown y]
      by_cases hz : p.snd.mass (Sum.inl y) = 0
      · simp [hz]
      · simp [div_self hz]
    · simp [hknown y y' he]
  have hu' (y : Y) (z : Z) :
      -(p.mass (y, Sum.inr z) *
        Real.log (p.mass (y, Sum.inr z) / p.snd.mass (Sum.inr z))) =
      -(u y z * (p.fst.mass y * Real.log (p.fst.mass y))) +
        p.fst.mass y * (u y z * Real.log (p.snd.mass (Sum.inr z) / u y z)) := by
    rw [hunknown]
    by_cases hp : p.fst.mass y = 0
    · simp [hp]
    by_cases hz : u y z = 0
    · simp [hz]
    have hj : 0 < p.mass (y, Sum.inr z) := by
      rw [hunknown]
      exact mul_pos (lt_of_le_of_ne (p.fst.nonneg y) (Ne.symm hp))
        (lt_of_le_of_ne (hu y z) (Ne.symm hz))
    have hb : p.snd.mass (Sum.inr z) ≠ 0 :=
      (lt_of_lt_of_le hj (p.mass_le_snd y (Sum.inr z))).ne'
    rw [Real.log_div (mul_ne_zero hp hz) hb, Real.log_mul hp hz,
      Real.log_div hb hz]
    ring
  unfold conditionalEntropy
  rw [p.map_snd_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, hk, Finset.sum_const_zero, zero_add]
  rw [← Finset.sum_neg_distrib]
  simp_rw [← Finset.sum_neg_distrib, hu', Finset.sum_add_distrib]
  simp_rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hsum, ← Finset.mul_sum]
  simp [entropy, mul_neg]

/-- Grouping the unknown observations by a finite statistic gives Kahn's
log-sum bound (33). Compatibility restricts the marginal mass in each group. -/
lemma reveal_entropy_le_grouped {K : Type*} [Fintype K] [DecidableEq K]
    (p : Law (Y × (Y ⊕ Z))) (u : Y → Z → ℝ) (c : ℝ)
    (hu : ∀ y z, 0 ≤ u y z)
    (hknown : ∀ y y', y ≠ y' → p.mass (y, Sum.inl y') = 0)
    (hunknown : ∀ y z, p.mass (y, Sum.inr z) = p.fst.mass y * u y z)
    (hsum : ∀ y, ∑ z, u y z = c)
    (size : Z → K) (compatible : Y → Z → Prop) [DecidableRel compatible]
    (hcompatible : ∀ y z, p.fst.mass y ≠ 0 → ¬ compatible y z → u y z = 0)
    (q : K → ℝ)
    (hq : ∀ y, p.fst.mass y ≠ 0 → ∀ k, (∑ z, if size z = k then u y z else 0) = q k) :
    p.conditionalEntropy Prod.snd ≤ c * entropy p.fst.mass +
      ∑ y, p.fst.mass y * ∑ k, q k *
        Real.log ((∑ z, if size z = k ∧ compatible y z
          then p.snd.mass (Sum.inr z) else 0) / q k) := by
  classical
  rw [p.reveal_entropy_eq u c hu hknown hunknown hsum]
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro y _
  by_cases hp : p.fst.mass y = 0
  · simp [hp]
  apply mul_le_mul_of_nonneg_left _ (p.fst.nonneg y)
  let w : Z → ℝ := fun z => if compatible y z then p.snd.mass (Sum.inr z) else 0
  have hw (z : Z) : 0 ≤ w z := ite_nonneg (p.snd.nonneg _) (le_refl 0)
  have hs (z : Z) (hz : w z = 0) : u y z = 0 := by
    by_cases hc : compatible y z
    · have hb : p.snd.mass (Sum.inr z) = 0 := by simpa [w, hc] using hz
      have hj : p.mass (y, Sum.inr z) = 0 :=
        le_antisymm (hb ▸ p.mass_le_snd y (Sum.inr z)) (p.nonneg _)
      rw [hunknown] at hj
      exact (mul_eq_zero.mp hj).resolve_left hp
    · exact hcompatible y z hp hc
  have hl := log_sum_le_grouped (u y) w size (hu y) hw hs
  have he (z : Z) : u y z * Real.log (w z / u y z) =
      u y z * Real.log (p.snd.mass (Sum.inr z) / u y z) := by
    by_cases hc : compatible y z
    · simp [w, hc]
    · simp [hcompatible y z hp hc]
  simp_rw [he, hq y hp] at hl
  have hg (k : K) : (∑ z, if size z = k then w z else 0) =
      ∑ z, if size z = k ∧ compatible y z then p.snd.mass (Sum.inr z) else 0 := by
    apply Finset.sum_congr rfl
    intro z _
    simp [w, ite_and]
  simpa only [hg] using hl

/-- A version of the reveal bound whose hypotheses involve joint probabilities only.
Null marginal values require no separately chosen conditional probabilities. -/
lemma reveal_entropy_le_of_joint_masses {K : Type*} [Fintype K] [DecidableEq K]
    (p : Law (Y × (Y ⊕ Z))) (c : ℝ)
    (hknown : ∀ y y', y ≠ y' → p.mass (y, Sum.inl y') = 0)
    (hrow : ∀ y, (∑ z, p.mass (y, Sum.inr z)) = c * p.fst.mass y)
    (size : Z → K) (compatible : Y → Z → Prop) [DecidableRel compatible]
    (hcompatible : ∀ y z, ¬ compatible y z → p.mass (y, Sum.inr z) = 0)
    (q : K → ℝ)
    (hgroup : ∀ y k, (∑ z, if size z = k then p.mass (y, Sum.inr z) else 0) =
      p.fst.mass y * q k) :
    p.conditionalEntropy Prod.snd ≤ c * entropy p.fst.mass +
      ∑ y, p.fst.mass y * ∑ k, q k *
        Real.log ((∑ z, if size z = k ∧ compatible y z
          then p.snd.mass (Sum.inr z) else 0) / q k) := by
  classical
  have hex : ∃ y₀, 0 < p.fst.mass y₀ := by
    by_contra h
    push_neg at h
    have hz : ∑ y, p.fst.mass y = 0 :=
      Finset.sum_eq_zero fun y _ => le_antisymm (h y) (p.fst.nonneg y)
    rw [p.fst.total] at hz
    norm_num at hz
  obtain ⟨y₀, hy₀⟩ := hex
  let u : Y → Z → ℝ := fun y z =>
    if p.fst.mass y = 0 then p.mass (y₀, Sum.inr z) / p.fst.mass y₀
    else p.mass (y, Sum.inr z) / p.fst.mass y
  have hu (y : Y) (z : Z) : 0 ≤ u y z := by
    unfold u
    split_ifs
    · exact div_nonneg (p.nonneg _) (p.fst.nonneg _)
    · exact div_nonneg (p.nonneg _) (p.fst.nonneg _)
  have hunknown (y : Y) (z : Z) :
      p.mass (y, Sum.inr z) = p.fst.mass y * u y z := by
    by_cases hy : p.fst.mass y = 0
    · have hz : p.mass (y, Sum.inr z) = 0 :=
        le_antisymm (hy ▸ p.mass_le_fst y (Sum.inr z)) (p.nonneg _)
      simp [u, hy, hz]
    · simp only [u, if_neg hy]
      exact (mul_div_cancel₀ _ hy).symm
  have hsum (y : Y) : ∑ z, u y z = c := by
    by_cases hy : p.fst.mass y = 0
    · simp only [u, if_pos hy]
      rw [← Finset.sum_div, hrow, mul_div_cancel_right₀ _ hy₀.ne']
    · simp only [u, if_neg hy]
      rw [← Finset.sum_div, hrow, mul_div_cancel_right₀ _ hy]
  apply p.reveal_entropy_le_grouped u c hu hknown hunknown hsum size compatible
  · intro y z hy hc
    simp [u, hy, hcompatible y z hc]
  · intro y hy k
    simp only [u, if_neg hy]
    have he (z : Z) : (if size z = k then p.mass (y, Sum.inr z) / p.fst.mass y else 0) =
        (if size z = k then p.mass (y, Sum.inr z) else 0) / p.fst.mass y := by
      split_ifs <;> simp
    simp_rw [he]
    rw [← Finset.sum_div, hgroup, mul_div_cancel_left₀ _ hy]

/-- Relax each compatible marginal group to an upper bound.
The joint support guarantees positivity of the logarithm's argument whenever
its coefficient is positive. -/
lemma reveal_entropy_le_of_group_bounds {K : Type*} [Fintype K] [DecidableEq K]
    (p : Law (Y × (Y ⊕ Z))) (c : ℝ)
    (hknown : ∀ y y', y ≠ y' → p.mass (y, Sum.inl y') = 0)
    (hrow : ∀ y, (∑ z, p.mass (y, Sum.inr z)) = c * p.fst.mass y)
    (size : Z → K) (compatible : Y → Z → Prop) [DecidableRel compatible]
    (hcompatible : ∀ y z, ¬ compatible y z → p.mass (y, Sum.inr z) = 0)
    (q : K → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hgroup : ∀ y k, (∑ z, if size z = k then p.mass (y, Sum.inr z) else 0) =
      p.fst.mass y * q k)
    (B : Y → K → ℝ)
    (hbound : ∀ y k, (∑ z, if size z = k ∧ compatible y z
      then p.snd.mass (Sum.inr z) else 0) ≤ q k * B y k) :
    p.conditionalEntropy Prod.snd ≤ c * entropy p.fst.mass +
      ∑ y, p.fst.mass y * ∑ k, q k * Real.log (B y k) := by
  classical
  apply (p.reveal_entropy_le_of_joint_masses c hknown hrow size compatible
    hcompatible q hgroup).trans
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : p.fst.mass y = 0
  · simp [hy]
  apply mul_le_mul_of_nonneg_left _ (p.fst.nonneg y)
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : q k = 0
  · simp [hk]
  have hqp : 0 < q k := lt_of_le_of_ne (hq k) (Ne.symm hk)
  have hyp : 0 < p.fst.mass y := lt_of_le_of_ne (p.fst.nonneg y) (Ne.symm hy)
  have hlower : p.fst.mass y * q k ≤
      ∑ z, if size z = k ∧ compatible y z then p.snd.mass (Sum.inr z) else 0 := by
    rw [← hgroup y k]
    apply Finset.sum_le_sum
    intro z _
    by_cases hs : size z = k
    · by_cases hc : compatible y z
      · simp only [hs, hc, and_self, ↓reduceIte]
        exact p.mass_le_snd y (Sum.inr z)
      · simp [hs, hc, hcompatible y z hc]
    · simp [hs]
  have hrp : 0 < ∑ z, if size z = k ∧ compatible y z
      then p.snd.mass (Sum.inr z) else 0 := lt_of_lt_of_le (mul_pos hyp hqp) hlower
  apply mul_le_mul_of_nonneg_left _ (hq k)
  apply Real.log_le_log (div_pos hrp hqp)
  exact (div_le_iff₀ hqp).mpr (by simpa [mul_comm] using hbound y k)

/-- The relaxed group bound need only hold on the marginal support. -/
lemma reveal_entropy_le_of_group_bounds_on_support {K : Type*} [Fintype K] [DecidableEq K]
    (p : Law (Y × (Y ⊕ Z))) (c : ℝ)
    (hknown : ∀ y y', y ≠ y' → p.mass (y, Sum.inl y') = 0)
    (hrow : ∀ y, (∑ z, p.mass (y, Sum.inr z)) = c * p.fst.mass y)
    (size : Z → K) (compatible : Y → Z → Prop) [DecidableRel compatible]
    (hcompatible : ∀ y z, ¬ compatible y z → p.mass (y, Sum.inr z) = 0)
    (q : K → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hgroup : ∀ y k, (∑ z, if size z = k then p.mass (y, Sum.inr z) else 0) =
      p.fst.mass y * q k)
    (B : Y → K → ℝ)
    (hbound : ∀ y, p.fst.mass y ≠ 0 → ∀ k, (∑ z, if size z = k ∧ compatible y z
      then p.snd.mass (Sum.inr z) else 0) ≤ q k * B y k) :
    p.conditionalEntropy Prod.snd ≤ c * entropy p.fst.mass +
      ∑ y, p.fst.mass y * ∑ k, q k * Real.log (B y k) := by
  classical
  apply (p.reveal_entropy_le_of_joint_masses c hknown hrow size compatible
    hcompatible q hgroup).trans
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : p.fst.mass y = 0
  · simp [hy]
  apply mul_le_mul_of_nonneg_left _ (p.fst.nonneg y)
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : q k = 0
  · simp [hk]
  have hqp : 0 < q k := lt_of_le_of_ne (hq k) (Ne.symm hk)
  have hyp : 0 < p.fst.mass y := lt_of_le_of_ne (p.fst.nonneg y) (Ne.symm hy)
  have hlower : p.fst.mass y * q k ≤
      ∑ z, if size z = k ∧ compatible y z then p.snd.mass (Sum.inr z) else 0 := by
    rw [← hgroup y k]
    apply Finset.sum_le_sum
    intro z _
    by_cases hs : size z = k
    · by_cases hc : compatible y z
      · simp only [hs, hc, and_self, ↓reduceIte]
        exact p.mass_le_snd y (Sum.inr z)
      · simp [hs, hc, hcompatible y z hc]
    · simp [hs]
  have hrp : 0 < ∑ z, if size z = k ∧ compatible y z
      then p.snd.mass (Sum.inr z) else 0 := lt_of_lt_of_le (mul_pos hyp hqp) hlower
  apply mul_le_mul_of_nonneg_left _ (hq k)
  apply Real.log_le_log (div_pos hrp hqp)
  exact (div_le_iff₀ hqp).mpr (by simpa [mul_comm] using hbound y hy k)

end Law
end FiniteEntropy
