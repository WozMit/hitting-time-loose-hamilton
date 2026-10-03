module

public import HittingTimeLooseHamilton.KahnLaw

public section

open scoped BigOperators
noncomputable section
namespace FiniteEntropy

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The log-sum inequality when both total masses are positive. -/
lemma log_sum_le_of_pos (x y : A → ℝ) (hx : ∀ a, 0 ≤ x a)
    (hy : ∀ a, 0 ≤ y a) (hsupp : ∀ a, y a = 0 → x a = 0)
    (hX : 0 < ∑ a, x a) (hY : 0 < ∑ a, y a) :
    (∑ a, x a * Real.log (y a / x a)) ≤
      (∑ a, x a) * Real.log ((∑ a, y a) / (∑ a, x a)) := by
  let X := ∑ a, x a
  let Y := ∑ a, y a
  have hXp : 0 < X := hX
  have hYp : 0 < Y := hY
  have hpoint (a : A) : x a * Real.log (y a / x a) ≤
      x a * Real.log (Y / X) + y a * X / Y - x a := by
    by_cases hxa : x a = 0
    · simp only [hxa, zero_mul, add_zero, sub_zero]
      simpa using div_nonneg (mul_nonneg (hy a) hXp.le) hYp.le
    have hya : y a ≠ 0 := fun h => hxa (hsupp a h)
    have hyp : 0 < y a := lt_of_le_of_ne (hy a) (Ne.symm hya)
    have h := mul_log_ratio_le (x a) (y a * X / Y) (hx a) (by positivity)
    rw [Real.log_div (mul_ne_zero hya hXp.ne') hYp.ne',
      Real.log_mul hya hXp.ne'] at h
    rw [Real.log_div hya hxa, Real.log_div hYp.ne' hXp.ne']
    nlinarith
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) => hpoint a)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_div] at hsum
  change (∑ a, x a * Real.log (y a / x a)) ≤ X * Real.log (Y / X)
  have heq : Y * X / Y = X := by field_simp
  change (∑ a, x a * Real.log (y a / x a)) ≤ X * Real.log (Y / X) + Y * X / Y - X at hsum
  rw [heq] at hsum
  linarith

/-- General finite log-sum inequality, including zero masses and zero totals. -/
lemma log_sum_le (x y : A → ℝ) (hx : ∀ a, 0 ≤ x a)
    (hy : ∀ a, 0 ≤ y a) (hsupp : ∀ a, y a = 0 → x a = 0) :
    (∑ a, x a * Real.log (y a / x a)) ≤
      (∑ a, x a) * Real.log ((∑ a, y a) / (∑ a, x a)) := by
  have hX : 0 ≤ ∑ a, x a := Finset.sum_nonneg (fun a _ => hx a)
  have hY : 0 ≤ ∑ a, y a := Finset.sum_nonneg (fun a _ => hy a)
  by_cases hX0 : (∑ a, x a) = 0
  · have hx0 (a : A) : x a = 0 := by
      have h := Finset.single_le_sum (fun b (_ : b ∈ (Finset.univ : Finset A)) => hx b)
        (Finset.mem_univ a)
      rw [hX0] at h
      exact le_antisymm h (hx a)
    simp [hx0]
  by_cases hY0 : (∑ a, y a) = 0
  · have hy0 (a : A) : y a = 0 := by
      have h := Finset.single_le_sum (fun b (_ : b ∈ (Finset.univ : Finset A)) => hy b)
        (Finset.mem_univ a)
      rw [hY0] at h
      exact le_antisymm h (hy a)
    have hx0 (a : A) : x a = 0 := hsupp a (hy0 a)
    simp [hx0]
  exact log_sum_le_of_pos x y hx hy hsupp (lt_of_le_of_ne hX (Ne.symm hX0))
    (lt_of_le_of_ne hY (Ne.symm hY0))

/-- Log-sum applied within every fiber of a finite statistic. -/
lemma log_sum_le_grouped [DecidableEq B] (x y : A → ℝ) (f : A → B) (hx : ∀ a, 0 ≤ x a)
    (hy : ∀ a, 0 ≤ y a) (hsupp : ∀ a, y a = 0 → x a = 0) :
    (∑ a, x a * Real.log (y a / x a)) ≤
      ∑ b, (∑ a, if f a = b then x a else 0) *
        Real.log ((∑ a, if f a = b then y a else 0) /
          (∑ a, if f a = b then x a else 0)) := by
  classical
  have hf (b : B) := log_sum_le
    (fun a => if f a = b then x a else 0)
    (fun a => if f a = b then y a else 0)
    (fun a => ite_nonneg (hx a) (le_refl 0))
    (fun a => ite_nonneg (hy a) (le_refl 0)) (by
      intro a ha
      by_cases hab : f a = b
      · simp only [hab, ↓reduceIte] at ha ⊢
        exact hsupp a ha
      · simp [hab])
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset B)) => hf b)
  have hpoint (a : A) (b : B) :
      (if f a = b then x a else 0) *
        Real.log ((if f a = b then y a else 0) / (if f a = b then x a else 0)) =
        if f a = b then x a * Real.log (y a / x a) else 0 := by
    split_ifs <;> simp
  simp_rw [hpoint] at hsum
  rw [Finset.sum_comm] at hsum
  simpa using hsum

end FiniteEntropy
