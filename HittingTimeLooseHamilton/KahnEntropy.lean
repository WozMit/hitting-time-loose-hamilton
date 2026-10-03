module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public section

open scoped BigOperators

noncomputable section

namespace FiniteEntropy

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Shannon entropy of a finite real-valued mass function, using natural logarithms. -/
@[expose] def entropy (p : A → ℝ) : ℝ := -∑ a, p a * Real.log (p a)

/-- A finite probability mass function. Zero masses are allowed. -/
structure Law (A : Type*) [Fintype A] where
  mass : A → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

lemma Law.mass_le_one (p : Law A) (a : A) : p.mass a ≤ 1 := by
  rw [← p.total]
  exact Finset.single_le_sum (fun b _ => p.nonneg b) (Finset.mem_univ a)

lemma Law.entropy_nonneg (p : Law A) : 0 ≤ entropy p.mass := by
  unfold entropy
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro a _
  exact mul_nonpos_of_nonneg_of_nonpos (p.nonneg a)
    (Real.log_nonpos (p.nonneg a) (p.mass_le_one a))

lemma mul_log_mul (x y : ℝ) :
    (x * y) * Real.log (x * y) = y * (x * Real.log x) + x * (y * Real.log y) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [Real.log_mul hx hy]
  ring

/-- The elementary relative-entropy inequality, valid also at zero mass. -/
lemma mul_log_ratio_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) :
    x * Real.log y - x * Real.log x ≤ y - x := by
  by_cases h : x = 0
  · simp only [h, zero_mul, sub_zero, sub_self]
    exact hy.le
  have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm h)
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hy hx')) hx
  rw [Real.log_div hy.ne' h] at hlog
  have hdiv : x * (y / x - 1) = y - x := by field_simp
  rw [hdiv] at hlog
  nlinarith

/-- Gibbs' inequality in a form that permits zero atoms in the first law. -/
lemma entropy_le_crossEntropy (p q : Law A) (hq : ∀ a, 0 < q.mass a) :
    entropy p.mass ≤ -∑ a, p.mass a * Real.log (q.mass a) := by
  have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) =>
    mul_log_ratio_le (p.mass a) (q.mass a) (p.nonneg a) (hq a))
  simp only [Finset.sum_sub_distrib, p.total, q.total, sub_self] at h
  unfold entropy
  linarith

/-- Gibbs' inequality only needs positivity on the support of the first law. -/
lemma entropy_le_crossEntropy_of_support (p q : Law A)
    (hsupp : ∀ a, q.mass a = 0 → p.mass a = 0) :
    entropy p.mass ≤ -∑ a, p.mass a * Real.log (q.mass a) := by
  have hpoint (a : A) :
      p.mass a * Real.log (q.mass a) - p.mass a * Real.log (p.mass a) ≤
        q.mass a - p.mass a := by
    by_cases hq : q.mass a = 0
    · simp [hq, hsupp a hq]
    · exact mul_log_ratio_le _ _ (p.nonneg a)
        (lt_of_le_of_ne (q.nonneg a) (Ne.symm hq))
  have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) => hpoint a)
  simp only [Finset.sum_sub_distrib, p.total, q.total, sub_self] at h
  unfold entropy
  linarith

/-- The uniform probability law on a nonempty finite type. -/
@[expose] def uniform [Nonempty A] : Law A where
  mass := fun _ => (Fintype.card A : ℝ)⁻¹
  nonneg := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

lemma entropy_uniform [Nonempty A] : entropy (uniform (A := A)).mass =
    Real.log (Fintype.card A) := by
  unfold entropy uniform
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.log_inv]
  have hn : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

/-- A finite law has entropy at most the logarithm of the size of its alphabet. -/
lemma entropy_le_log_card [Nonempty A] (p : Law A) :
    entropy p.mass ≤ Real.log (Fintype.card A) := by
  have h := entropy_le_crossEntropy p (uniform (A := A)) (fun _ =>
    inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  simpa only [uniform, Real.log_inv, ← Finset.sum_mul, p.total, one_mul, neg_neg] using h

/-- The chain rule for a finite law specified by a marginal and conditional laws. -/
lemma entropy_kernel (p : Law A) (q : A → Law B) :
    entropy (fun ab : A × B => p.mass ab.1 * (q ab.1).mass ab.2) =
      entropy p.mass + ∑ a, p.mass a * entropy (q a).mass := by
  unfold entropy
  simp_rw [Fintype.sum_prod_type, mul_log_mul, Finset.sum_add_distrib]
  have hrow (a : A) :
      (∑ b, (q a).mass b * (p.mass a * Real.log (p.mass a))) =
        p.mass a * Real.log (p.mass a) := by
    rw [← Finset.sum_mul, (q a).total, one_mul]
  simp_rw [hrow, ← Finset.mul_sum, mul_neg]
  rw [Finset.sum_neg_distrib]
  ring

/-- Entropy is additive for the product of two finite probability laws. -/
lemma entropy_product (p : Law A) (q : Law B) :
    entropy (fun ab : A × B => p.mass ab.1 * q.mass ab.2) =
      entropy p.mass + entropy q.mass := by
  rw [entropy_kernel p (fun _ => q), ← Finset.sum_mul, p.total, one_mul]

/-- Product law of independent finite variables. -/
@[expose] def Law.prod (p : Law A) (q : Law B) : Law (A × B) where
  mass := fun ab => p.mass ab.1 * q.mass ab.2
  nonneg := fun ab => mul_nonneg (p.nonneg _) (q.nonneg _)
  total := by
    simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, q.total, mul_one]
    exact p.total

/-- First marginal of a joint law. -/
@[expose] def Law.fst (p : Law (A × B)) : Law A where
  mass := fun a => ∑ b, p.mass (a,b)
  nonneg := fun _ => Finset.sum_nonneg (fun _ _ => p.nonneg _)
  total := by rw [← Fintype.sum_prod_type]; exact p.total

/-- Second marginal of a joint law. -/
@[expose] def Law.snd (p : Law (A × B)) : Law B where
  mass := fun b => ∑ a, p.mass (a,b)
  nonneg := fun _ => Finset.sum_nonneg (fun _ _ => p.nonneg _)
  total := by rw [Finset.sum_comm, ← Fintype.sum_prod_type]; exact p.total

lemma Law.mass_le_fst (p : Law (A × B)) (a : A) (b : B) :
    p.mass (a,b) ≤ p.fst.mass a := by
  exact Finset.single_le_sum (fun c _ => p.nonneg (a,c)) (Finset.mem_univ b)

lemma Law.mass_le_snd (p : Law (A × B)) (a : A) (b : B) :
    p.mass (a,b) ≤ p.snd.mass b := by
  exact Finset.single_le_sum (fun c _ => p.nonneg (c,b)) (Finset.mem_univ a)

/-- Subadditivity of entropy for arbitrary finite joint laws. -/
lemma entropy_subadditive (p : Law (A × B)) :
    entropy p.mass ≤ entropy p.fst.mass + entropy p.snd.mass := by
  have hsupp : ∀ ab, (p.fst.prod p.snd).mass ab = 0 → p.mass ab = 0 := by
    intro ⟨a,b⟩ h
    change p.fst.mass a * p.snd.mass b = 0 at h
    rcases mul_eq_zero.mp h with h | h
    · exact le_antisymm (h ▸ p.mass_le_fst a b) (p.nonneg _)
    · exact le_antisymm (h ▸ p.mass_le_snd a b) (p.nonneg _)
  have h := entropy_le_crossEntropy_of_support p (p.fst.prod p.snd) hsupp
  have hpoint (a : A) (b : B) :
      p.mass (a,b) * Real.log ((p.fst.prod p.snd).mass (a,b)) =
        p.mass (a,b) * Real.log (p.fst.mass a) +
          p.mass (a,b) * Real.log (p.snd.mass b) := by
    by_cases hz : (p.fst.prod p.snd).mass (a,b) = 0
    · simp [hsupp (a,b) hz]
    · change p.fst.mass a * p.snd.mass b ≠ 0 at hz
      change p.mass (a,b) * Real.log (p.fst.mass a * p.snd.mass b) = _
      rw [Real.log_mul (mul_ne_zero_iff.mp hz).1 (mul_ne_zero_iff.mp hz).2, mul_add]
  have heq : (∑ ab, p.mass ab * Real.log ((p.fst.prod p.snd).mass ab)) =
      (∑ a, p.fst.mass a * Real.log (p.fst.mass a)) +
      (∑ b, p.snd.mass b * Real.log (p.snd.mass b)) := by
    rw [Fintype.sum_prod_type]
    simp_rw [hpoint, Finset.sum_add_distrib]
    congr 1
    · simp_rw [← Finset.sum_mul]
      rfl
    · rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      rfl
  rw [heq, neg_add] at h
  exact h

/-- Normalize a nonnegative finite weight function with positive total mass. -/
@[expose] def normalize (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (hpos : 0 < ∑ a, w a) : Law A where
  mass := fun a => w a / ∑ b, w b
  nonneg := fun a => div_nonneg (hw a) hpos.le
  total := by rw [← Finset.sum_div, div_self hpos.ne']

/-- The finite Gibbs variational upper bound for a positive weight function. -/
lemma entropy_add_weight_le_log_sum (p : Law A) (w : A → ℝ)
    (hw : ∀ a, 0 < w a) (hpos : 0 < ∑ a, w a) :
    entropy p.mass + ∑ a, p.mass a * Real.log (w a) ≤ Real.log (∑ a, w a) := by
  have h := entropy_le_crossEntropy p (normalize w (fun a => (hw a).le) hpos)
    (fun a => div_pos (hw a) hpos)
  have hpoint (a : A) :
      p.mass a * Real.log ((normalize w (fun a => (hw a).le) hpos).mass a) =
      p.mass a * Real.log (w a) - p.mass a * Real.log (∑ b, w b) := by
    change p.mass a * Real.log (w a / ∑ b, w b) = _
    rw [Real.log_div (hw a).ne' hpos.ne', mul_sub]
  simp_rw [hpoint] at h
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, p.total, one_mul] at h
  linarith

/-- Gibbs variational bound with zero weights allowed away from the support. -/
lemma entropy_add_weight_le_log_sum_of_support (p : Law A) (w : A → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hpos : 0 < ∑ a, w a)
    (hsupp : ∀ a, w a = 0 → p.mass a = 0) :
    entropy p.mass + ∑ a, p.mass a * Real.log (w a) ≤ Real.log (∑ a, w a) := by
  have h := entropy_le_crossEntropy_of_support p (normalize w hw hpos) (by
    intro a ha
    apply hsupp a
    exact (div_eq_zero_iff.mp ha).resolve_right hpos.ne')
  have hpoint (a : A) :
      p.mass a * Real.log ((normalize w hw hpos).mass a) =
      p.mass a * Real.log (w a) - p.mass a * Real.log (∑ b, w b) := by
    by_cases ha : w a = 0
    · simp [hsupp a ha]
    · change p.mass a * Real.log (w a / ∑ b, w b) = _
      rw [Real.log_div ha hpos.ne', mul_sub]
  simp_rw [hpoint] at h
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, p.total, one_mul] at h
  linarith

end FiniteEntropy
