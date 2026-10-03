module

public import HittingTimeLooseHamilton.KahnConditioning
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy

/-- Relative entropy in cross-entropy form; used with a positive reference law. -/
@[expose] def finiteRelativeEntropy {A : Type*} [Fintype A] (p q : Law A) : ℝ :=
  -entropy p.mass - ∑ a, p.mass a * Real.log (q.mass a)

lemma finiteRelativeEntropy_nonneg {A : Type*} [Fintype A]
    (p q : Law A) (hq : ∀ a, 0 < q.mass a) :
    0 ≤ finiteRelativeEntropy p q := by
  have h := entropy_le_crossEntropy p q hq
  unfold finiteRelativeEntropy
  linarith

lemma finiteRelativeEntropy_uniform {A : Type*} [Fintype A] [Nonempty A]
    (p : Law A) : finiteRelativeEntropy p uniform =
      Real.log (Fintype.card A) - entropy p.mass := by
  simp only [finiteRelativeEntropy, uniform, Real.log_inv, mul_neg,
    Finset.sum_neg_distrib, ← Finset.sum_mul, p.total, one_mul]
  ring

/-- A reference event of mass at most `t` transfers with only a logarithmic
relative entropy loss. This is the binary coarsening estimate used in (collision). -/
lemma rare_event_entropy_bound {A : Type*} [Fintype A]
    (p q : Law A) (hq : ∀ a, 0 < q.mass a) (E : A → Prop)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (hE : q.event E ≤ t) :
    p.event E ≤ (finiteRelativeEntropy p q + Real.log 2) / Real.log (1/t) := by
  classical
  let w : A → ℝ := fun a => q.mass a * (if E a then 1/t else 1)
  have hw (a : A) : 0 < w a := by
    dsimp [w]
    split_ifs
    · exact mul_pos (hq a) (div_pos zero_lt_one ht)
    · simpa using hq a
  have hqsum : (∑ a, q.mass a * (if E a then 1/t else 1)) =
      1 + (1/t - 1) * q.event E := by
    have hpt (a : A) : q.mass a * (if E a then 1/t else 1) =
        q.mass a + (1/t - 1) * (if E a then q.mass a else 0) := by
      split_ifs <;> ring
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, q.total]
    rfl
  have hinv : 0 ≤ 1/t-1 := by
    have : 1 ≤ 1/t := (le_div_iff₀ ht).mpr (by simpa using ht1.le)
    linarith
  have hsum2 : (∑ a, w a) ≤ 2 := by
    change (∑ a, q.mass a * (if E a then 1/t else 1)) ≤ 2
    rw [hqsum]
    have h := mul_le_mul_of_nonneg_left hE hinv
    have heq : (1/t-1)*t = 1-t := by field_simp
    rw [heq] at h
    linarith
  have hsumpos : 0 < ∑ a, w a := by
    change 0 < ∑ a, q.mass a * (if E a then 1/t else 1)
    rw [hqsum]
    have := mul_nonneg hinv (q.event_nonneg E)
    linarith
  have hg := entropy_add_weight_le_log_sum p w hw hsumpos
  have hpt (a : A) : p.mass a * Real.log (w a) =
      p.mass a * Real.log (q.mass a) +
        (if E a then p.mass a else 0) * Real.log (1/t) := by
    dsimp [w]
    split_ifs
    · rw [Real.log_mul (hq a).ne' (div_pos zero_lt_one ht).ne', mul_add]
    · simp
  simp_rw [hpt] at hg
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hg
  change entropy p.mass + ((∑ a, p.mass a * Real.log (q.mass a)) +
    p.event E * Real.log (1/t)) ≤ _ at hg
  have hlog := Real.log_le_log hsumpos hsum2
  have htlog : 0 < Real.log (1/t) := Real.log_pos ((lt_div_iff₀ ht).mpr (by simpa using ht1))
  apply (le_div_iff₀ htlog).mpr
  unfold finiteRelativeEntropy
  linarith

end LooseHamilton
