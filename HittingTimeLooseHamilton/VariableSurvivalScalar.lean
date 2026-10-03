module

public import HittingTimeLooseHamilton.BatchVarianceScalar
public import HittingTimeLooseHamilton.CandidateLogSurvival

public section

noncomputable section
open scoped BigOperators
namespace LooseHamilton

/-- One factor of the normalized joint survival ratio for unequal support sizes. -/
lemma variable_joint_factor_le_exp (m a b t I : ℝ)
    (hm : 0 < m) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) (hI : 0 ≤ I)
    (ha4 : 4*a ≤ m) (hb4 : 4*b ≤ m) (ht4 : 4*t ≤ m) :
    ((m-a-b+I-t)*(m-t))/((m-a-t)*(m-b-t)) ≤ Real.exp (4*I/m) := by
  have hda : 0 < m-a-t := by linarith
  have hdb : 0 < m-b-t := by linarith
  have hp : m*(m-t) ≤ 4*((m-a-t)*(m-b-t)) := by
    have h1 := mul_nonneg (show 0 ≤ m-a-t-m/2 by linarith)
      (show 0 ≤ m-b-t by linarith)
    have h2 := mul_nonneg (show 0 ≤ m-b-t-m/2 by linarith) hm.le
    nlinarith
  have hh : ((m-a-b+I-t)*(m-t))/((m-a-t)*(m-b-t)) ≤ 1+4*I/m := by
    apply (div_le_iff₀ (mul_pos hda hdb)).2
    apply (mul_le_mul_iff_left₀ hm).mp
    have hi := mul_le_mul_of_nonneg_right hp hI
    have he : ((1+4*I/m)*((m-a-t)*(m-b-t)))*m =
        (m+4*I)*((m-a-t)*(m-b-t)) := by field_simp
    rw [he]
    nlinarith [mul_nonneg (mul_nonneg ha hb) hm.le]
  exact hh.trans (by simpa [add_comm] using Real.add_one_le_exp (4*I/m))

/-- Multiplying the unequal-support factors costs only the intersection size. -/
lemma variable_joint_product_le_exp (m a b τ I : ℕ)
    (hm : 0 < m) (ha4 : 4*a ≤ m) (hb4 : 4*b ≤ m) (ht4 : 4*τ ≤ m) :
    (∏ i ∈ Finset.range τ,
      (((m:ℝ)-a-b+I-i)*((m:ℝ)-i))/(((m:ℝ)-a-i)*((m:ℝ)-b-i))) ≤
      Real.exp (4*(τ:ℝ)*I/m) := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have haR : 4*(a:ℝ)≤m := by exact_mod_cast ha4
  have hbR : 4*(b:ℝ)≤m := by exact_mod_cast hb4
  have htR : 4*(τ:ℝ)≤m := by exact_mod_cast ht4
  calc
    _ ≤ ∏ i ∈ Finset.range τ, Real.exp (4*(I:ℝ)/m) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        have hiR : (i:ℝ)≤τ := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hi))
        apply div_nonneg
        · apply mul_nonneg <;> linarith [show (0:ℝ)≤I by positivity]
        · apply mul_nonneg <;> linarith
      · intro i hi
        apply variable_joint_factor_le_exp (m:ℝ) a b i I hmR
          (by positivity) (by positivity) (by positivity) (by positivity) haR hbR
        have hiR : (i:ℝ)≤τ := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hi))
        linarith
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_range]
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end LooseHamilton
