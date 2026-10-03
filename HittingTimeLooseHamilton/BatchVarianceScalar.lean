module

public import HittingTimeLooseHamilton.KahnEntropy
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

public section

noncomputable section
open scoped BigOperators
namespace LooseHamilton

/-- A single factor in the normalized probability that two sets survive a batch. -/
lemma batch_joint_factor_le_exp (m k t I : ℝ)
    (hm : 0 < m) (_hk : 0 ≤ k) (ht : 0 ≤ t) (hI : 0 ≤ I)
    (hk4 : 4*k ≤ m) (ht4 : 4*t ≤ m) :
    ((m-2*k+I-t)*(m-t))/(m-k-t)^2 ≤ Real.exp (4*I/m) := by
  have hd : 0 < m-k-t := by linarith
  have hx : 0 ≤ m-t := by linarith
  have hsq : m*(m-t) ≤ 4*(m-k-t)^2 := by
    have h1 : 0 ≤ (m-k-t)*((m-k-t)-m/2) := mul_nonneg hd.le (by linarith)
    have h2 : 0 ≤ m*((m-k-t)-m/2) := mul_nonneg hm.le (by linarith)
    nlinarith
  have hfrac : ((m-2*k+I-t)*(m-t))/(m-k-t)^2 ≤ 1+4*I/m := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).2
    apply (mul_le_mul_iff_left₀ hm).mp
    have hh := mul_le_mul_of_nonneg_right hsq hI
    have he : ((1+4*I/m)*(m-k-t)^2)*m = (m+4*I)*(m-k-t)^2 := by field_simp
    rw [he]
    nlinarith [mul_nonneg (sq_nonneg k) hm.le]
  exact hfrac.trans (by simpa [add_comm] using Real.add_one_le_exp (4*I/m))

/-- Convexity interpolates the overlap factor between zero and full overlap. -/
lemma batch_exp_chord (c I k : ℝ) (hk : 0 < k) (hI : 0 ≤ I) (hIk : I ≤ k) :
    Real.exp (c*I) ≤ 1+(Real.exp (c*k)-1)*(I/k) := by
  have hq0 : 0 ≤ I/k := div_nonneg hI hk.le
  have hq1 : I/k ≤ 1 := (div_le_one hk).2 hIk
  have h := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (c*k))
    (show 0 ≤ 1-I/k by linarith) hq0 (by ring : (1-I/k)+I/k=1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  have he : I/k*(c*k)=c*I := by field_simp <;> ring
  rw [he] at h
  nlinarith

/-- Averaging the convex interpolation uses only the mean normalized overlap. -/
lemma batch_mean_exp_bound {A : Type*} [Fintype A]
    (p : FiniteEntropy.Law A) (I : A → ℝ) (c k : ℝ)
    (hk : 0 < k) (hI : ∀ a, 0 ≤ I a) (hIk : ∀ a, I a ≤ k) :
    (∑ a, p.mass a*Real.exp (c*I a))-1 ≤
      (Real.exp (c*k)-1)*(∑ a, p.mass a*(I a/k)) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
    mul_le_mul_of_nonneg_left (batch_exp_chord c (I a) k hk (hI a) (hIk a)) (p.nonneg a))
  calc
    (∑ a, p.mass a*Real.exp (c*I a))-1 ≤
        (∑ a, p.mass a*(1+(Real.exp (c*k)-1)*(I a/k)))-1 := sub_le_sub_right h 1
    _ = (Real.exp (c*k)-1)*(∑ a, p.mass a*(I a/k)) := by
      simp_rw [mul_add, mul_one]
      rw [Finset.sum_add_distrib, p.total, Finset.mul_sum]
      rw [add_sub_cancel_left]
      apply Finset.sum_congr rfl
      intro a _
      ring

/-- The normalized joint survival product has the exponential overlap bound. -/
lemma batch_joint_product_le_exp (m k τ I : ℕ)
    (hm : 0 < m) (hk4 : 4*k ≤ m) (ht4 : 4*τ ≤ m) :
    (∏ i ∈ Finset.range τ,
      (((m:ℝ)-2*k+I-i)*((m:ℝ)-i))/((m:ℝ)-k-i)^2) ≤
      Real.exp (4*(τ:ℝ)*I/m) := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hkR : 4*(k:ℝ)≤m := by exact_mod_cast hk4
  have htR : 4*(τ:ℝ)≤m := by exact_mod_cast ht4
  have hh : ∀ i ∈ Finset.range τ,
      0 ≤ (((m:ℝ)-2*k+I-i)*((m:ℝ)-i))/((m:ℝ)-k-i)^2 := by
    intro i hi
    have hiR : (i:ℝ)≤τ := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hi))
    apply div_nonneg
    · apply mul_nonneg <;> linarith [show (0:ℝ)≤I by positivity]
    · positivity
  calc
    _ ≤ ∏ i ∈ Finset.range τ, Real.exp (4*(I:ℝ)/m) := by
      apply Finset.prod_le_prod₀ hh
      intro i hi
      apply batch_joint_factor_le_exp (m:ℝ) k i I hmR (by positivity) (by positivity) (by positivity) hkR
      have hiR : (i:ℝ)≤τ := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hi))
      linarith
    _ = Real.exp (4*(τ:ℝ)*I/m) := by
      simp only [Finset.prod_const, Finset.card_range]
      rw [← Real.exp_nat_mul]
      congr 1
      ring

lemma batch_exp_chord_nonneg (c I k : ℝ) (hk : 0 ≤ k) (hI : 0 ≤ I) (hIk : I ≤ k) :
    Real.exp (c*I) ≤ 1+(Real.exp (c*k)-1)*(I/k) := by
  rcases eq_or_lt_of_le hk with h | h
  · have hi : I=0 := by linarith
    simp [← h, hi]
  · exact batch_exp_chord c I k h hI hIk

/-- Direct finite-family version of the overlap interpolation. -/
lemma batch_sum_factor_bound {A : Type*} (F : Finset A) (I Q : A → A → ℝ)
    (c k : ℝ) (hk : 0 ≤ k) (_hc : 0 ≤ c)
    (hI : ∀ a ∈ F, ∀ b ∈ F, 0 ≤ I a b)
    (hIk : ∀ a ∈ F, ∀ b ∈ F, I a b ≤ k)
    (hQ : ∀ a ∈ F, ∀ b ∈ F, Q a b ≤ Real.exp (c*I a b)) :
    (∑ a ∈ F, ∑ b ∈ F, Q a b) ≤ (F.card:ℝ)^2 +
      Real.exp (c*k)*(∑ a ∈ F, ∑ b ∈ F, I a b/k) := by
  have hh : ∀ a ∈ F, ∀ b ∈ F,
      Q a b ≤ 1+Real.exp (c*k)*(I a b/k) := by
    intro a ha b hb
    have h := batch_exp_chord_nonneg c (I a b) k hk (hI a ha b hb) (hIk a ha b hb)
    have hn : 0 ≤ I a b/k := div_nonneg (hI a ha b hb) hk
    exact (hQ a ha b hb).trans (by nlinarith)
  calc
    _ ≤ ∑ a ∈ F, ∑ b ∈ F, (1+Real.exp (c*k)*(I a b/k)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.sum_le_sum (fun b hb => hh a ha b hb)
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [sq]

end LooseHamilton
