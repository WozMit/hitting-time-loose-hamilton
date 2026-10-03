module

public import HittingTimeLooseHamilton.VariableSurvivalScalar

public section

noncomputable section
open scoped BigOperators
namespace LooseHamilton
open CandidateLogSurvival

/-- Exact falling-factorial product for two supports of possibly different sizes. -/
lemma variable_joint_choose_eq_product (m a b τ I : ℕ)
    (ha4 : 4*a ≤ m) (hb4 : 4*b ≤ m) (ht4 : 4*τ ≤ m) (hI : I ≤ a+b) :
    ((m-(a+b-I)).choose τ : ℝ)*(m.choose τ : ℝ)/
      (((m-a).choose τ : ℝ)*((m-b).choose τ : ℝ)) =
    ∏ i ∈ Finset.range τ,
      (((m:ℝ)-a-b+I-i)*((m:ℝ)-i))/(((m:ℝ)-a-i)*((m:ℝ)-b-i)) := by
  calc
    _ = (((m-(a+b-I)).choose τ : ℝ)/((m-a).choose τ : ℝ)) *
        ((m.choose τ : ℝ)/((m-b).choose τ : ℝ)) := by ring
    _ = _ := by
      rw [Hypergeometric.choose_ratio_eq_prod, Hypergeometric.choose_ratio_eq_prod,
        ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have h1 : ((m-(a+b-I)-i:ℕ):ℝ) = (m:ℝ)-a-b+I-i := by
        rw [Nat.cast_sub (by omega : i ≤ m-(a+b-I)),
          Nat.cast_sub (by omega : a+b-I ≤ m), Nat.cast_sub hI, Nat.cast_add]
        ring
      have h2 : ((m-i:ℕ):ℝ) = (m:ℝ)-i := Nat.cast_sub (by omega)
      have h3 : ((m-a-i:ℕ):ℝ) = (m:ℝ)-a-i := by
        rw [Nat.cast_sub (by omega : i ≤ m-a), Nat.cast_sub (by omega : a ≤ m)]
      have h4 : ((m-b-i:ℕ):ℝ) = (m:ℝ)-b-i := by
        rw [Nat.cast_sub (by omega : i ≤ m-b), Nat.cast_sub (by omega : b ≤ m)]
      rw [h1,h2,h3,h4, div_mul_div_comm]

/-- Normalized joint survival is exponentially controlled by the overlap. -/
lemma variable_zeta_joint_le_exp (m a b τ I : ℕ)
    (hm : 0 < m) (ha4 : 4*a ≤ m) (hb4 : 4*b ≤ m) (ht4 : 4*τ ≤ m)
    (hI : I ≤ a+b) :
    zeta m (a+b-I) τ / (zeta m a τ*zeta m b τ) ≤ Real.exp (4*(τ:ℝ)*I/m) := by
  have hc : (m.choose τ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : τ ≤ m)))
  have hca : ((m-a).choose τ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : τ ≤ m-a)))
  have hcb : ((m-b).choose τ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : τ ≤ m-b)))
  have he : zeta m (a+b-I) τ / (zeta m a τ*zeta m b τ) =
      ((m-(a+b-I)).choose τ : ℝ)*(m.choose τ : ℝ)/
        (((m-a).choose τ : ℝ)*((m-b).choose τ : ℝ)) := by
    unfold zeta
    field_simp [hc, hca, hcb] <;> ring
  rw [he, variable_joint_choose_eq_product m a b τ I ha4 hb4 ht4 hI]
  exact variable_joint_product_le_exp m a b τ I hm ha4 hb4 ht4

/-- Convex interpolation gives the linear overlap bound at a common support cap. -/
lemma variable_zeta_joint_le_chord (m k a b τ I : ℕ)
    (hm : 0 < m) (hk : 0 < k) (hk4 : 4*k ≤ m) (ht4 : 4*τ ≤ m)
    (ha : a ≤ k) (hb : b ≤ k) (hI : I ≤ a+b) (hIk : I ≤ k) :
    zeta m (a+b-I) τ ≤ zeta m a τ*zeta m b τ *
      (1+(Real.exp (4*(τ:ℝ)*k/m)-1)*((I:ℝ)/k)) := by
  have hz := mul_pos (zeta_pos (m:=m) (k:=a) (τ:=τ) (by omega))
    (zeta_pos (m:=m) (k:=b) (τ:=τ) (by omega))
  rw [mul_comm (zeta m a τ*zeta m b τ)]
  apply (div_le_iff₀ hz).mp
  have h := variable_zeta_joint_le_exp m a b τ I hm (by omega) (by omega) ht4 hI
  have hc := batch_exp_chord (4*(τ:ℝ)/m) I k
    (by exact_mod_cast hk) (by positivity) (by exact_mod_cast hIk)
  have he : 4*(τ:ℝ)*I/m = (4*(τ:ℝ)/m)*I := by ring
  have he' : (4*(τ:ℝ)/m)*k = 4*(τ:ℝ)*k/m := by ring
  rw [he] at h
  rw [he'] at hc
  simpa only [mul_comm] using h.trans hc

/-- Removing at most `d` sampled edges from a support changes its survival probability
by at most `exp (2*d*τ/m)`. The denominator remains the original sampled universe. -/
lemma variable_zeta_bounds (m k q d τ : ℕ) (hm : 0<m)
    (hk4 : 4*k≤m) (ht4 : 4*τ≤m) (hq : q≤k) (hqd : k-d≤q) :
    zeta m k τ ≤ zeta m q τ ∧
    zeta m q τ ≤ Real.exp (2*(d:ℝ)*τ/m)*zeta m k τ := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hkR : 4*(k:ℝ)≤m := by exact_mod_cast hk4
  have htR : 4*(τ:ℝ)≤m := by exact_mod_cast ht4
  have hqdR : (k:ℝ)-q≤d := by
    have h : (k:ℝ)≤q+d := by exact_mod_cast (show k≤q+d by omega)
    linarith
  have hc : (m.choose τ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : τ ≤ m)))
  have hz := zeta_pos (m:=m) (k:=k) (τ:=τ) (by omega)
  constructor
  · unfold zeta
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.choose_le_choose τ (show m-k≤m-q by omega)
  · apply (div_le_iff₀ hz).mp
    have he : zeta m q τ / zeta m k τ =
        ((m-q).choose τ : ℝ)/((m-k).choose τ : ℝ) := by
      unfold zeta
      field_simp
    rw [he, Hypergeometric.choose_ratio_eq_prod]
    calc
      _ ≤ ∏ i ∈ Finset.range τ, Real.exp (2*(d:ℝ)/m) := by
        apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hiR : (i:ℝ)≤τ := by exact_mod_cast (Nat.le_of_lt hi')
        have hden : 0 < (m:ℝ)-k-i := by linarith
        rw [Nat.cast_sub (by omega : i≤m-q), Nat.cast_sub (by omega : q≤m),
          Nat.cast_sub (by omega : i≤m-k), Nat.cast_sub (by omega : k≤m)]
        have hf : ((m:ℝ)-q-i)/((m:ℝ)-k-i) ≤ 1+2*(d:ℝ)/m := by
          apply (div_le_iff₀ hden).2
          apply (mul_le_mul_iff_left₀ hmR).mp
          have hd := mul_nonneg (show (0:ℝ)≤d by positivity)
            (show 0≤2*((m:ℝ)-k-i)-m by linarith)
          have he : ((1+2*(d:ℝ)/m)*((m:ℝ)-k-i))*m =
            (m+2*(d:ℝ))*((m:ℝ)-k-i) := by field_simp
          rw [he]
          nlinarith [mul_le_mul_of_nonneg_right hqdR hmR.le]
        exact hf.trans (by simpa [add_comm] using Real.add_one_le_exp (2*(d:ℝ)/m))
      _ = _ := by
        simp only [Finset.prod_const, Finset.card_range]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
end LooseHamilton
