module

public import HittingTimeLooseHamilton.HypergeometricAvoidanceLower
public import Mathlib.Tactic

public section

noncomputable section
namespace LooseHamilton.CandidateLogSurvival

/-- The exact probability that a uniform batch avoids a fixed k-set. -/
@[expose] def zeta (m k τ : ℕ) : ℝ := ((m-k).choose τ : ℝ)/(m.choose τ : ℝ)

lemma log_zeta_bounds {m k τ : ℕ} (hm : 0<m) (h : k+τ<m) :
    -((k:ℝ)*τ/(m-k-τ:ℕ)) ≤ Real.log (zeta m k τ) ∧
    Real.log (zeta m k τ) ≤ -((k:ℝ)*τ/m) := by
  have hlo := Hypergeometric.avoidance_ratio_ge_exp (N:=m) (m:=τ) (t:=k) (by omega)
  have hhi := Hypergeometric.avoidance_ratio_le_exp (N:=m) (m:=τ) (t:=k)
    (by omega) hm (by omega)
  have hz : 0 < zeta m k τ := (Real.exp_pos _).trans_le hlo
  constructor
  · have hh := Real.log_le_log (Real.exp_pos _) hlo
    rw [Real.log_exp] at hh
    simpa only [zeta, show m-τ-k=m-k-τ by omega] using hh
  · have hh := Real.log_le_log hz hhi
    rwa [Real.log_exp] at hh

lemma zeta_pos {m k τ : ℕ} (h : k+τ<m) : 0 < zeta m k τ :=
  (Real.exp_pos _).trans_le
    (Hypergeometric.avoidance_ratio_ge_exp (N:=m) (m:=τ) (t:=k) (by omega))

lemma reciprocal_error {a b c : ℝ} (ha : 0<a) (hb : 0≤b)
    (hc : 0≤c) (hhalf : 2*b≤a) :
    c/(a-b)-c/a ≤ 2*c*b/a^2 := by
  have hd : 0<a-b := by linarith
  have hid : c/(a-b)-c/a = c*b/((a-b)*a) := by
    field_simp <;> ring
  rw [hid]
  apply (div_le_div_iff₀ (mul_pos hd ha) (sq_pos_of_pos ha)).mpr
  nlinarith [mul_nonneg (mul_nonneg hc hb) (show 0≤a*(a-2*b) by exact mul_nonneg ha.le (by linarith))]

/-- Finite, uniform version of the logarithmic hypergeometric expansion. -/
theorem log_zeta_error {m k τ : ℕ} (hm : 0<m) (h : 2*(k+τ)≤m) :
    |Real.log (zeta m k τ)+(k:ℝ)*τ/m| ≤
      2*(k:ℝ)*τ*(k+τ)/(m:ℝ)^2 := by
  have hstrict : k+τ<m := by omega
  obtain ⟨hl,hu⟩ := log_zeta_bounds hm hstrict
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hc : ((m-k-τ:ℕ):ℝ)=(m:ℝ)-((k:ℝ)+τ) := by
    rw [Nat.cast_sub (by omega : τ≤m-k), Nat.cast_sub (by omega : k≤m)]
    ring
  rw [hc] at hl
  have he := reciprocal_error hmR (show 0≤(k:ℝ)+τ by positivity)
    (show 0≤(k:ℝ)*τ by positivity) (by exact_mod_cast h)
  rw [abs_le]
  constructor
  · ring_nf at hl hu he ⊢
    linarith
  · have hn : 0≤2*(k:ℝ)*τ*(k+τ)/(m:ℝ)^2 := by positivity
    linarith

/-- A finite logarithmic expansion of the surviving mean-degree ratio. -/
theorem log_mean_ratio_error {m k τ : ℕ} (hm : 0<m) (h : 2*τ≤m) :
    |(k:ℝ)*Real.log (((m:ℝ)-τ)/m)+(k:ℝ)*τ/m| ≤
      2*(k:ℝ)*τ^2/(m:ℝ)^2 := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hhalf : 2*(τ:ℝ)≤m := by exact_mod_cast h
  have hd : 0<(m:ℝ)-τ := by linarith
  have hq : 0<((m:ℝ)-τ)/m := div_pos hd hmR
  have hl := Real.one_sub_inv_le_log_of_pos hq
  have hu := Real.log_le_sub_one_of_pos hq
  have heq : 1-(((m:ℝ)-τ)/m)⁻¹=-(τ:ℝ)/((m:ℝ)-τ) := by field_simp <;> ring
  have heq' : ((m:ℝ)-τ)/m-1=-(τ:ℝ)/m := by field_simp <;> ring
  rw [heq] at hl
  rw [heq'] at hu
  have hkl := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg k : (0:ℝ)≤k)
  have hku := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg k : (0:ℝ)≤k)
  have he := reciprocal_error hmR (Nat.cast_nonneg τ)
    (show 0≤(k:ℝ)*τ by positivity) hhalf
  rw [abs_le]
  constructor
  · ring_nf at hkl hku he ⊢
    linarith
  · have hn : 0≤2*(k:ℝ)*τ^2/(m:ℝ)^2 := by positivity
    ring_nf at hku hn ⊢
    nlinarith
end LooseHamilton.CandidateLogSurvival
