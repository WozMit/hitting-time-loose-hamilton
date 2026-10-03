module

public import HittingTimeLooseHamilton.ExceptionalSetAsymptotics

public section

noncomputable section
namespace LooseHamilton
open Filter

lemma exp_neg_log_nat (n : ℕ) (hn : 0 < n) (p : ℝ) :
    Real.exp (-p*Real.log (n:ℝ)) = (n:ℝ)^(-p) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn)]
  congr 1
  ring

/-- A polynomial number of tests is dominated by the pair-incidence exponential tail. -/
theorem eventually_path_pair_exponent (A : ℝ) {c : ℝ} (hc : 0<c) (p : ℕ) :
    ∀ᶠ n : ℕ in atTop, 0<n ∧ 1≤Real.log (n:ℝ) ∧
      ∀ μ k : ℝ, (99/100:ℝ)*Real.log n ≤ μ →
        c*μ*(Real.log n)^(-1/4:ℝ) ≤ k →
        Real.exp (A*μ/(n:ℝ)^(1/2:ℝ)-k*Real.log n/2) ≤
          (n:ℝ)^(-((p:ℝ)+1)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogpow : Tendsto (fun n : ℕ => (Real.log (n:ℝ))^(3/4:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).comp hlog
  have hsqrt : Tendsto (fun n : ℕ => (n:ℝ)^(1/2:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ => A/(n:ℝ)^(1/2:ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hsqrt
  filter_upwards [eventually_ge_atTop (1:ℕ),hlog.eventually (eventually_ge_atTop 1),
    hlogpow.eventually (eventually_ge_atTop (max 1 (400*((p:ℝ)+1)/(99*c)))),
    (tendsto_order.mp hsmall).2 (c/4) (by positivity)] with n hn hl hp ha
  have hn0 : 0<n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hl0 : 0<Real.log (n:ℝ) := by linarith
  have hp1 : 1 ≤ (Real.log (n:ℝ))^(3/4:ℝ) := (le_max_left _ _).trans hp
  have hp2 : 400*((p:ℝ)+1)/(99*c) ≤ (Real.log (n:ℝ))^(3/4:ℝ) := (le_max_right _ _).trans hp
  have hpc := (div_le_iff₀ (by positivity : 0<99*c)).mp hp2
  refine ⟨hn0,hl,?_⟩
  intro μ k hμ hk
  have hμ0 : 0≤μ := by nlinarith
  have he : (Real.log (n:ℝ))^(-1/4:ℝ)*Real.log n = (Real.log (n:ℝ))^(3/4:ℝ) := by
    calc
      _ = (Real.log (n:ℝ))^(-1/4:ℝ)*(Real.log n)^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hl0]; norm_num
  have hkm := mul_le_mul_of_nonneg_right hk hl0.le
  rw [mul_assoc,he] at hkm
  have hma := mul_le_mul_of_nonneg_right ha.le hμ0
  have hbase : A*μ/(n:ℝ)^(1/2:ℝ) ≤ c*μ/4 := by convert hma using 1 <;> ring
  have hprod := mul_le_mul_of_nonneg_right hμ (show 0≤c*(Real.log (n:ℝ))^(3/4:ℝ) by positivity)
  have hscale := mul_le_mul_of_nonneg_right hpc hl0.le
  rw [← exp_neg_log_nat n hn0 ((p:ℝ)+1)]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hμ0 (sub_nonneg.mpr hp1)]

/-- For a large fixed threshold factor, degree upper tails beat any prescribed polynomial. -/
theorem path_degree_exponent (A : ℝ) (p : ℕ) {n : ℕ} {μ k C : ℝ}
    (hn : 0<n) (hl : 0≤Real.log (n:ℝ))
    (hμ : (99/100:ℝ)*Real.log n ≤ μ)
    (hC : 2*A+100*((p:ℝ)+1)/99 ≤ C*Real.log 2)
    (hk : C*μ ≤ k) :
    Real.exp (2*A*μ-k*Real.log 2) ≤ (n:ℝ)^(-((p:ℝ)+1)) := by
  have hμ0 : 0≤μ := by nlinarith
  have hc := mul_le_mul_of_nonneg_right hC hμ0
  have hk' := mul_le_mul_of_nonneg_right hk (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
  have hp : 0≤(p:ℝ)+1 := by positivity
  have hm := mul_le_mul_of_nonneg_right hμ hp
  rw [←exp_neg_log_nat n hn ((p:ℝ)+1)]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Summing an n^(-(p+1)) tail over n^p tests still gives a vanishing bound. -/
theorem path_polynomial_error_tendsto_zero (p : ℕ) :
    Tendsto (fun n : ℕ => (n:ℝ)^p*(n:ℝ)^(-((p:ℝ)+1))) atTop (nhds 0) := by
  have h := tendsto_nat_rpow_ratio (by norm_num : (-1:ℝ)<0)
  simp only [Real.rpow_zero,div_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [←Real.rpow_natCast,←Real.rpow_add hn0]
  congr 1
  ring
/-- The lower tail after sufficiently many extension edges also beats any polynomial. -/
lemma path_degree_lower_exponent (p : ℕ) {n : ℕ} {μ lam k : ℝ}
    (hn : 0<n) (hμ : 16*((p:ℝ)+1)*Real.log (n:ℝ) ≤ μ)
    (hlam : μ/4≤lam) (hk : k*Real.log 2≤μ/16) :
    Real.exp (-lam/2+k*Real.log 2) ≤ (n:ℝ)^(-((p:ℝ)+1)) := by
  rw [←exp_neg_log_nat n hn ((p:ℝ)+1)]
  apply Real.exp_le_exp.mpr
  linarith

/-- A bounded terminal codegree is absorbed by any fixed positive fraction of the path threshold. -/
theorem eventually_pair_threshold_margin {c : ℝ} (hc : 0<c) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ μ : ℝ, (99/100:ℝ)*Real.log (n:ℝ) ≤ μ →
      B ≤ c*μ*(Real.log (n:ℝ))^(-1/4:ℝ) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (Real.log (n:ℝ))^(3/4:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).comp hlog
  filter_upwards [hlog.eventually (eventually_ge_atTop 1),
    hpow.eventually (eventually_ge_atTop (100*B/(99*c)))] with n hl hp
  intro μ hμ
  have hl0 : 0<Real.log (n:ℝ) := by linarith
  have he : Real.log (n:ℝ)*(Real.log (n:ℝ))^(-1/4:ℝ) = (Real.log (n:ℝ))^(3/4:ℝ) := by
    calc
      _ = (Real.log (n:ℝ))^(1:ℝ)*(Real.log (n:ℝ))^(-1/4:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hl0]; norm_num
  have hprod := mul_le_mul_of_nonneg_right hμ (Real.rpow_nonneg hl0.le (-1/4:ℝ))
  rw [mul_assoc,he] at hprod
  have hpc := (div_le_iff₀ (by positivity : 0<99*c)).mp hp
  nlinarith [mul_le_mul_of_nonneg_left hprod hc.le]

lemma terminal_degree_absorption {n : ℕ} {C μ d : ℝ}
    (hC : 0≤C) (hμ : (99/100:ℝ)*Real.log (n:ℝ) ≤ μ)
    (hl : 0≤Real.log (n:ℝ)) (hd : d≤C*Real.log n) : d≤2*C*μ := by
  nlinarith [mul_le_mul_of_nonneg_left hμ hC,mul_nonneg hC hl]
end LooseHamilton
