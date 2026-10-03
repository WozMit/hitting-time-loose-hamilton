module

public import HittingTimeLooseHamilton.ExceptionalSetAsymptotics
public import HittingTimeLooseHamilton.WindowMeanAsymptotics

public section

/-! Uniform scalar estimates for the terminal feasibility bound. -/
noncomputable section
namespace LooseHamilton
open Filter

/-- The prescribed density window and bounded offsets leave a fixed tail margin. -/
theorem eventually_feasibility_parameters (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n:ℝ) ∧
      (∀ μ : ℝ, |μ-Real.log n| ≤ 3*Real.log (Real.log n) →
        (99/100:ℝ)*Real.log n ≤ μ) ∧
      (∀ ell : ℕ, |(ell:ℝ)-Nat.floor (epsilon*Real.log n)| ≤ B →
        (ell:ℝ) ≤ (11/1000:ℝ)*Real.log n) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ => Real.log (Real.log n)/Real.log n)
      atTop (nhds 0) := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  filter_upwards [hlog.eventually (eventually_ge_atTop (max 1 (1000*B))),
    (tendsto_order.mp hratio).2 (1/300) (by norm_num)] with n hn hr
  have h1 : 1 ≤ Real.log (n:ℝ) := (le_max_left _ _).trans hn
  have hB : 1000*B ≤ Real.log (n:ℝ) := (le_max_right _ _).trans hn
  have hl : 0 < Real.log (n:ℝ) := by linarith
  have hh := (div_lt_iff₀ hl).mp hr
  refine ⟨h1,?_,?_⟩
  · intro μ hμ
    have := (abs_le.mp hμ).1
    linarith
  · intro ell hell
    have hf : (Nat.floor (epsilon*Real.log (n:ℝ)) : ℝ) ≤ epsilon*Real.log n :=
      Nat.floor_le (by unfold epsilon; positivity)
    have ho := (abs_le.mp hell).2
    unfold epsilon at hf ho
    linarith

lemma feasibility_exp_subtract {a b t : ℝ}
    (ha : a ≤ t/2) (hb : t ≤ b) (ht : 2*Real.log 2 ≤ t) :
    Real.exp (-t) ≤ Real.exp (-a)-Real.exp (-b) := by
  have h1 : Real.exp (-t) * 2 ≤ Real.exp (-a) := by
    calc
      _ = Real.exp (-t+Real.log 2) := by rw [Real.exp_add,Real.exp_log (by norm_num)]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-b) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- The product lower bound dominates the overflow loss uniformly over admissible M. -/
theorem eventually_feasibility_scales {r : ℕ} (hr : 1 ≤ r) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ (n:ℝ)^(-91/100:ℝ) ≤ 1/2 ∧
      ∀ M : ℕ, 1 ≤ Real.log (n:ℝ) →
        (99/100:ℝ)*Real.log n ≤ (r:ℝ)*M/n →
        Real.exp (-(n:ℝ)^(1/10:ℝ)) ≤
          Real.exp (-2*(n:ℝ)^(-91/100:ℝ)*n) - Real.exp (-(M:ℝ)/1010000) := by
  have hr0 : (0:ℝ)<r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hu : Tendsto (fun n : ℕ => (n:ℝ)^(-91/100:ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<91/100)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hratio := tendsto_nat_rpow_ratio (by norm_num : (9/100:ℝ)<1/10)
  have hlarge : Tendsto (fun n : ℕ => (n:ℝ)^(1/10:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).comp tendsto_natCast_atTop_atTop
  have hlinear := tendsto_nat_rpow_ratio (by norm_num : (1/10:ℝ)<1)
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_order.mp hu).2 (1/2) (by norm_num),
    (tendsto_order.mp hratio).2 (1/4) (by norm_num),
    hlarge.eventually (eventually_ge_atTop (2*Real.log 2)),
    (tendsto_order.mp hlinear).2 (1/(2*(r:ℝ)*1010000)) (by positivity)]
    with n hn hu hrati ht hlin
  refine ⟨hn,hu.le,?_⟩
  intro M hl hM
  have hn0 : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have ht0 : 0 < (n:ℝ)^(1/10:ℝ) := Real.rpow_pos_of_pos hn0 _
  have hid : (n:ℝ)^(-91/100:ℝ)*(n:ℝ) = (n:ℝ)^(9/100:ℝ) := by
    calc
      _ = (n:ℝ)^(-91/100:ℝ)*(n:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn0]; norm_num
  have ha : 2*(n:ℝ)^(-91/100:ℝ)*n ≤ (n:ℝ)^(1/10:ℝ)/2 := by
    have := (div_lt_iff₀ ht0).mp hrati
    rw [mul_assoc,hid]
    linarith
  have hb : (n:ℝ)^(1/10:ℝ) ≤ (M:ℝ)/1010000 := by
    rw [Real.rpow_one] at hlin
    have hμ := (le_div_iff₀ hn0).mp hM
    have hc : 0 < 2*(r:ℝ)*1010000 := by positivity
    have hscale := (div_lt_div_iff₀ hn0 hc).mp hlin
    have hlog : (n:ℝ)/2 ≤ (r:ℝ)*M := by nlinarith only [hμ,hl,hn0]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<1010000)).mpr
    apply (mul_le_mul_iff_right₀ hr0).mp
    nlinarith only [hscale,hlog]
  simpa only [neg_mul,neg_div] using feasibility_exp_subtract ha hb ht
end LooseHamilton
