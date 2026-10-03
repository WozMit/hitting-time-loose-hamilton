module

public import HittingTimeLooseHamilton.FrameScales
public import HittingTimeLooseHamilton.FrameSurvivalRates
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section

/-! Uniform scalar estimates for the frame survival concentration argument. -/
noncomputable section
namespace LooseHamilton.FrameScales
open Filter Topology

lemma exp_four_nu (N : ℕ) (hL : 0 < L2 N) :
    Real.exp (4 * nu N) = (L2 N) ^ (1 / 25 : ℝ) := by
  rw [Real.rpow_def_of_pos hL]
  congr 1
  dsimp [nu, L3]
  ring

lemma exp_four_nu_div_L2 (N : ℕ) (hL : 0 < L2 N) :
    Real.exp (4 * nu N) / L2 N = (L2 N) ^ (-24 / 25 : ℝ) := by
  rw [exp_four_nu N hL]
  have he : (-24 / 25 : ℝ) = 1 / 25 - 1 := by norm_num
  rw [he, Real.rpow_sub hL, Real.rpow_one]

/-- The raw-host density lower bound controls its logarithm uniformly in the host. -/
theorem eventually_log_density_lower :
    ∀ᶠ N in atTop, ∀ μ : ℝ, L1 N / 2 ≤ μ →
      0 < Real.log μ ∧ L2 N / 2 ≤ Real.log μ := by
  filter_upwards [L1_tendsto.eventually (eventually_gt_atTop 0),
    L2_tendsto.eventually (eventually_gt_atTop (2 * Real.log 2 + 1))] with N h1 h2 μ hμ
  have hp : 0 < L1 N / 2 := by positivity
  have hm := Real.strictMonoOn_log.monotoneOn hp (hp.trans_le hμ) hμ
  rw [Real.log_div (ne_of_gt h1) (by norm_num)] at hm
  have hl : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  change L2 N - Real.log 2 ≤ Real.log μ at hm
  constructor <;> linarith

/-- The exact exponent 24/25 comes from exp(4ν)=L₂^(1/25). -/
theorem eventually_concentration_power :
    ∀ᶠ N in atTop, ∀ μ : ℝ, L1 N / 2 ≤ μ →
      Real.exp (4 * nu N) / Real.log μ ≤ 2 * (L2 N) ^ (-24 / 25 : ℝ) := by
  filter_upwards [eventually_log_density_lower, eventual_range] with N hN hR μ hμ
  obtain ⟨hm, hlog⟩ := hN μ hμ
  rw [← exp_four_nu_div_L2 N hR.2.1]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hm hR.2.1).mpr
  nlinarith [mul_nonneg (Real.exp_pos (4 * nu N)).le
    (show 0 ≤ 2 * Real.log μ - L2 N by linarith)]

/-- A batch exponent no larger than 4ν has the same uniform power bound. -/
theorem eventually_concentration_power_of_exponent :
    ∀ᶠ N in atTop, ∀ μ x : ℝ, L1 N / 2 ≤ μ → x ≤ 4 * nu N →
      Real.exp x / Real.log μ ≤ 2 * (L2 N) ^ (-24 / 25 : ℝ) := by
  filter_upwards [eventually_concentration_power, eventually_log_density_lower] with N hN hlog μ x hμ hx
  exact (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hx)
    (hlog μ hμ).1.le).trans (hN μ hμ)

/-- Boundary distortion is uniformly linear in ν/N; the squared distortion
factor appearing in the variance is eventually at most two. -/
theorem eventually_boundary_distortion (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ N in atTop, ∀ y : ℝ, 0 ≤ y → y ≤ A * (nu N / (N : ℝ)) →
      |Real.exp (2*y) - 1| ≤ 4*A*(nu N / (N : ℝ)) ∧
      Real.exp (4*y) ≤ 2 := by
  have ht := nu_div_vertices_tendsto_zero.const_mul (8*A)
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)), eventual_range]
    with N hN hR y hy hyA
  have hq : 0 ≤ nu N / (N : ℝ) := div_nonneg hR.2.2.2.2.2.1.le (Nat.cast_nonneg _)
  have h2 : |2*y| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; nlinarith
  have h4 : |4*y| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; nlinarith
  have he2 := Real.abs_exp_sub_one_le h2
  have he4 := Real.abs_exp_sub_one_le h4
  rw [abs_of_nonneg (by positivity : (0:ℝ)≤2*y)] at he2
  rw [abs_of_nonneg (by positivity : (0:ℝ)≤4*y)] at he4
  constructor
  · nlinarith
  · have hh := le_abs_self (Real.exp (4*y)-1)
    nlinarith

/-- Scalar variance envelope. All constants and the eventual threshold are
chosen before the density, batch exponents and relative-error threshold. -/
theorem eventually_variance_envelope (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ N in atTop, ∀ μ x y h : ℝ,
      L1 N / 2 ≤ μ → x ≤ nu N →
      0 ≤ y → y ≤ A * (nu N / (N : ℝ)) → 0 < h →
      Real.exp (4*y) * (Real.exp (4*x)-1) * (B / Real.log μ) / h^2 ≤
        (4*B) * (L2 N)^(-24/25:ℝ) / h^2 := by
  filter_upwards [eventually_boundary_distortion A hA,
    eventually_concentration_power, eventually_log_density_lower] with N hb hp hl μ x y h hμ hx hy hyA hh
  have hlog := (hl μ hμ).1
  have he := (hb y hy hyA).2
  have hexp : Real.exp (4*x)-1 ≤ Real.exp (4*nu N) := by
    have := Real.exp_le_exp.mpr (show 4*x ≤ 4*nu N by linarith)
    linarith
  have heprod : Real.exp (4*y)*(Real.exp (4*x)-1) ≤ 2*Real.exp (4*nu N) := by
    calc
      _ ≤ Real.exp (4*y)*Real.exp (4*nu N) :=
        mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
  apply div_le_div_of_nonneg_right _ (sq_nonneg h)
  have hmain := mul_le_mul_of_nonneg_right heprod (div_nonneg hB hlog.le)
  have hpower := mul_le_mul_of_nonneg_left (hp μ hμ) (show 0 ≤ 2*B by positivity)
  calc
    _ ≤ (2*Real.exp (4*nu N))*(B / Real.log μ) := hmain
    _ = (2*B)*(Real.exp (4*nu N)/Real.log μ) := by ring
    _ ≤ (2*B)*(2*(L2 N)^(-24/25:ℝ)) := hpower
    _ = _ := by ring

/-- A version ready to apply to a survival-family variance bound, with the
batch and overlap parameters left universally quantified. -/
theorem eventually_survival_variance (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ N in atTop, ∀ μ m k τ d O h : ℝ,
      L1 N / 2 ≤ μ → 0 < m → 0 < k → 0 ≤ τ → 0 ≤ d →
      τ*k/m ≤ nu N → d*τ/m ≤ A*(nu N/(N:ℝ)) →
      O/k ≤ B/Real.log μ → 0 < h →
      Real.exp (4*d*τ/m)*(Real.exp (4*τ*k/m)-1)*(O/k)/h^2 ≤
        (4*B)*(L2 N)^(-24/25:ℝ)/h^2 := by
  filter_upwards [eventually_variance_envelope A B hA hB] with N hN μ m k τ d O h hμ hm hk hτ hd hx hy hO hh
  have hy0 : 0 ≤ d*τ/m := by positivity
  have hfactor : 0 ≤ Real.exp (4*(τ*k/m))-1 := by
    have hz : 0 ≤ 4*(τ*k/m) := by positivity
    have := Real.exp_le_exp.mpr hz
    rw [Real.exp_zero] at this
    linarith
  have hcompare := mul_le_mul_of_nonneg_left hO
    (mul_nonneg (Real.exp_pos (4*(d*τ/m))).le hfactor)
  have hden := div_le_div_of_nonneg_right hcompare (sq_nonneg h)
  have hbound := hN μ (τ*k/m) (d*τ/m) h hμ hx hy0 hy hh
  convert hden.trans hbound using 1 <;> congr 2 <;> congr 1 <;> ring

/-- The lower comparison between k and N converts the coarse overlap count
into the normalized overlap required by the variance estimate. -/
lemma normalized_overlap_bound (N k O μ a K : ℝ)
    (hk : 0 < k) (hlog : 0 < Real.log μ) (hK : 0 ≤ K)
    (hNk : N ≤ a*k) (hO : O ≤ K*N/Real.log μ) :
    O/k ≤ (a*K)/Real.log μ := by
  apply (div_le_iff₀ hk).2
  apply (mul_le_mul_iff_left₀ hlog).mp
  have hO' := (le_div_iff₀ hlog).mp hO
  have hN' := mul_le_mul_of_nonneg_left hNk hK
  field_simp [ne_of_gt hlog]
  nlinarith

/-- The boundary error is negligible even on the prescribed shrinking alpha scale. -/
theorem nu_div_vertices_div_alpha_tendsto_zero :
    Tendsto (fun N => (nu N / (N:ℝ)) / alpha N) atTop (nhds 0) := by
  have ht := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  simp only [Real.rpow_two, Real.rpow_one] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventual_range] with N hN
    exact div_nonneg (div_nonneg hN.2.2.2.2.2.1.le (Nat.cast_nonneg _)) hN.2.2.2.1.le
  · filter_upwards [eventual_range] with N hN
    have h21 : L2 N ≤ L1 N := by
      have := Real.log_le_sub_one_of_pos hN.1
      change Real.log (L1 N) ≤ L1 N
      linarith
    have h32 : L3 N ≤ L2 N := by
      have := Real.log_le_sub_one_of_pos hN.2.1
      change Real.log (L2 N) ≤ L2 N
      linarith
    have hν : nu N ≤ L1 N := by dsimp [nu]; linarith [hN.2.2.1]
    have hi : 1 / alpha N ≤ L3 N := by
      rw [alpha, one_div, ← Real.rpow_neg (by linarith : 0 ≤ L3 N)]
      norm_num
      exact (Real.rpow_le_rpow_of_exponent_le hN.2.2.1.le (by norm_num : (1/100:ℝ)≤1)).trans_eq (Real.rpow_one _)
    have hmul := mul_le_mul hν (hi.trans (h32.trans h21))
      (div_nonneg (by norm_num) hN.2.2.2.1.le) hN.1.le
    have hd := div_le_div_of_nonneg_right hmul (Nat.cast_nonneg N : (0:ℝ)≤N)
    change nu N / (N:ℝ) / alpha N ≤ L1 N ^ 2 / (N:ℝ)
    convert hd using 1 <;> ring

/-- Uniform boundary bias on the small relative-error scale used in the
candidate transfer step. -/
theorem eventually_boundary_bias_alpha (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ N in atTop, ∀ y : ℝ, 0 ≤ y → y ≤ A*(nu N/(N:ℝ)) →
      Real.exp (2*y)-1 ≤ (alpha N/100000)/4 ∧ Real.exp (2*y) ≤ 2 := by
  have ht := nu_div_vertices_div_alpha_tendsto_zero.const_mul (1600000*A)
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    eventually_boundary_distortion A hA, eventual_range] with N hN hb hR y hy hyA
  have hb' := hb y hy hyA
  have ha := hR.2.2.2.1
  have ht' : 1600000*A*(nu N/(N:ℝ)) < alpha N := by
    have hh : (1600000*A*(nu N/(N:ℝ))) / alpha N < 1 := by
      convert hN using 1 <;> ring
    simpa only [one_mul] using (div_lt_iff₀ ha).mp hh
  constructor
  · have := le_abs_self (Real.exp (2*y)-1)
    nlinarith [hb'.1]
  · exact (Real.exp_le_exp.mpr (by linarith : 2*y≤4*y)).trans hb'.2

end LooseHamilton.FrameScales
