module

public import HittingTimeLooseHamilton.FramePreservationScales
public import HittingTimeLooseHamilton.CoreParameterBounds

public section

noncomputable section
namespace LooseHamilton.BootstrapPrivateMobilityScales
open Filter Topology FrameScales

/-- The static exclusion envelope is negligible even relative to alpha. -/
theorem exclusion_ratio_tendsto_zero (r : ℕ) :
    Tendsto (fun N : ℕ => (2*(N:ℝ)^(1/10:ℝ)+(r:ℝ)+1) / (N:ℝ) / alpha N)
      atTop (nhds 0) := by
  have hx : Tendsto (fun N : ℕ => (N:ℝ)^(1/10:ℝ)*Real.log N/N) atTop (nhds 0) := by
    have hh := tendsto_nat_rpow_mul_log_pow (by norm_num : (1/10:ℝ)-1<0) 1
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    have hp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    rw [Real.rpow_sub hp, Real.rpow_one, pow_one]
    ring
  have hy : Tendsto (fun N : ℕ => Real.log (N:ℝ)/(N:ℝ)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun N : ℕ => (2*(N:ℝ)^(1/10:ℝ)+(r:ℝ)+1)*Real.log N/N)
      atTop (nhds 0) := by
    convert (hx.const_mul 2).add (hy.const_mul ((r:ℝ)+1)) using 1 <;> try simp
    ext N; ring
  apply squeeze_zero' _ _ hz
  · filter_upwards [eventual_range] with N hN
    exact div_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg _)) hN.2.2.2.1.le
  · filter_upwards [eventual_range] with N hN
    have h21 := Real.log_le_sub_one_of_pos hN.1
    have h32 := Real.log_le_sub_one_of_pos hN.2.1
    have hi : 1/alpha N ≤ Real.log N := by
      apply (inv_alpha_le_L3 N hN.2.2.1).trans
      change L2 N ≤ L1 N-1 at h21
      change L3 N ≤ L2 N-1 at h32
      change L3 N ≤ L1 N
      linarith
    have hh := mul_le_mul_of_nonneg_left hi
      (show 0≤(2*(N:ℝ)^(1/10:ℝ)+(r:ℝ)+1)/(N:ℝ) by positivity)
    convert hh using 1 <;> ring

/-- Square-root alpha is negligible relative to rho = alpha^(1/8). -/
theorem sqrt_alpha_div_rho_tendsto_zero :
    Tendsto (fun N => Real.sqrt (alpha N)/rho N) atTop (nhds 0) := by
  have hh := alpha_tendsto_zero.rpow_const (p := (3/8:ℝ)) (Or.inr (by norm_num))
  simp only [Real.zero_rpow (by norm_num : (3/8:ℝ)≠0)] at hh
  apply hh.congr'
  filter_upwards [eventual_range] with N hN
  rw [Real.sqrt_eq_rpow, rho, ←Real.rpow_sub hN.2.2.2.1]
  norm_num



/-- Uniform in the matching-size parameter; no threshold depends on s. -/
theorem eventually_exclusion_bound (r : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ s : ℕ, (s:ℝ)≤(N:ℝ)^(1/10:ℝ) →
      ((2*s+r+1:ℕ):ℝ) ≤ ε*alpha N*(N:ℝ) := by
  filter_upwards [(exclusion_ratio_tendsto_zero r).eventually (gt_mem_nhds hε),
    eventual_range, eventually_ge_atTop (1:ℕ)] with N hh hR hN s hs
  have hp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have h1 := (div_lt_iff₀ hR.2.2.2.1).mp hh
  have h2 := (div_lt_iff₀ hp).mp h1
  have hl : ((2*s+r+1:ℕ):ℝ) ≤ 2*(N:ℝ)^(1/10:ℝ)+(r:ℝ)+1 := by
    push_cast
    linarith
  exact hl.trans h2.le

/-- Simultaneous density and exceptional-target estimates for the paper's scales. -/
theorem eventually_private_mobility_bounds (r : ℕ) (hr : 3≤r) :
    ∀ᶠ N : ℕ in atTop, 8*r≤N ∧ 0<alpha N ∧ alpha N≤1/2 ∧ 0<rho N ∧
      ∀ s : ℕ, (s:ℝ)≤(N:ℝ)^(1/10:ℝ) →
        (2:ℝ)^(r-1)*((r-1).factorial:ℝ)*Real.sqrt (((r-2:ℕ):ℝ)*alpha N) +
          ((2*s+r+1:ℕ):ℝ)*((r-1:ℕ):ℝ)/((N-1:ℕ):ℝ) < rho N ∧
        Real.sqrt (((r-2:ℕ):ℝ)*alpha N)*(N:ℝ)+((2*s+r+1:ℕ):ℝ) ≤
          (Real.sqrt ((r-2:ℕ):ℝ)+1)*Real.sqrt (alpha N)*(N:ℝ) := by
  let K : ℝ := (2:ℝ)^(r-1)*((r-1).factorial:ℝ)*Real.sqrt ((r-2:ℕ):ℝ)
  have ht := sqrt_alpha_div_rho_tendsto_zero.const_mul K
  simp only [mul_zero] at ht
  have hrp : (0:ℝ)<((r-1:ℕ):ℝ) := by exact_mod_cast (show 0<r-1 by omega)
  have he : (0:ℝ)<1/(4*((r-1:ℕ):ℝ)) := by positivity
  filter_upwards [eventually_ge_atTop (8*r), eventual_range,
    alpha_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    eventually_exclusion_bound r he,
    eventually_exclusion_bound r (by norm_num : (0:ℝ)<1)] with N hN hR ha hk hexc hexc1
  have hap := hR.2.2.2.1
  have hrho := hR.2.2.2.2.2.2.1
  refine ⟨hN,hap,ha.le,hrho,?_⟩
  intro s hs
  have h2N : 2≤N := by omega
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hNm : (0:ℝ)<((N-1:ℕ):ℝ) := by exact_mod_cast (show 0<N-1 by omega)
  have hhalf : (N:ℝ)≤2*((N-1:ℕ):ℝ) := by exact_mod_cast (show N≤2*(N-1) by omega)
  have harho : alpha N≤rho N := by
    change alpha N ≤ (alpha N)^(1/8:ℝ)
    calc
      _ = (alpha N)^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge' hap.le hR.2.2.2.2.1.le (by norm_num) (by norm_num)
  have hasqrt : alpha N≤Real.sqrt (alpha N) := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ = (alpha N)^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge' hap.le hR.2.2.2.2.1.le (by norm_num) (by norm_num)
  have hsqr : Real.sqrt (((r-2:ℕ):ℝ)*alpha N) = Real.sqrt ((r-2:ℕ):ℝ)*Real.sqrt (alpha N) :=
    Real.sqrt_mul (Nat.cast_nonneg _) _
  have hfirst : (2:ℝ)^(r-1)*((r-1).factorial:ℝ)*Real.sqrt (((r-2:ℕ):ℝ)*alpha N)<rho N/2 := by
    have hh := (div_lt_iff₀ hrho).mp (show K*Real.sqrt (alpha N)/rho N<1/2 by convert hk using 1 <;> ring)
    rw [hsqr]
    dsimp [K] at hh
    nlinarith
  have he1 := hexc s hs
  have he2 : ((2*s+r+1:ℕ):ℝ)*((r-1:ℕ):ℝ) ≤ alpha N*(N:ℝ)/4 := by
    have hh := mul_le_mul_of_nonneg_right he1 hrp.le
    calc
      _ ≤ (1/(4*((r-1:ℕ):ℝ))*alpha N*(N:ℝ))*((r-1:ℕ):ℝ) := hh
      _ = (alpha N*(N:ℝ)/4) * (((r-1:ℕ):ℝ)/((r-1:ℕ):ℝ)) := by ring
      _ = _ := by rw [div_self hrp.ne', mul_one]
  have hcollision : ((2*s+r+1:ℕ):ℝ)*((r-1:ℕ):ℝ)/((N-1:ℕ):ℝ)≤rho N/2 := by
    apply (div_le_iff₀ hNm).mpr
    have hh := mul_le_mul_of_nonneg_left hhalf hap.le
    have hh2 := mul_le_mul_of_nonneg_right harho hNm.le
    nlinarith
  refine ⟨by linarith,?_⟩
  have hlast := hexc1 s hs
  simp only [one_mul] at hlast
  have hlast2 := mul_le_mul_of_nonneg_right hasqrt hNp.le
  rw [hsqr]
  nlinarith

end LooseHamilton.BootstrapPrivateMobilityScales
