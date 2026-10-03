module

public import HittingTimeLooseHamilton.BootstrapPrivateMobilityScales
public import HittingTimeLooseHamilton.MigrationCutScales

public section

noncomputable section
namespace LooseHamilton.BootstrapEndpointMobilityScales
open Filter Topology FrameScales BootstrapPrivateMobilityScales

/-- Simultaneous density and exceptional-target estimates for the paper's scales. -/
theorem eventually_endpoint_mobility_bounds (r : ℕ) (hr : 3≤r) :
    ∀ᶠ N : ℕ in atTop, 8*r≤N ∧ 0<alpha N ∧ alpha N≤1/2 ∧ 0<rho N ∧
      ∀ s : ℕ, (s:ℝ)≤(N:ℝ)^(1/10:ℝ) →
        (2:ℝ)^(r-1)*((r-1).factorial:ℝ)*Real.sqrt (alpha N) +
          ((2*s+3*r+4:ℕ):ℝ)*((r-1:ℕ):ℝ)/((N-1:ℕ):ℝ) < rho N ∧
        Real.sqrt (alpha N)*(N:ℝ)+((2*s+3*r+4:ℕ):ℝ) ≤
          2*Real.sqrt (alpha N)*(N:ℝ) := by
  let K : ℝ := (2:ℝ)^(r-1)*((r-1).factorial:ℝ)
  have ht := sqrt_alpha_div_rho_tendsto_zero.const_mul K
  simp only [mul_zero] at ht
  have hrp : (0:ℝ)<((r-1:ℕ):ℝ) := by exact_mod_cast (show 0<r-1 by omega)
  have he : (0:ℝ)<1/(4*((r-1:ℕ):ℝ)) := by positivity
  filter_upwards [eventually_ge_atTop (8*r), eventual_range,
    alpha_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    eventually_exclusion_bound (3*r+3) he,
    eventually_exclusion_bound (3*r+3) (by norm_num : (0:ℝ)<1)] with N hN hR ha hk hexc hexc1
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
  have hfirst : (2:ℝ)^(r-1)*((r-1).factorial:ℝ)*Real.sqrt (alpha N)<rho N/2 := by
    have hh := (div_lt_iff₀ hrho).mp (show K*Real.sqrt (alpha N)/rho N<1/2 by convert hk using 1 <;> ring)
    dsimp [K] at hh
    nlinarith
  have he1 : ((2*s+3*r+4:ℕ):ℝ) ≤ 1/(4*((r-1:ℕ):ℝ))*alpha N*(N:ℝ) := by
    simpa [Nat.add_assoc] using hexc s hs
  have he2 : ((2*s+3*r+4:ℕ):ℝ)*((r-1:ℕ):ℝ) ≤ alpha N*(N:ℝ)/4 := by
    have hh := mul_le_mul_of_nonneg_right he1 hrp.le
    calc
      _ ≤ (1/(4*((r-1:ℕ):ℝ))*alpha N*(N:ℝ))*((r-1:ℕ):ℝ) := hh
      _ = (alpha N*(N:ℝ)/4) * (((r-1:ℕ):ℝ)/((r-1:ℕ):ℝ)) := by ring
      _ = _ := by rw [div_self hrp.ne', mul_one]
  have hcollision : ((2*s+3*r+4:ℕ):ℝ)*((r-1:ℕ):ℝ)/((N-1:ℕ):ℝ)≤rho N/2 := by
    apply (div_le_iff₀ hNm).mpr
    have hh := mul_le_mul_of_nonneg_left hhalf hap.le
    have hh2 := mul_le_mul_of_nonneg_right harho hNm.le
    nlinarith
  refine ⟨by linarith,?_⟩
  have hlast : ((2*s+3*r+4:ℕ):ℝ) ≤ 1*alpha N*(N:ℝ) := by
    simpa [Nat.add_assoc] using hexc1 s hs
  simp only [one_mul] at hlast
  have hlast2 := mul_le_mul_of_nonneg_right hasqrt hNp.le
  nlinarith

/-- The weighted exceptional fraction is exactly a constant times alpha^(1/4). -/
theorem weighted_fraction_eq (N : ℕ) (hα : 0 ≤ alpha N) :
    Real.sqrt (2*Real.sqrt (alpha N)) = Real.sqrt 2 * (alpha N)^(1/4:ℝ) := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  simp only [Real.sqrt_eq_rpow, ← Real.rpow_mul hα]
  norm_num

theorem weighted_fraction_sq (N : ℕ) (hα : 0 ≤ alpha N) :
    (Real.sqrt 2 * (alpha N)^(1/4:ℝ))^2 = 2*Real.sqrt (alpha N) := by
  rw [← weighted_fraction_eq N hα]
  exact Real.sq_sqrt (by positivity)

/-- All one-vertex residual sizes have negligible discarded cut mass, while
weighted target averaging costs only sqrt(2)*alpha^(1/4). -/
theorem eventually_weighted_bounds (r : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      0 < Real.sqrt (2*Real.sqrt (alpha N)) ∧
      Real.sqrt (2*Real.sqrt (alpha N)) ≤ 1/4 ∧
      ∀ n : ℕ, N-1 ≤ n → Migration.cutLoss r n ≤ 1/4 := by
  have ht : Tendsto (fun N => Real.sqrt (2*Real.sqrt (alpha N))) atTop (nhds 0) := by
    have hh := ((alpha_tendsto_zero.sqrt).const_mul 2).sqrt
    simpa using hh
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (Migration.eventually_cutLoss_le_quarter r)
  filter_upwards [eventual_range, ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4)),
    eventually_ge_atTop (n₀+1)] with N hR hsmall hN
  refine ⟨Real.sqrt_pos.2 (mul_pos (by norm_num) (Real.sqrt_pos.2 hR.2.2.2.1)),
    hsmall.le, ?_⟩
  intro n hn
  exact hn₀ n (by omega)

/-- The residual source room condition follows already from the ambient threshold. -/
theorem residual_room {N n p r : ℕ} (hr : 3 ≤ r) (hN : 8*r ≤ N)
    (hn : N-1 ≤ n) (hp : p = r-2) : 5*(r-1) < n-p := by omega

end LooseHamilton.BootstrapEndpointMobilityScales
