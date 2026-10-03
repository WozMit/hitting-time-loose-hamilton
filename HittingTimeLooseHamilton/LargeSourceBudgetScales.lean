module

public import HittingTimeLooseHamilton.PathPerturbationScalars
public import HittingTimeLooseHamilton.FrameScales

public section

noncomputable section
namespace LooseHamilton
open Filter Topology

/-- Sublinear marker errors and polynomial count losses fit into one unit of
the original entropy error, uniformly once their constants are fixed. -/
theorem eventually_large_source_error (K A : ℝ) (hK : 0≤K) (hA : 0≤A) :
    ∀ᶠ N : ℕ in atTop,
      K*((N:ℝ)^(1/10:ℝ)+1)*Real.log N+A*Real.log N ≤
        (N:ℝ)/Real.sqrt (Real.log N) := by
  have ht := (tendsto_nat_power_log_real (by norm_num : (-9/10:ℝ)<0) 2).const_mul (2*K+A)
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    FrameScales.L1_tendsto.eventually (eventually_ge_atTop 1),
    eventually_ge_atTop (1:ℕ)] with N ht hlog hN
  change 1≤Real.log (N:ℝ) at hlog
  have hNp : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hNr : 1≤(N:ℝ) := by exact_mod_cast hN
  have hp : 1≤(N:ℝ)^(1/10:ℝ) := Real.one_le_rpow hNr (by norm_num)
  have hlogp : 0<Real.log (N:ℝ) := by linarith
  have hs : 0<Real.sqrt (Real.log (N:ℝ)) := Real.sqrt_pos.mpr hlogp
  have hsq : Real.sqrt (Real.log (N:ℝ))≤Real.log N := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · exact hlogp.le
    · nlinarith
  have he : (N:ℝ)^(-9/10:ℝ)=(N:ℝ)^(1/10:ℝ)/(N:ℝ) := by
    rw [show (-9/10:ℝ)=(1/10:ℝ)-1 by norm_num,Real.rpow_sub hNp,Real.rpow_one]
  rw [he,Real.rpow_two] at ht
  have ht' : (2*K+A)*(N:ℝ)^(1/10:ℝ)*(Real.log N)^2≤N := by
    have hh := (div_lt_iff₀ hNp).mp (show
      ((2*K+A)*(N:ℝ)^(1/10:ℝ)*(Real.log N)^2)/(N:ℝ)<1 by convert ht using 1; ring)
    linarith
  have hcoef : K*((N:ℝ)^(1/10:ℝ)+1)+A ≤ (2*K+A)*(N:ℝ)^(1/10:ℝ) := by nlinarith
  have hcoef0 : 0≤K*((N:ℝ)^(1/10:ℝ)+1)+A := by positivity
  have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (Real.log (N:ℝ)))
  have hhs := mul_le_mul_of_nonneg_left hsq (mul_nonneg hcoef0 hlogp.le)
  apply (le_div_iff₀ hs).mpr
  nlinarith only [ht',hh,hhs]

end LooseHamilton
