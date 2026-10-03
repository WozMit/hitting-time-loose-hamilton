module

public import HittingTimeLooseHamilton.BootstrapMaximumIntersection
public import HittingTimeLooseHamilton.BootstrapPrivateMobilityScales
public import HittingTimeLooseHamilton.SequentialCompletionGates

public section

/-! Numerical losses for sequential mobility in a one-port residual base. -/
noncomputable section
namespace LooseHamilton.BootstrapPortDensityScales
open Filter Topology FrameScales BootstrapPrivateMobilityScales

/-- The endpoint exceptional fraction is negligible relative to the test density. -/
theorem quarter_alpha_div_rho_tendsto_zero :
    Tendsto (fun N => (alpha N)^(1/4:ℝ)/rho N) atTop (nhds 0) := by
  have hh := alpha_tendsto_zero.rpow_const (p := (1/8:ℝ)) (Or.inr (by norm_num))
  simp only [Real.zero_rpow (by norm_num : (1/8:ℝ)≠0)] at hh
  apply hh.congr'
  filter_upwards [eventual_range] with N hN
  rw [rho, ←Real.rpow_sub hN.2.2.2.1]
  norm_num

/-- The ambient sequential-mobility error is smaller than rho. -/
theorem error_div_rho_tendsto_zero (r : ℕ) :
    Tendsto (fun N => BootstrapMaximumIntersection.error r N / rho N)
      atTop (nhds 0) := by
  have hstatic : Tendsto (fun N : ℕ =>
      (((r-2:ℕ):ℝ)+2*(N:ℝ)^(1/10:ℝ)+2)/(N:ℝ)/rho N)
      atTop (nhds 0) := by
    apply squeeze_zero' _ _ (exclusion_ratio_tendsto_zero (r+1))
    · filter_upwards [eventual_range] with N hN
      exact div_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg _))
        hN.2.2.2.2.2.2.1.le
    · filter_upwards [eventual_range] with N hN
      have harho : alpha N ≤ rho N := by
        change alpha N ≤ (alpha N)^(1/8:ℝ)
        calc
          _ = (alpha N)^(1:ℝ) := (Real.rpow_one _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge' hN.2.2.2.1.le
            hN.2.2.2.2.1.le (by norm_num) (by norm_num)
      have hr : ((r-2:ℕ):ℝ) ≤ (r:ℝ) := by exact_mod_cast Nat.sub_le r 2
      apply le_trans (div_le_div_of_nonneg_left (by positivity) hN.2.2.2.1 harho)
      apply div_le_div_of_nonneg_right _ hN.2.2.2.1.le
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      push_cast
      linarith
  have hh := ((sqrt_alpha_div_rho_tendsto_zero.const_mul
    (Real.sqrt (r-2:ℕ)+1)).add
      (quarter_alpha_div_rho_tendsto_zero.const_mul (Real.sqrt 2))).add hstatic
  convert hh using 1
  · ext N
    unfold BootstrapMaximumIntersection.error
    ring
  · simp

/-- Every fixed multiple of the ambient error lies below rho eventually. -/
theorem eventually_error_lt_rho (r : ℕ) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C*BootstrapMaximumIntersection.error r N < rho N := by
  have ht := (error_div_rho_tendsto_zero r).const_mul C
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    eventual_range] with N hh hN
  have hp := hN.2.2.2.2.2.2.1
  have hx : C*BootstrapMaximumIntersection.error r N/rho N < 1 := by
    convert hh using 1 <;> ring
  simpa using (div_lt_iff₀ hp).mp hx

/-- Loss from forbidding original ports is covered by the same ambient error. -/
theorem forbidden_ratio_le_error {r N s : ℕ} (hα : 0 ≤ alpha N)
    (hs : (s:ℝ) ≤ (N:ℝ)^(1/10:ℝ)) :
    ((s:ℝ)+1)/(N:ℝ) ≤ BootstrapMaximumIntersection.error r N := by
  have hnum : (s:ℝ)+1 ≤ ((r-2:ℕ):ℝ)+2*(N:ℝ)^(1/10:ℝ)+2 := by
    have hp : 0 ≤ (N:ℝ)^(1/10:ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hr : 0 ≤ ((r-2:ℕ):ℝ) := Nat.cast_nonneg _
    linarith
  have hh := div_le_div_of_nonneg_right hnum (Nat.cast_nonneg N)
  unfold BootstrapMaximumIntersection.error
  have hfirst : 0 ≤ (Real.sqrt (r-2:ℕ)+1)*Real.sqrt (alpha N) := by positivity
  have hsecond : 0 ≤ Real.sqrt 2*(alpha N)^(1/4:ℝ) := by positivity
  linarith

/-- Simultaneous sequential and forbidden-link losses are uniformly below rho. -/
theorem eventually_combined_loss_lt_rho (r : ℕ) (C D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ N : ℕ in atTop, ∀ s : ℕ, (s:ℝ) ≤ (N:ℝ)^(1/10:ℝ) →
      C*BootstrapMaximumIntersection.error r N + D*((s:ℝ)+1)/(N:ℝ) < rho N := by
  filter_upwards [eventually_error_lt_rho r (C+D), eventual_range] with N hN hR s hs
  have hh := mul_le_mul_of_nonneg_left
    (forbidden_ratio_le_error (r:=r) hR.2.2.2.1.le hs) hD
  calc
    _ ≤ (C+D)*BootstrapMaximumIntersection.error r N := by
      calc
        _ = C*BootstrapMaximumIntersection.error r N + D*(((s:ℝ)+1)/(N:ℝ)) := by ring
        _ ≤ C*BootstrapMaximumIntersection.error r N + D*BootstrapMaximumIntersection.error r N := add_le_add_right hh _
        _ = _ := by ring
    _ < rho N := hN

end LooseHamilton.BootstrapPortDensityScales

namespace LooseHamilton.BootstrapPortDensityScales
open FrameScales

/-- Replace the residual denominator by the ambient size, with a factor two. -/
theorem residual_port_loss_le {r N s : ℕ} (hN : 2 ≤ N) :
    2*(s:ℝ)*((r-1:ℕ):ℝ)/((N-1:ℕ):ℝ) ≤
      4*((r-1:ℕ):ℝ)*((s:ℝ)+1)/(N:ℝ) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hm : (0:ℝ)<((N-1:ℕ):ℝ) := by exact_mod_cast (show 0<N-1 by omega)
  have hhalf : (N:ℝ) ≤ 2*((N-1:ℕ):ℝ) := by exact_mod_cast (show N≤2*(N-1) by omega)
  apply (div_le_div_iff₀ hm hn).mpr
  have hh := mul_le_mul_of_nonneg_left hhalf
    (show 0≤2*(s:ℝ)*((r-1:ℕ):ℝ) by positivity)
  nlinarith [show 0≤((r-1:ℕ):ℝ)*((N-1:ℕ):ℝ) by positivity]

/-- A coefficient depending only on r and the finite counting coefficient. -/
@[expose] def densityCoefficient (r : ℕ) (K : ℝ) : ℝ :=
  K*(Real.sqrt (r-2:ℕ)+1+Real.sqrt 2+(r:ℝ)+3)+4*((r-1:ℕ):ℝ)

/-- The actual sequential envelope, before replacing s by its uniform upper bound. -/
theorem explicit_density_bound {r N s : ℕ} {K : ℝ} (hN : 2 ≤ N)
    (hK : 0 ≤ K) (hα : 0 ≤ alpha N) (hα1 : alpha N ≤ 1) :
    K*((Real.sqrt (r-2:ℕ)+1)*Real.sqrt (alpha N) +
      Real.sqrt 2*(alpha N)^(1/4:ℝ) +
      (((r-2:ℕ):ℝ)+2*(s:ℝ)+1)/(N:ℝ)) +
      2*(s:ℝ)*((r-1:ℕ):ℝ)/((N-1:ℕ):ℝ) ≤
      densityCoefficient r K*(alpha N)^(1/4:ℝ) +
        densityCoefficient r K*((s:ℝ)+1)/(N:ℝ) := by
  have hsqrt : Real.sqrt (alpha N) ≤ (alpha N)^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge' hα hα1 (by norm_num) (by norm_num)
  have hstatic : (((r-2:ℕ):ℝ)+2*(s:ℝ)+1)/(N:ℝ) ≤
      ((r:ℝ)+3)*((s:ℝ)+1)/(N:ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    have hr : ((r-2:ℕ):ℝ) ≤ (r:ℝ) := by exact_mod_cast Nat.sub_le r 2
    nlinarith [show 0≤(r:ℝ)*(s:ℝ) by positivity]
  have hm := mul_le_mul_of_nonneg_left hsqrt
    (show 0≤Real.sqrt (r-2:ℕ)+1 by positivity)
  have hseq := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add_left hm (Real.sqrt 2*(alpha N)^(1/4:ℝ))) hstatic) hK
  have hport := residual_port_loss_le (r:=r) (s:=s) hN
  let A : ℝ := Real.sqrt (r-2:ℕ)+1+Real.sqrt 2
  have hA : 0≤A := by dsimp [A]; positivity
  have ht : 0≤(alpha N)^(1/4:ℝ) := Real.rpow_nonneg hα _
  have hx : 0≤((s:ℝ)+1)/(N:ℝ) := by positivity
  have hsum :
      K*((Real.sqrt (r-2:ℕ)+1)*Real.sqrt (alpha N)+
        Real.sqrt 2*(alpha N)^(1/4:ℝ)+(((r-2:ℕ):ℝ)+2*(s:ℝ)+1)/(N:ℝ))+
        2*(s:ℝ)*((r-1:ℕ):ℝ)/((N-1:ℕ):ℝ) ≤
      K*A*(alpha N)^(1/4:ℝ) +
        (K*((r:ℝ)+3)+4*((r-1:ℕ):ℝ))*(((s:ℝ)+1)/(N:ℝ)) := by
    dsimp [A]
    calc
      _ ≤ _ := add_le_add hseq hport
      _ = _ := by ring
  apply hsum.trans
  have hp : 0 ≤ (K*((r:ℝ)+3)+4*((r-1:ℕ):ℝ))*(alpha N)^(1/4:ℝ) := by positivity
  have hq : 0 ≤ K*A*(((s:ℝ)+1)/(N:ℝ)) := by positivity
  unfold densityCoefficient
  dsimp [A] at hp hq ⊢
  ring_nf at hp hq ⊢
  linarith

end LooseHamilton.BootstrapPortDensityScales

namespace LooseHamilton.BootstrapPortDensityScales
open Filter Topology FrameScales SequentialCompletion

@[expose] def countingCoefficient (r : ℕ) : ℝ := (2:ℝ)^(r-1)*((r-1).factorial:ℝ)
@[expose] def densityConstant (r : ℕ) : ℝ :=
  densityCoefficient r (countingCoefficient r*((r-1:ℕ):ℝ))

theorem densityConstant_nonneg (r : ℕ) : 0 ≤ densityConstant r := by
  unfold densityConstant densityCoefficient countingCoefficient
  positivity

/-- Direct density estimate with the true number of forbidden ports. -/
theorem actual_density_bound {r N s p q : ℕ} (hN : 2 ≤ N)
    (hp : p ≤ 2*s) (hq : q ≤ 2*s)
    (hα : 0 ≤ alpha N) (hα1 : alpha N ≤ 1) :
    countingCoefficient r*((r-1:ℕ):ℝ)*(exceptionBound r N p/(N:ℝ)) +
      (q:ℝ)*((r-1:ℕ):ℝ)/((N-1:ℕ):ℝ) ≤
      densityConstant r*(alpha N)^(1/4:ℝ) +
        densityConstant r*((s:ℝ)+1)/(N:ℝ) := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (show N≠0 by omega)
  have hp' : (p:ℝ)≤2*(s:ℝ) := by exact_mod_cast hp
  have hq' : (q:ℝ)≤2*(s:ℝ) := by exact_mod_cast hq
  have he : exceptionBound r N p/(N:ℝ) ≤
      (Real.sqrt (r-2:ℕ)+1)*Real.sqrt (alpha N)+
        Real.sqrt 2*(alpha N)^(1/4:ℝ)+(((r-2:ℕ):ℝ)+2*(s:ℝ)+1)/(N:ℝ) := by
    unfold exceptionBound
    rw [show ((Real.sqrt (r-2:ℕ)+1)*Real.sqrt (alpha N)*N+
      Real.sqrt 2*(alpha N)^(1/4:ℝ)*N+(r-2:ℕ)+p+1)/(N:ℝ) =
      (Real.sqrt (r-2:ℕ)+1)*Real.sqrt (alpha N)+Real.sqrt 2*(alpha N)^(1/4:ℝ)+
        (((r-2:ℕ):ℝ)+p+1)/(N:ℝ) by field_simp <;> ring]
    gcongr
  have hl : (q:ℝ)*((r-1:ℕ):ℝ)/((N-1:ℕ):ℝ) ≤
      2*(s:ℝ)*((r-1:ℕ):ℝ)/((N-1:ℕ):ℝ) := by gcongr
  have hK : 0≤countingCoefficient r*((r-1:ℕ):ℝ) := by unfold countingCoefficient; positivity
  exact (add_le_add (mul_le_mul_of_nonneg_left he hK) hl).trans
    (explicit_density_bound hN hK hα hα1)

/-- The explicit constant envelope is itself below the port-test density. -/
theorem eventually_explicit_density_lt_rho (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ s : ℕ, (s:ℝ) ≤ (N:ℝ)^(1/10:ℝ) →
      densityConstant r*(alpha N)^(1/4:ℝ)+
        densityConstant r*((s:ℝ)+1)/(N:ℝ) < rho N := by
  have ht := ((quarter_alpha_div_rho_tendsto_zero.add
    (error_div_rho_tendsto_zero r)).const_mul (densityConstant r))
  simp only [add_zero, mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    eventual_range] with N hh hR s hs
  have he := mul_le_mul_of_nonneg_left
    (forbidden_ratio_le_error (r:=r) hR.2.2.2.1.le hs) (densityConstant_nonneg r)
  have hlt : densityConstant r*(alpha N)^(1/4:ℝ)+
      densityConstant r*BootstrapMaximumIntersection.error r N < rho N := by
    have hx : (densityConstant r*(alpha N)^(1/4:ℝ)+
      densityConstant r*BootstrapMaximumIntersection.error r N)/rho N < 1 := by
      convert hh using 1 <;> ring
    simpa using (div_lt_iff₀ hR.2.2.2.2.2.2.1).mp hx
  calc
    _ = densityConstant r*(alpha N)^(1/4:ℝ)+
        densityConstant r*(((s:ℝ)+1)/(N:ℝ)) := by ring
    _ ≤ _ := add_le_add_right he _
    _ < rho N := hlt

end LooseHamilton.BootstrapPortDensityScales
