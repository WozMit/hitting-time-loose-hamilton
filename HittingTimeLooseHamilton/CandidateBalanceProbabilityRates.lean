module

public import HittingTimeLooseHamilton.CandidateBalanceScales

public section

noncomputable section
namespace LooseHamilton.FrameScales
open Filter Topology

/-- Any nonnegative failure probability satisfying the uniform Chebyshev scale
is little-o of every fixed alpha power, including the powers lost to Markov. -/
lemma failure_probability_div_alpha_power {p : ℕ→ℝ} {C : ℝ}
    (hp : ∀ᶠ N in atTop,0≤p N)
    (hbound : ∀ᶠ N in atTop,
      p N≤C*((alpha N/100000)^(-2:ℝ)*(L2 N)^(-24/25:ℝ))) (a : ℝ) :
    Tendsto (fun N=>p N/(alpha N)^a) atTop (nhds 0) := by
  have ht := (failure_scale_div_alpha_power a).const_mul C
  simp only [mul_zero] at ht
  apply squeeze_zero' ?_ ?_ ht
  · filter_upwards [eventual_range,hp] with N hN hp
    exact div_nonneg hp (Real.rpow_nonneg hN.2.2.2.1.le a)
  · filter_upwards [eventual_range,hbound] with N hN hb
    have hh := div_le_div_of_nonneg_right hb (Real.rpow_nonneg hN.2.2.2.1.le a)
    simpa only [mul_div_assoc] using hh

/-- The static entropy exceptional fraction, with any fixed implied constant,
is negligible compared with alpha. -/
lemma static_exceptional_fraction_small {p : ℕ→ℝ} {C : ℝ}
    (hp : ∀ᶠ N in atTop,0≤p N)
    (hbound : ∀ᶠ N in atTop,p N≤C/(alpha N*Real.sqrt (L2 N))) :
    Tendsto (fun N=>p N/alpha N) atTop (nhds 0) := by
  have ht := (static_error_div_alpha_power 1).const_mul C
  simp only [Real.rpow_one,mul_zero] at ht
  apply squeeze_zero' ?_ ?_ ht
  · filter_upwards [eventual_range,hp] with N hN hp
    exact div_nonneg hp hN.2.2.2.1.le
  · filter_upwards [eventual_range,hbound] with N hN hb
    have hh := div_le_div_of_nonneg_right hb hN.2.2.2.1.le
    convert hh using 1
    ring

end LooseHamilton.FrameScales
