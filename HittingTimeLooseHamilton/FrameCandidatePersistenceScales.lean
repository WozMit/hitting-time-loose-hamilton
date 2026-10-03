module

public import HittingTimeLooseHamilton.FrameConcentrationScales

public section

noncomputable section
namespace LooseHamilton.FrameScales
open Filter Topology

/-- Any fixed boundary error O(1/N) is at most one quarter of alpha. -/
theorem eventually_boundary_fraction_small (A : ℝ) (hA : 0≤A) :
    ∀ᶠ N : ℕ in atTop, alpha N≤1/4 ∧ A/(N:ℝ)≤alpha N/4 := by
  have ht := nu_div_vertices_div_alpha_tendsto_zero.const_mul (4*A)
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    nu_tendsto.eventually (eventually_ge_atTop 1),eventual_range,
    alpha_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))]
    with N hsmall hnu hR halpha
  refine ⟨halpha.le,?_⟩
  have h1 : A/(N:ℝ)≤A*(nu N/(N:ℝ)) := by
    have hh := div_le_div_of_nonneg_right hnu (Nat.cast_nonneg N : (0:ℝ)≤N)
    convert mul_le_mul_of_nonneg_left hh hA using 1 <;> ring
  have h2 : A*(nu N/(N:ℝ))≤alpha N/4 := by
    have hh : (4*A*(nu N/(N:ℝ)))/alpha N<1 := by convert hsmall using 1 <;> ring
    have hx := (div_lt_iff₀ hR.2.2.2.1).mp hh
    nlinarith
  exact h1.trans h2
end LooseHamilton.FrameScales
