module

public import HittingTimeLooseHamilton.FrameScales

public section

/-! Uniform scalar envelopes for bounded frame modifications. All thresholds
are chosen before the varying frame, host and boundary data. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Filter Topology

/-- A fixed multiple of the allowed marker scale, plus a bounded error, is o(N). -/
theorem frame_loss_ratio_tendsto_zero (a b : ℝ) :
    Tendsto (fun N : ℕ => (a*(N:ℝ)^(1/10:ℝ)+b)/(N:ℝ))
      atTop (nhds 0) := by
  have hp := tendsto_nat_rpow_ratio (a := (1/10:ℝ)) (b := 1) (by norm_num)
  simp only [Real.rpow_one] at hp
  have hi : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  convert (hp.const_mul a).add (hi.const_mul b) using 1 <;>
    simp [add_div, mul_div_assoc, div_eq_mul_inv, add_mul, mul_assoc]

/-- Uniform absorption of all losses bounded by a fixed affine marker envelope. -/
theorem eventually_frame_loss_small (a b ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      x ≤ a*(N:ℝ)^(1/10:ℝ)+b → x ≤ ε*(N:ℝ) := by
  filter_upwards [((frame_loss_ratio_tendsto_zero a b).eventually
    (gt_mem_nhds hε)), eventually_ge_atTop (1:ℕ)] with N hN hpos x hx
  have hp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  exact hx.trans (le_of_lt (by
    have := (div_lt_iff₀ hp).mp hN
    nlinarith))

/-- One original-N threshold works simultaneously for every marker count and
bounded deletion count. -/
theorem eventually_marker_deletion_envelope (r : ℕ) (a b ε : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ s d : ℕ,
      (s:ℝ) ≤ (N:ℝ)^(1/10:ℝ) → d ≤ 4*r →
      a*s+b*d ≤ ε*(N:ℝ) := by
  filter_upwards [eventually_frame_loss_small a (b*(4*r)) ε hε] with N hN s d hs hd
  apply hN
  have hd' : (d:ℝ) ≤ 4*r := by exact_mod_cast hd
  nlinarith [mul_le_mul_of_nonneg_left hs ha, mul_le_mul_of_nonneg_left hd' hb]

/-- Cardinality hypotheses needed for the half-density candidate estimate,
uniform over bounded frame changes and all admissible original marker counts. -/
theorem eventually_candidate_port_envelope (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ s p d n : ℕ,
      (s:ℝ) ≤ (N:ℝ)^(1/10:ℝ) → p ≤ 4*s+4 →
      d ≤ 4*r → n+d=N → 2*r*p ≤ n := by
  filter_upwards [eventually_frame_loss_small (8*r) (12*r) 1 (by norm_num)] with N hN s p d n hs hp hd hn
  have hb : ((2*r*p+d:ℕ):ℝ) ≤ (8*(r:ℝ))*(N:ℝ)^(1/10:ℝ)+12*r := by
    have hp' : (p:ℝ) ≤ 4*(s:ℝ)+4 := by exact_mod_cast hp
    have hd' : (d:ℝ) ≤ 4*r := by exact_mod_cast hd
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 8*(r:ℝ) by positivity)]
  have h := hN _ hb
  simp only [one_mul] at h
  have : 2*r*p+d ≤ N := by exact_mod_cast h
  omega
/-- The same threshold controls the active vertex count and candidate losses. -/
theorem eventually_candidate_uniform_envelope (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ s p d n : ℕ,
      (s:ℝ) ≤ (N:ℝ)^(1/10:ℝ) → p ≤ 4*s+4 →
      d ≤ 4*r → n+d=N → 2*r*p ≤ n ∧ N ≤ 2*n ∧ r ≤ n := by
  filter_upwards [eventually_candidate_port_envelope r,
    eventually_ge_atTop (8*r)] with N hN hlarge s p d n hs hp hd hn
  exact ⟨hN s p d n hs hp hd hn, by omega, by omega⟩
end LooseHamilton.CandidateBalance
