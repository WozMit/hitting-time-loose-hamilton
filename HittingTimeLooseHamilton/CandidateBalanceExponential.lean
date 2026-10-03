module

public import HittingTimeLooseHamilton.CandidateBalanceScales

public section

noncomputable section
namespace LooseHamilton
open Filter Topology
open FrameScales

/-- A multiplicative forward loss at most one half is absorbed in half the
reverse exponential exponent. -/
lemma candidate_exponential_scalar {p ε c d τ L a x : ℝ}
    (hp : 0 ≤ p) (hε : ε ≤ 1/2) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hτ : d * x ≤ τ) (hscale : a*x = L/100)
    (hlarge : Real.log 2 ≤ c*d*L/200)
    (hforward : (1-ε)*p ≤ Real.exp (-c*a*τ)) :
    p ≤ Real.exp (-(c*d/200)*L) := by
  have hh := (forward_reverse_scalar_bound hε hp hforward).2.2
  have hmul := mul_le_mul_of_nonneg_left hτ (mul_nonneg hc ha)
  have hex : -c*a*τ ≤ -(c*d*L/100) := by
    have he : c*a*(d*x) = c*d*L/100 := by rw [mul_assoc c a, mul_left_comm a d,←mul_assoc, hscale]; ring
    nlinarith only [hmul,he]
  calc
    p ≤ 2*Real.exp (-c*a*τ) := hh
    _ ≤ 2*Real.exp (-(c*d*L/100)) := by gcongr
    _ = Real.exp (Real.log 2 - c*d*L/100) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ)<2),Real.exp_neg]
      ring
    _ ≤ Real.exp (-(c*d/200)*L) := by gcongr; linarith

/-- Section 8's stretched exponential follows with an explicit constant from
its multiplicative forward/reverse comparison and batch lower bound. -/
theorem eventually_candidate_exponential {c d : ℝ} (hc : 0<c) (hd : 0<d)
    {p ε τ : ℕ→ℝ} (hp : ∀ᶠ N in atTop,0≤p N)
    (hε : ∀ᶠ N in atTop,ε N≤1/2)
    (hτ : ∀ᶠ N in atTop,d*nu N*L1 N≤τ N)
    (hforward : ∀ᶠ N in atTop,
      (1-ε N)*p N≤Real.exp (-c*alpha N*τ N)) :
    ∀ᶠ N in atTop,
      p N≤Real.exp (-(c*d/200)*L1 N*(L3 N)^(99/100:ℝ)) := by
  have hlarge := (target_exponent_tendsto.const_mul_atTop (show 0<c*d/200 from div_pos (mul_pos hc hd) (by norm_num))).eventually
    (eventually_ge_atTop (Real.log 2))
  filter_upwards [eventual_range,hp,hε,hτ,hforward,hlarge] with N hN hp hε hτ hf hl
  have h3 : 0<L3 N := by linarith [hN.2.2.1]
  have hs : alpha N*(nu N*L1 N) = (L1 N*(L3 N)^(99/100:ℝ))/100 := by
    rw [←mul_assoc,alpha_mul_nu N h3]; ring
  have hh := candidate_exponential_scalar hp hε hc.le hN.2.2.2.1.le
    (by simpa only [mul_assoc] using hτ) hs (by nlinarith only [hl]) hf
  convert hh using 1
  congr 1
  ring

end LooseHamilton
