module

public import HittingTimeLooseHamilton.IndexedOverlapMonotone
public import HittingTimeLooseHamilton.FrameSamplingRefined
public import HittingTimeLooseHamilton.FrameConditionalCompletionLaw
public import HittingTimeLooseHamilton.FrameConcentrationScales

public section

noncomputable section
namespace LooseHamilton.CandidateBalance

/-- A bounded boundary and linear-size objects make the support loss negligible. -/
lemma boundary_batch_exponent_bound (N k d τ m a b ν : ℝ)
    (hN : 0 < N) (hk : 0 < k) (hd : 0 ≤ d) (hb : 0 ≤ b) (hν : 0 ≤ ν)
    (hNk : N ≤ a*k) (hdb : d ≤ b) (hratio : τ/m ≤ ν/k) :
    d*τ/m  ≤  (b*a)*(ν/N) := by
  have hbase : ν/k ≤ a*(ν/N) := by
    apply (div_le_iff₀ hk).mpr
    apply (mul_le_mul_iff_left₀ hN).mp
    have hx := mul_le_mul_of_nonneg_left hNk hν
    field_simp [hN.ne']
    nlinarith
  calc
    d*τ/m = d*(τ/m) := by ring
    _  ≤  d*(ν/k) := mul_le_mul_of_nonneg_left hratio hd
    _  ≤  b*(ν/k) := mul_le_mul_of_nonneg_right hdb (div_nonneg hν hk.le)
    _  ≤  b*(a*(ν/N)) := mul_le_mul_of_nonneg_left hbase hb
    _ = _ := by ring

/-- The smaller conditional batch still satisfies the quarter-size hypotheses. -/
lemma erased_quarter_parameters (m k τ : ℕ) (hk : 1 ≤ k)
    (hk4 : 4*k ≤ m) (ht4 : 4*τ ≤ m) :
    0 < m-1 ∧ 4*(k-1) ≤ m-1 ∧ 4*(τ-1) ≤ m-1 := by omega

end LooseHamilton.CandidateBalance
