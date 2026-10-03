module

public import HittingTimeLooseHamilton.FrameSamplingParameters
public import HittingTimeLooseHamilton.FrameSurvivalRatios
public import HittingTimeLooseHamilton.FrameSurvivalRates
public import HittingTimeLooseHamilton.CandidateNormalizationTransferScalar

public section

noncomputable section
set_option maxHeartbeats 800000
namespace LooseHamilton.CandidateBalance
open FrameSurvival

/-- Exact raw-host retention factor. The sampling population m0 can be smaller. -/
@[expose] def rawRetention (m τ : ℕ) : ℝ := ((m:ℝ)-τ)/m

theorem restricted_normalization_finite (m m0 k τ N : ℕ) (ν a r : ℝ)
    (hN : 0 < (N:ℝ)) (hm0 : 0 < m0) (hm : m0 ≤ m) (hk : 1 ≤ k)
    (ht : 1 ≤ τ) (hk4 : 4*k ≤ m0) (ht4 : 4*τ ≤ m0)
    (hν : 0 ≤ ν) (ha : 0 ≤ a) (hr : 0 < r) (hlog : 0 < Real.log (N:ℝ))
    (hNk : (N:ℝ) ≤ a*k) (hkN : (k:ℝ) ≤ N)
    (hτ : (τ:ℝ) ≤ ν*m0/k)
    (hdense : (N:ℝ)*Real.log N/(2*r) ≤ m0) :
    |rawRetention m τ-1|  ≤  a*(ν/N) ∧
    |zeta m0 τ (k-1)/zeta m0 τ k-1|  ≤  2*a*(ν/N) ∧
    |conditionedZeta m0 τ k/zeta m0 τ k-1|  ≤  4*r/Real.log N+2*a*(ν/N) ∧
    |rawRetention m τ*(zeta m0 τ (k-1)/zeta m0 τ k)-1|  ≤  3*a*(ν/N) ∧
    |rawRetention m τ*(conditionedZeta m0 τ k/zeta m0 τ k)-1|  ≤ 
      4*r/Real.log N+3*a*(ν/N) := by
  have hmR : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have h0R : 0 < (m0:ℝ) := by exact_mod_cast hm0
  have hkR : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk4R : 4*(k:ℝ) ≤ m0 := by exact_mod_cast hk4
  have ht4R : 4*(τ:ℝ) ≤ m0 := by exact_mod_cast ht4
  have hτk := (le_div_iff₀ hkR).mp hτ
  have htk : (τ:ℝ)*(N:ℝ)  ≤  a*ν*m0 := by
    have hh := mul_le_mul_of_nonneg_left hNk (Nat.cast_nonneg τ : (0:ℝ) ≤ τ)
    have hh' := mul_le_mul_of_nonneg_left hτk ha
    nlinarith
  have hb : (τ:ℝ)/m0  ≤  a*(ν/N) := by
    apply (div_le_iff₀ h0R).mpr
    apply (mul_le_mul_iff_left₀ hN).mp
    field_simp
    nlinarith
  have hbraw : (τ:ℝ)/m  ≤  a*(ν/N) :=
    (div_le_div_of_nonneg_left (Nat.cast_nonneg _) h0R (Nat.cast_le.mpr hm)).trans hb
  have hret : |rawRetention m τ-1| ≤ a*(ν/N) := by
    have he : rawRetention m τ-1= -(τ:ℝ)/m := by unfold rawRetention; field_simp <;> ring
    rw [he,abs_div,abs_neg,abs_of_nonneg (Nat.cast_nonneg τ),abs_of_pos hmR]
    exact hbraw
  have hsurv := completion_ratio hk (by omega : k ≤ m0) (by omega : τ ≤ m0-k)
  have hcond := conditioned_completion_ratio hk ht (by omega : τ ≤ m0-k)
  have hs : |zeta m0 τ (k-1)/zeta m0 τ k-1| ≤ 2*a*(ν/N) := by
    rw [hsurv]
    exact frame_survival_ratio_rate _ _ _ _ _ _ h0R hkR hN hν (Nat.cast_nonneg _) hk4R ht4R hτ hNk
  have hkden : 2*(k:ℝ)/m0 ≤ 4*r/Real.log N := by
    have hd := (div_le_iff₀ (by positivity : 0 < 2*r)).mp hdense
    apply (div_le_div_iff₀ h0R hlog).mpr
    nlinarith [mul_le_mul_of_nonneg_right hkN hlog.le]
  have hc : |conditionedZeta m0 τ k/zeta m0 τ k-1| ≤ 4*r/Real.log N+2*a*(ν/N) := by
    rw [hcond]
    have hh := frame_deleted_survival_ratio_error (m0:ℝ) k τ h0R
      (by exact_mod_cast hk) (Nat.cast_nonneg _) hk4R ht4R
    have hh' : 2*((k:ℝ)+τ)/m0 = 2*(k:ℝ)/m0+2*((τ:ℝ)/m0) := by ring
    rw [hh'] at hh
    linarith
  have hret01 : 0 ≤ rawRetention m τ ∧ rawRetention m τ ≤ 1 := by
    have hτm : (τ:ℝ) ≤ m := by exact_mod_cast (show τ ≤ m by omega)
    unfold rawRetention
    exact ⟨div_nonneg (sub_nonneg.mpr hτm) hmR.le,(div_le_one hmR).mpr (by linarith [(Nat.cast_nonneg τ : (0:ℝ) ≤ τ)])⟩
  have hprod (b e : ℝ) (hb : |b-1| ≤ e) :
      |rawRetention m τ*b-1| ≤ e+a*(ν/N) := by
    calc
      _ = |rawRetention m τ*(b-1)+(rawRetention m τ-1)| := by congr 1; ring
      _  ≤  |rawRetention m τ*(b-1)|+|rawRetention m τ-1| := abs_add_le _ _
      _ = rawRetention m τ*|b-1|+|rawRetention m τ-1| := by rw [abs_mul,abs_of_nonneg hret01.1]
      _  ≤  e+a*(ν/N) := add_le_add ((mul_le_mul_of_nonneg_right hret01.2 (abs_nonneg (b-1))).trans (by simpa only [one_mul] using hb)) hret
  refine ⟨hret,hs,hc,?_,?_⟩
  · convert hprod _ _ hs using 1 <;> ring
  · convert hprod _ _ hc using 1 <;> ring
end LooseHamilton.CandidateBalance
