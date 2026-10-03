module

public import HittingTimeLooseHamilton.BiasedRoleCancellation

public section

/-! Quantitative finite role-support cancellation, with an explicit marker error. -/
noncomputable section
namespace LooseHamilton

/-- Bernoulli cross entropy dominates binary entropy. -/
theorem bernoulli_cross_entropy_gap_nonneg {a q : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hq : 0 < q) (hq1 : q < 1) :
    0 ≤ -q * Real.log a - (1-q) * Real.log (1-a) - Real.binEntropy q := by
  have hb : 0 < 1-a := by linarith
  have hc : 0 < 1-q := by linarith
  have h1 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos ha hq)) hq.le
  have h2 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hb hc)) hc.le
  rw [Real.log_div ha.ne' hq.ne'] at h1
  rw [Real.log_div hb.ne' hc.ne'] at h2
  have hid : q*(a/q-1)+(1-q)*((1-a)/(1-q)-1) = 0 := by
    field_simp <;> ring
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def]
  linarith

/-- Absolute form of the fixed-weight cross-entropy estimate. -/
theorem fixed_weight_cross_entropy_abs_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L j : ℕ, 0 < j → j < L →
      ∀ a : ℝ, 0 < a → a < 1 →
      |-(j : ℝ)*Real.log a - ((L : ℝ)-j)*Real.log (1-a) -
          Real.log (L.choose j : ℝ)| ≤
        (L : ℝ) * (((j : ℝ)/L-a)^2/(a*(1-a))) +
          3*Real.log ((L : ℝ)+1)+C := by
  obtain ⟨C, hC, hchoose⟩ := log_choose_binary_entropy_bound
  refine ⟨C, hC, ?_⟩
  intro L j hj hjL a ha ha1
  have hL : (0 : ℝ) < L := by exact_mod_cast (lt_trans hj hjL)
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hjLr : (j : ℝ) < L := by exact_mod_cast hjL
  have hqp := div_pos hjr hL
  have hq1 := (div_lt_one hL).mpr hjLr
  have hgap := mul_le_mul_of_nonneg_left
    (bernoulli_cross_entropy_gap_le ha ha1 hqp hq1) hL.le
  have hnon := mul_nonneg hL.le (bernoulli_cross_entropy_gap_nonneg ha ha1 hqp hq1)
  have heq : (L : ℝ)*(-((j : ℝ)/L)*Real.log a -
      (1-(j : ℝ)/L)*Real.log (1-a)-Real.binEntropy ((j : ℝ)/L)) =
      -(j : ℝ)*Real.log a - ((L : ℝ)-j)*Real.log (1-a) -
        (L : ℝ)*Real.binEntropy ((j : ℝ)/L) := by
    field_simp <;> ring
  rw [heq] at hgap hnon
  have hc := abs_le.mp (hchoose L j hj hjL)
  have hb : 0 < 1-a := by linarith
  have hquad : 0 ≤ (L : ℝ) * (((j : ℝ)/L-a)^2/(a*(1-a))) := by positivity
  apply abs_le.mpr
  constructor <;> linarith

/-- Uniform finite role-support cancellation. The relations are the real-cast
forms of `L=N-2s`, `j=k-s`, and `N=(r-1)k+s`. -/
theorem finite_role_support_cancellation (r : ℝ) (hr : 2 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L j : ℕ) (k s : ℝ),
      0 < j → j < L → 1 ≤ s → s ≤ L →
      (j : ℝ) = k-s → (L : ℝ) = (r-1)*k-s →
      |Real.log (L.choose j : ℝ) + (s-1)*Real.log 2 +
        k*(r-2)*Real.log ((r-2)/(r-1)) - k*Real.log (r-1)| ≤
        C*(s+Real.log ((L : ℝ)+1)+1) := by
  obtain ⟨C₀, hC₀, hweight⟩ := fixed_weight_cross_entropy_abs_bound
  let C := (r-2)+3+C₀+|Real.log (r-1)|+|Real.log 2|
  refine ⟨C, by dsimp [C]; have := abs_nonneg (Real.log (r-1)); have := abs_nonneg (Real.log 2); linarith, ?_⟩
  intro L j k s hj hjL hs hsL hjrel hLrel
  have hr1 : 0 < r-1 := by linarith
  have hr2 : 0 < r-2 := by linarith
  have hLp : (0 : ℝ) < L := by linarith
  have hsp : 0 ≤ s := by linarith
  have ha : 0 < 1/(r-1) := by positivity
  have ha1 : 1/(r-1) < 1 := (div_lt_one hr1).mpr (by linarith)
  have hb : 1-1/(r-1) = (r-2)/(r-1) := by field_simp <;> ring
  have hw := hweight L j hj hjL (1/(r-1)) ha ha1
  have hquad : (L : ℝ)*(((j : ℝ)/L-1/(r-1))^2/
      ((1/(r-1))*(1-1/(r-1)))) = (r-2)*s^2/L := by
    have hh := role_weight_quadratic_identity (r := r) (N := (L : ℝ)+2*s)
      (k := k) (s := s) hr (by linarith) (by linarith)
    have hid : (L : ℝ)+2*s-2*s = L := by ring
    rw [hid, ← hjrel] at hh
    exact hh
  have hqle : (r-2)*s^2/(L : ℝ) ≤ (r-2)*s := by
    apply (div_le_iff₀ hLp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsL hsp]
  rw [hquad, hb, one_div, Real.log_inv] at hw
  have hlogs : 0 ≤ Real.log ((L : ℝ)+1) := Real.log_nonneg (by linarith)
  have hmain : Real.log (L.choose j : ℝ)+(s-1)*Real.log 2+
        k*(r-2)*Real.log ((r-2)/(r-1))-k*Real.log (r-1) =
      - (-(j : ℝ)*(-Real.log (r-1))-((L : ℝ)-j)*Real.log ((r-2)/(r-1))-
        Real.log (L.choose j : ℝ)) - s*Real.log (r-1)+(s-1)*Real.log 2 := by
    rw [hjrel, hLrel]
    ring
  rw [hmain]
  calc
    _ ≤ |-(j : ℝ)*(-Real.log (r-1))-((L : ℝ)-j)*Real.log ((r-2)/(r-1))-
          Real.log (L.choose j : ℝ)| +
        s*|Real.log (r-1)|+(s-1)*|Real.log 2| := by
      have h := abs_add_le (- (-(j : ℝ)*(-Real.log (r-1))-
        ((L : ℝ)-j)*Real.log ((r-2)/(r-1))-Real.log (L.choose j : ℝ)) -
        s*Real.log (r-1)) ((s-1)*Real.log 2)
      have hh := abs_sub (- (-(j : ℝ)*(-Real.log (r-1))-
        ((L : ℝ)-j)*Real.log ((r-2)/(r-1))-Real.log (L.choose j : ℝ)))
        (s*Real.log (r-1))
      rw [abs_neg, abs_mul, abs_of_nonneg hsp] at hh
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ s-1)] at h
      linarith
    _ ≤ (r-2)*s+3*Real.log ((L : ℝ)+1)+C₀+
        s*|Real.log (r-1)|+(s-1)*|Real.log 2| := by linarith
    _ ≤ C*(s+Real.log ((L : ℝ)+1)+1) := by
      dsimp [C]
      nlinarith [abs_nonneg (Real.log (r-1)), abs_nonneg (Real.log 2),
        mul_nonneg hC₀ hsp, mul_nonneg hC₀ hlogs,
        mul_nonneg hr2.le hlogs,
        mul_nonneg (abs_nonneg (Real.log (r-1))) hlogs,
        mul_nonneg (abs_nonneg (Real.log 2)) hlogs]

/-- The role-support cancellation with the actual clone density `λ₀=b^(r-2)μ`.
The constant depends only on the fixed uniformity. -/
theorem finite_role_support_density_cancellation (r : ℕ) (hr : 3 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L j : ℕ) (k s μ : ℝ),
      0 < j → j < L → 1 ≤ s → s ≤ L → 0 < μ →
      (j : ℝ) = k-s → (L : ℝ) = ((r : ℝ)-1)*k-s →
      |Real.log (L.choose j : ℝ) + (s-1)*Real.log 2 +
        k*Real.log ((((r : ℝ)-2)/((r : ℝ)-1))^(r-2)*μ) -
        k*Real.log (((r : ℝ)-1)*μ)| ≤ C*(s+Real.log ((L : ℝ)+1)+1) := by
  have hrR : (2 : ℝ) < r := by exact_mod_cast (show 2 < r by omega)
  obtain ⟨C, hC, hbound⟩ := finite_role_support_cancellation (r : ℝ) hrR
  refine ⟨C, hC, ?_⟩
  intro L j k s μ hj hjL hs hsL hμ hjrel hLrel
  have hr1 : (0 : ℝ) < r-1 := by linarith
  have hr2 : (0 : ℝ) < r-2 := by linarith
  have hb : (0 : ℝ) < ((r : ℝ)-2)/((r : ℝ)-1) := div_pos hr2 hr1
  have hpow : (((r : ℝ)-2)/((r : ℝ)-1))^(r-2) ≠ 0 := pow_ne_zero _ hb.ne'
  rw [Real.log_mul hpow hμ.ne', Real.log_pow,
    Real.log_mul hr1.ne' hμ.ne', Nat.cast_sub (show 2 ≤ r by omega)]
  norm_num only [Nat.cast_ofNat]
  have heq : Real.log (L.choose j : ℝ)+(s-1)*Real.log 2+
      k*(((r : ℝ)-2)*Real.log (((r : ℝ)-2)/((r : ℝ)-1))+Real.log μ)-
      k*(Real.log ((r : ℝ)-1)+Real.log μ) =
      Real.log (L.choose j : ℝ)+(s-1)*Real.log 2+
      k*((r : ℝ)-2)*Real.log (((r : ℝ)-2)/((r : ℝ)-1))-k*Real.log ((r : ℝ)-1) := by ring
  rw [heq]
  exact hbound L j k s hj hjL hs hsL hjrel hLrel

/-- Natural-number version with the manuscript's original `N,k,s` parameters. -/
theorem finite_role_support_density_cancellation_nat (r : ℕ) (hr : 3 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N k s : ℕ) (μ : ℝ),
      N = (r-1)*k+s → 1 ≤ s → s < k → s ≤ N-2*s → 0 < μ →
      |Real.log ((N-2*s).choose (k-s) : ℝ) + ((s : ℝ)-1)*Real.log 2 +
        (k : ℝ)*Real.log ((((r : ℝ)-2)/((r : ℝ)-1))^(r-2)*μ) -
        (k : ℝ)*Real.log (((r : ℝ)-1)*μ)| ≤
        C*((s : ℝ)+Real.log ((N : ℝ)+1)+1) := by
  obtain ⟨C, hC, hbound⟩ := finite_role_support_density_cancellation r hr
  refine ⟨C, hC, ?_⟩
  intro N k s μ hbook hs hsk hsL hμ
  have h2s : 2*s ≤ N := by
    have hr1 : 2 ≤ r-1 := by omega
    nlinarith
  have hbookR := congrArg (fun n : ℕ => (n : ℝ)) hbook
  push_cast [Nat.cast_sub (show 1 ≤ r by omega)] at hbookR
  have hjrel : ((k-s : ℕ) : ℝ) = (k : ℝ)-s := Nat.cast_sub hsk.le
  have hLrel : ((N-2*s : ℕ) : ℝ) = ((r : ℝ)-1)*k-s := by
    rw [Nat.cast_sub h2s]
    push_cast
    linarith
  have hj : 0 < k-s := Nat.sub_pos_of_lt hsk
  have hjL : k-s < N-2*s := by
    have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
    have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hh : ((k-s : ℕ) : ℝ) < (N-2*s : ℕ) := by
      rw [hjrel, hLrel]
      nlinarith
    exact_mod_cast hh
  have hb := hbound (N-2*s) (k-s) k s μ hj hjL (by exact_mod_cast hs)
    (by exact_mod_cast hsL) hμ hjrel hLrel
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hC
  have hlog : Real.log ((N-2*s : ℕ)+ (1 : ℝ)) ≤ Real.log ((N : ℝ)+1) := by
    apply Real.log_le_log (by positivity)
    have hh : ((N-2*s : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N (2*s)
    linarith
  linarith

end LooseHamilton
