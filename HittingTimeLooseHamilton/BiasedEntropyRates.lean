module

public import HittingTimeLooseHamilton.BiasedEntropyDeficits
public import HittingTimeLooseHamilton.ExceptionalSetAsymptotics

public section

noncomputable section
open Filter
namespace FiniteEntropy

/-- Fixed multiplicative comparison survives any nonnegative real power. -/
lemma comparable_rpow_bound {eta zeta C alpha : ℝ}
    (heta : 0 ≤ eta) (hzeta : 0 ≤ zeta) (hC : 0 ≤ C)
    (halpha : 0 ≤ alpha) (hcomp : zeta ≤ C * eta) :
    zeta ^ alpha ≤ C ^ alpha * eta ^ alpha := by
  simpa only [Real.mul_rpow hC heta] using Real.rpow_le_rpow hzeta hcomp halpha

/-- A finite quantitative inverse-log comparison. Smallness of eta is stated
explicitly, so this can be used before passing to eventual bounds. -/
lemma comparable_inverse_log_bound {eta zeta C : ℝ}
    (heta : 0 < eta) (heta1 : eta < 1) (hzeta : 0 < zeta) (hC : 0 < C)
    (hcomp : zeta ≤ C * eta)
    (hsmall : 2 * Real.log C ≤ Real.log (1 / eta)) :
    0 < Real.log (1 / zeta) ∧
      1 / Real.log (1 / zeta) ≤ 2 / Real.log (1 / eta) := by
  have hlpos : 0 < Real.log (1 / eta) := by
    apply Real.log_pos
    exact (lt_div_iff₀ heta).2 (by linarith)
  have hlog := Real.log_le_log hzeta hcomp
  rw [Real.log_mul hC.ne' heta.ne'] at hlog
  have he : Real.log (1 / eta) = -Real.log eta := by rw [one_div, Real.log_inv]
  have hz : Real.log (1 / zeta) = -Real.log zeta := by rw [one_div, Real.log_inv]
  have hhalf : Real.log (1 / eta) / 2 ≤ Real.log (1 / zeta) := by
    rw [he] at hsmall ⊢
    rw [hz]
    linarith
  have hzpos : 0 < Real.log (1 / zeta) := by linarith
  refine ⟨hzpos, ?_⟩
  apply (div_le_div_iff₀ hzpos hlpos).2
  linarith

/-- If eta tends to zero and zeta is eventually positive and at most a fixed
multiple of eta, the inverse-log error loses at most a factor two. -/
theorem eventually_comparable_inverse_log_bound {eta zeta : ℕ → ℝ} {C : ℝ}
    (heta : Tendsto eta atTop (nhds 0))
    (heta_pos : ∀ᶠ n in atTop, 0 < eta n)
    (hzeta_pos : ∀ᶠ n in atTop, 0 < zeta n) (hC : 0 < C)
    (hcomp : ∀ᶠ n in atTop, zeta n ≤ C * eta n) :
    ∀ᶠ n in atTop, 0 < Real.log (1 / zeta n) ∧
      1 / Real.log (1 / zeta n) ≤ 2 / Real.log (1 / eta n) := by
  have hsmall := (tendsto_order.mp heta).2 (Real.exp (-2 * Real.log C)) (Real.exp_pos _)
  have hone := (tendsto_order.mp heta).2 1 (by norm_num)
  filter_upwards [heta_pos, hzeta_pos, hcomp, hsmall, hone] with n hen hzn hcn hsn hon
  apply comparable_inverse_log_bound hen hon hzn hC hcn
  have hlog := (Real.log_lt_iff_lt_exp hen).2 hsn
  rw [one_div, Real.log_inv]
  linarith

/-- The power comparison as a big-O statement, with an explicit witness C^alpha. -/
theorem comparable_rpow_isBigO {eta zeta : ℕ → ℝ} {C alpha : ℝ}
    (heta : ∀ᶠ n in atTop, 0 ≤ eta n)
    (hzeta : ∀ᶠ n in atTop, 0 ≤ zeta n) (hC : 0 ≤ C)
    (halpha : 0 ≤ alpha) (hcomp : ∀ᶠ n in atTop, zeta n ≤ C * eta n) :
    Asymptotics.IsBigO atTop (fun n => zeta n ^ alpha) (fun n => eta n ^ alpha) := by
  apply Asymptotics.isBigO_iff.2
  refine ⟨C ^ alpha, ?_⟩
  filter_upwards [heta, hzeta, hcomp] with n hen hzn hcn
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hzn alpha),
    abs_of_nonneg (Real.rpow_nonneg hen alpha)]
  exact comparable_rpow_bound hen hzn hC halpha hcn

/-- Both components of the entropy-error rate transfer under a fixed
multiplicative comparison, with an explicit constant. -/
theorem eventually_comparable_entropy_rate {eta zeta : ℕ → ℝ} {C alpha : ℝ}
    (heta : Tendsto eta atTop (nhds 0))
    (heta_pos : ∀ᶠ n in atTop, 0 < eta n)
    (hzeta_pos : ∀ᶠ n in atTop, 0 < zeta n) (hC : 0 < C)
    (halpha : 0 ≤ alpha) (hcomp : ∀ᶠ n in atTop, zeta n ≤ C * eta n) :
    ∀ᶠ n in atTop,
      zeta n ^ alpha + 1 / Real.log (1 / zeta n) ≤
        (C ^ alpha + 2) * (eta n ^ alpha + 1 / Real.log (1 / eta n)) := by
  have hlog := eventually_comparable_inverse_log_bound heta heta_pos hzeta_pos hC hcomp
  have hone := (tendsto_order.mp heta).2 1 (by norm_num)
  filter_upwards [heta_pos, hzeta_pos, hcomp, hlog, hone] with n hen hzn hcn hln hon
  have hp := comparable_rpow_bound hen.le hzn.le hC.le halpha hcn
  have hbase : 0 < Real.log (1 / eta n) :=
    Real.log_pos ((lt_div_iff₀ hen).2 (by linarith))
  have hinv : 0 ≤ 1 / Real.log (1 / eta n) := le_of_lt (one_div_pos.mpr hbase)
  have hcp := Real.rpow_nonneg hC.le alpha
  have hep := Real.rpow_nonneg hen.le alpha
  have hl := hln.2
  have hextra := mul_nonneg hcp hinv
  have htwo : 2 / Real.log (1 / eta n) = 2 * (1 / Real.log (1 / eta n)) := by ring
  rw [htwo] at hl
  nlinarith

/-- Rounding the auxiliary maximum degree adds at most one copy of the mean
once the mean is at least one. -/
lemma ceil_degree_bound {K mu : ℝ} (hK : 0 ≤ K) (hmu : 1 ≤ mu) :
    (⌈K * mu⌉₊ : ℝ) ≤ (K + 1) * mu := by
  have h := Nat.ceil_lt_add_one (mul_nonneg hK (by linarith : 0 ≤ mu))
  nlinarith

/-- The rounded-degree comparison holds eventually when the mean diverges. -/
theorem eventually_ceil_degree_bound {mu : ℕ → ℝ} {K : ℝ}
    (hmu : Tendsto mu atTop atTop) (hK : 0 ≤ K) :
    ∀ᶠ n in atTop, (⌈K * mu n⌉₊ : ℝ) ≤ (K + 1) * mu n := by
  filter_upwards [hmu.eventually (eventually_ge_atTop 1)] with n hn
  exact ceil_degree_bound hK hn

end FiniteEntropy
