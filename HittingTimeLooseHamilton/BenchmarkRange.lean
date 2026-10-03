module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

public section

/-! Uniform eventual elementary inequalities in the logarithmic benchmark range. -/

open Filter

namespace LooseHamilton

/-- The manuscript's sublinear marker bound implies all the finite range conditions
needed by the counting and logarithmic estimates, uniformly in `k`, `s`, and `j`.
Only the threshold is allowed to depend on the density constant `c`. -/
theorem benchmark_range_eventually (r : ℕ) (hr : 3 ≤ r) (c : ℝ) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k s j : ℕ,
      N = (r - 1) * k + s → 1 ≤ s →
      (s : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
      c * N * Real.log N ≤ j →
      2 * r ≤ N ∧ 3 ≤ k ∧ 2 * s ≤ k ∧ 1 ≤ j ∧
      1 ≤ Real.log N ∧ (k : ℝ) / j ≤ 1 := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(9 / 10 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 9 / 10)).comp
      tendsto_natCast_atTop_atTop
  have he : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(9 / 10 : ℝ)) < 1 / (4 * r) :=
    ht.eventually (gt_mem_nhds (by positivity))
  have hlog : ∀ᶠ N : ℕ in atTop, max 1 (1 / c) ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  have hall : ∀ᶠ N : ℕ in atTop,
      12 * r ≤ N ∧ (N : ℝ) ^ (-(9 / 10 : ℝ)) < 1 / (4 * r) ∧
      max 1 (1 / c) ≤ Real.log N := by
    filter_upwards [eventually_ge_atTop (12 * r), he, hlog] with N hN he hl
    exact ⟨hN, he, hl⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hall
  refine ⟨N₀, ?_⟩
  intro N hN k s j hsize hs hsbound hj
  obtain ⟨hlarge, hpow, hlog⟩ := hN₀ N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow' : (N : ℝ) ^ (1 / 10 : ℝ) / N < 1 / (4 * r) := by
    convert hpow using 1
    rw [← Real.rpow_sub_one (ne_of_gt hNpos)]
    norm_num
  have hsN : (4 : ℝ) * r * s ≤ N := by
    have hp := (div_lt_iff₀ hNpos).1 hpow'
    have hp' := (lt_div_iff₀ (show (0 : ℝ) < 4 * r by positivity)).1
      (show (N : ℝ) ^ (1 / 10 : ℝ) < N / (4 * r) by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hp)
    have hmul := mul_le_mul_of_nonneg_left hsbound
      (show (0 : ℝ) ≤ 4 * r by positivity)
    nlinarith
  have hsizeR : (N : ℝ) = ((r : ℝ) - 1) * k + s := by
    have ht : (N : ℝ) = ((r - 1 : ℕ) : ℝ) * k + s := by exact_mod_cast hsize
    simpa only [Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_one] using ht
  have hlargeR : (12 : ℝ) * r ≤ N := by exact_mod_cast hlarge
  have hk : 3 ≤ k := by
    by_contra! hkbad
    have hkR : (k : ℝ) ≤ 2 := by exact_mod_cast (show k ≤ 2 by omega)
    have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
    have hm := mul_le_mul_of_nonneg_left hkR (show 0 ≤ (r : ℝ) - 1 by linarith)
    have hspos : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    have hmS := mul_le_mul_of_nonneg_right hrR hspos
    nlinarith
  have hsk : 2 * s ≤ k := by
    have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
    have : (2 : ℝ) * s ≤ k := by
      by_contra! hh
      have hm := mul_lt_mul_of_pos_left hh (show 0 < (r : ℝ) - 1 by linarith)
      have hspos : (0 : ℝ) ≤ s := Nat.cast_nonneg _
      have hmS := mul_nonneg hrpos.le hspos
      nlinarith
    exact_mod_cast this
  have hkN : k ≤ N := by
    have hr1 : 1 ≤ r - 1 := by omega
    have : k ≤ (r - 1) * k := by nlinarith
    omega
  have hclog : 1 ≤ c * Real.log N := by
    have := (le_max_right (1 : ℝ) (1 / c)).trans hlog
    exact (div_le_iff₀ hc).1 this |>.trans_eq (mul_comm _ _)
  have hNj : (N : ℝ) ≤ j := by nlinarith
  have hjpos : (0 : ℝ) < j := hNpos.trans_le hNj
  have hjnat : 1 ≤ j := by exact_mod_cast (show (1 : ℝ) ≤ j by
    have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    linarith)
  refine ⟨by omega, hk, hsk, hjnat, (le_max_left _ _).trans hlog, ?_⟩
  apply (div_le_one hjpos).2
  exact (by exact_mod_cast hkN : (k : ℝ) ≤ N).trans hNj

end LooseHamilton
