module

public import HittingTimeLooseHamilton.ExceptionalWindowScales

public section
noncomputable section
namespace LooseHamilton
open Filter

lemma vertex_incidence_ratio {n r : ℕ} (hr : 1 ≤ r) (hn : r ≤ n) :
    ((n-1).choose (r-1) : ℝ) / (n.choose r : ℝ) = (r : ℝ) / n := by
  have h := Nat.choose_mul (n := n) hr
  have he : (n.choose r : ℝ) * (r : ℝ) =
      (n : ℝ) * ((n-1).choose (r-1) : ℝ) := by
    exact_mod_cast (by simpa only [Nat.choose_one_right] using h)
  have hN : (n.choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hn))
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp
  nlinarith

/-- Expected vertex degree at an arbitrary deterministic comparison time. -/
@[expose] def isolationMean (r : ℕ) (m : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((n-1).choose (r-1) : ℝ) * (m n : ℝ) / (n.choose r : ℝ)

lemma isolationMean_normalized {n r : ℕ} (hr : 1 ≤ r) (hn : r ≤ n) (m : ℕ → ℕ) :
    isolationMean r m n / Real.log n = (r : ℝ) * ((m n : ℝ) / ((n : ℝ) * Real.log n)) := by
  unfold isolationMean
  calc
    _ = (((n-1).choose (r-1) : ℝ) / (n.choose r : ℝ)) * (m n : ℝ) / Real.log n := by ring
    _ = _ := by rw [vertex_incidence_ratio hr hn]; ring

lemma isolationMean_ratio_tendsto {r : ℕ} (hr : 1 ≤ r) {m : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto (fun n => (m n : ℝ) / ((n : ℝ) * Real.log n)) atTop (nhds c)) :
    Tendsto (fun n => isolationMean r m n / Real.log n) atTop (nhds ((r : ℝ) * c)) := by
  apply (hm.const_mul (r : ℝ)).congr'
  filter_upwards [eventually_ge_atTop r] with n hn
  exact (isolationMean_normalized hr hn m).symm

lemma exceptionalWindowLo_mean_ratio_tendsto {r : ℕ} (hr : 1 ≤ r) :
    Tendsto (fun n => isolationMean r (exceptionalWindowLo r) n / Real.log n)
      atTop (nhds (99 / 100 : ℝ)) := by
  have h := isolationMean_ratio_tendsto hr (exceptionalWindowLo_ratio_tendsto r)
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  convert h using 1 <;> field_simp <;> ring

lemma exceptionalWindowHi_mean_ratio_tendsto {r : ℕ} (hr : 1 ≤ r) :
    Tendsto (fun n => isolationMean r (exceptionalWindowHi r) n / Real.log n)
      atTop (nhds (101 / 100 : ℝ)) := by
  have h := isolationMean_ratio_tendsto hr (exceptionalWindowHi_ratio_tendsto r)
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  convert h using 1 <;> field_simp <;> ring

lemma exceptionalWindowLo_mean_eventually {r : ℕ} (hr : 1 ≤ r) :
    ∀ᶠ n : ℕ in atTop, (98 / 100 : ℝ) * Real.log n ≤
      ((n-1).choose (r-1) : ℝ) * (exceptionalWindowLo r n : ℝ) / (n.choose r : ℝ) := by
  have h := (exceptionalWindowLo_mean_ratio_tendsto hr).eventually
    (lt_mem_nhds (by norm_num : (98 / 100 : ℝ) < 99 / 100))
  filter_upwards [h,eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  exact le_of_lt ((lt_div_iff₀ hlog).mp hn)
end LooseHamilton
