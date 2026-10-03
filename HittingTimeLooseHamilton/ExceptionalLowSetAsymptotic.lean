module

public import HittingTimeLooseHamilton.ExceptionalLowSetFinite
public import HittingTimeLooseHamilton.WindowMeanAsymptotics
public import HittingTimeLooseHamilton.ExceptionalSetReduction

public section

noncomputable section
namespace LooseHamilton
open Filter Finset
open scoped Topology

/-- Concrete per-vertex early-window bound, with no probabilistic input hypothesis. -/
theorem early_low_degree_probability_eventually {r : ℕ} (hr : 3 ≤ r) :
    ∀ᶠ n : ℕ in atTop, ∀ v : Fin n,
      (processLaw (Fin n) r).event
        (fun σ => vertexDegree (processState σ (exceptionalWindowLo r n)) v ≤ lowerDegreeBase (Fin n)) ≤
        (n : ℝ) ^ (-exceptionalWindowRate) := by
  filter_upwards [exceptionalWindow_times_le_complete_eventually hr,
    exceptionalWindowLo_mean_eventually (show 1 ≤ r by omega),
    eventually_ge_atTop r, eventually_ge_atTop (1 : ℕ)] with n htime hmean hnr hn v
  apply process_low_degree_probability_le (by omega) (by omega) (exceptionalWindowLo r n)
    htime.1 (Nat.choose_pos hnr) _ v
  calc
    _ ≤ ((n - 1).choose (r - 1) : ℝ) * (exceptionalWindowLo r n : ℝ) / (n.choose r : ℝ) := hmean
    _ = _ := by ring

/-- The explicit first-moment error bound for the early exceptional-set size. -/
theorem early_low_set_size_probability_eventually {r : ℕ} (hr : 3 ≤ r) :
    ∀ᶠ n : ℕ in atTop,
      (processLaw (Fin n) r).event
        (fun σ => ¬ ((lowDegreeVertices (processState σ (exceptionalWindowLo r n))).card : ℝ) ≤
          (n : ℝ) ^ (1 / 12 : ℝ)) ≤
      (n : ℝ) ^ (1 - exceptionalWindowRate) / (n : ℝ) ^ (1 / 12 : ℝ) := by
  filter_upwards [early_low_degree_probability_eventually hr, eventually_ge_atTop (1 : ℕ)]
    with n hv hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := low_degree_set_card_probability_le (V := Fin n) (r := r)
    (exceptionalWindowLo r n) ((n : ℝ) ^ (-exceptionalWindowRate))
    ((n : ℝ) ^ (1 / 12 : ℝ)) (Real.rpow_pos_of_pos hnpos _) hv
  have heq : (n : ℝ) * (n : ℝ) ^ (-exceptionalWindowRate) = (n : ℝ) ^ (1 - exceptionalWindowRate) := by
    rw [sub_eq_add_neg, Real.rpow_add hnpos, Real.rpow_one]
  simpa only [Fintype.card_fin,heq] using h

/-- With high probability the early exceptional set has at most n^(1/12) vertices. -/
theorem early_low_set_size_failure_tendsto_zero {r : ℕ} (hr : 3 ≤ r) :
    Tendsto (fun n : ℕ => (processLaw (Fin n) r).event
      (fun σ => ¬ ((lowDegreeVertices (processState σ (exceptionalWindowLo r n))).card : ℝ) ≤
        (n : ℝ) ^ (1 / 12 : ℝ))) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => (processLaw (Fin n) r).event_nonneg _)
    (early_low_set_size_probability_eventually hr)
  exact exceptional_window_size_error_tendsto_zero

/-- Failure index 1 in the complete Lemma 3.2 reduction is negligible. -/
theorem exceptional_failure_one_tendsto_zero {r : ℕ} (hr : 3 ≤ r) (C : ℝ) :
    Tendsto (fun n : ℕ => (processLaw (Fin n) r).event
      (exceptionalFailure C (exceptionalWindowLo r n) (exceptionalWindowHi r n) 1))
      atTop (𝓝 0) := by
  have heq (n : ℕ) : exceptionalFailure (V := Fin n) (r := r) C (exceptionalWindowLo r n)
      (exceptionalWindowHi r n) 1 = (fun σ => ¬ ((lowDegreeVertices
        (processState σ (exceptionalWindowLo r n))).card : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ)) := by
    funext σ
    simp only [exceptionalFailure, Fintype.card_fin]
    rfl
  simp_rw [heq]
  exact early_low_set_size_failure_tendsto_zero hr

end LooseHamilton
