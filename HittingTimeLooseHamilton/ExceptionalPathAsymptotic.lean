module

public import HittingTimeLooseHamilton.ProcessBergePathBound
public import HittingTimeLooseHamilton.EndpointMeanAsymptotic
public import HittingTimeLooseHamilton.ExceptionalPathExponent
public import HittingTimeLooseHamilton.ExceptionalWindowGrowth
public import HittingTimeLooseHamilton.ExceptionalSetReduction

public section

/-! Short Berge paths cannot join two exceptional vertices with appreciable
probability, simultaneously over every path of lengths one through four. -/
noncomputable section
namespace LooseHamilton
open Filter Finset
open scoped Topology BigOperators

theorem exceptional_fixed_path_tendsto_zero {r t : ℕ} (hr : 3 ≤ r) (ht : 1 ≤ t) :
    Tendsto (fun n : ℕ => (processLaw (Fin n) r).event
      (lowEndpointBergeEvent (exceptionalWindowLo r n) (exceptionalWindowHi r n) t
        (lowerDegreeBase (Fin n)))) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => (processLaw (Fin n) r).event_nonneg _)
    ?_ (exceptional_window_path_error_tendsto_zero r t)
  filter_upwards [endpoint_adjusted_mean_eventually hr t,
    endpoint_candidate_eventually (by omega : 2 ≤ r), exceptionalWindow_path_times hr t,
    eventually_ge_atTop (1 : ℕ)] with n hm hc hw hn
  have hmean := hm.2.2
  have hN : t < (completeEdges (Fin n) r).card := by
    simpa only [completeEdges_card, Fintype.card_fin] using hw.2.1
  have hhi : exceptionalWindowHi r n ≤ (completeEdges (Fin n) r).card := by
    simpa only [completeEdges_card, Fintype.card_fin] using hw.2.2
  have hfinite := process_low_endpoint_berge_bound_factored (V:=Fin n) (by omega : 2 ≤ r) ht
    (exceptionalWindowLo r n) (exceptionalWindowHi r n) (exceptionalWindowLo_le_hi r n)
    hhi hw.1 hN epsilon (by norm_num [epsilon]) (by norm_num [epsilon]) (lowerDegreeBase (Fin n))
  simp only [completeEdges_card, Fintype.card_fin] at hfinite
  have hexp := endpoint_exponential_le_rpow hn hmean
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply hfinite.trans
  calc
    _ ≤ (n : ℝ) * ((2*(r : ℝ))*Real.log n)^t *
        (n : ℝ)^(-2*exceptionalWindowRate) := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        apply pow_le_pow_left₀ (by positivity) hc
      · convert hexp using 1 <;> ring
      · positivity
      · positivity
    _ = (2*(r : ℝ))^t * ((n : ℝ)^(1-2*exceptionalWindowRate) * (Real.log n)^t) := by
      rw [show (1 : ℝ)-2*exceptionalWindowRate = 1+(-2*exceptionalWindowRate) by ring,
        Real.rpow_add hnpos, Real.rpow_one, mul_pow]
      ring

/-- Failure index four in the exact exceptional-set reduction. -/
theorem exceptional_path_failure_tendsto_zero {r : ℕ} (hr : 3 ≤ r) (C : ℝ) :
    Tendsto (fun n : ℕ => (processLaw (Fin n) r).event
      (exceptionalFailure C (exceptionalWindowLo r n) (exceptionalWindowHi r n) 4))
      atTop (𝓝 0) := by
  have hsum : Tendsto (fun n : ℕ => ∑ t : Fin 4, (processLaw (Fin n) r).event
      (lowEndpointBergeEvent (exceptionalWindowLo r n) (exceptionalWindowHi r n)
        (t.val+1) (lowerDegreeBase (Fin n)))) atTop (𝓝 0) := by
    simpa only [sum_const_zero] using tendsto_finset_sum univ
      (fun (t : Fin 4) _ => exceptional_fixed_path_tendsto_zero hr (by omega : 1 ≤ t.val+1))
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => (processLaw (Fin n) r).event_nonneg _)
    (Filter.Eventually.of_forall fun n => ?_) hsum
  have h := shortBerge_failure_probability_le_sum (V:=Fin n) (r:=r)
    (exceptionalWindowLo r n) (exceptionalWindowHi r n)
  convert h using 1
  congr 1
  funext σ
  apply propext
  simp only [exceptionalFailure, not_forall, Classical.not_imp, not_not, exists_prop]
end LooseHamilton
