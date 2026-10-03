module

public import HittingTimeLooseHamilton.HypergraphDegreeBounds
public import HittingTimeLooseHamilton.HypergeometricInclusionBounds
public import HittingTimeLooseHamilton.ExceptionalSetReduction
public import HittingTimeLooseHamilton.WindowMeanAsymptotics
public import Mathlib

public section

/-! A logarithmic maximum-degree bound at the upper comparison time. -/
noncomputable section
namespace LooseHamilton
open Finset Filter
open scoped Topology

private lemma binomial_term_exp_bound (D k : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (D.choose k : ℝ) * ρ^k ≤ Real.exp (2 * D * ρ) / 2^k := by
  have ht : (D.choose k : ℝ) * (2*ρ)^k ≤ (2*ρ+1)^D := by
    by_cases hk : k ≤ D
    · rw [add_pow]
      have h := single_le_sum (f := fun i => (2*ρ)^i * (1:ℝ)^(D-i) * (D.choose i : ℝ))
        (fun i _ => by positivity) (mem_range.mpr (by omega : k < D+1))
      simpa only [one_pow,mul_one,one_mul,mul_comm] using h
    · rw [Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero,zero_mul]
      positivity
  have he : (2*ρ+1)^D ≤ Real.exp (2*D*ρ) := by
    calc
      _ ≤ (Real.exp (2*ρ))^D := pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _ ) D
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2^k)).mpr
  calc
    (D.choose k : ℝ) * ρ^k * 2^k = (D.choose k : ℝ) * (2*ρ)^k := by rw [mul_pow]; ring
    _ ≤ _ := ht.trans he

/-- A finite exponential upper bound, valid also when the threshold exceeds the number of edges. -/
theorem process_maximum_degree_exp_bound {n r m k : ℕ} (hr : 1 ≤ r) (hn : r ≤ n)
    (hm : m ≤ (completeEdges (Fin n) r).card) :
    (processLaw (Fin n) r).event
      (fun σ => ∃ v, k ≤ vertexDegree (processState σ m) v) ≤
      (n : ℝ) * Real.exp (2 * (((n-1).choose (r-1) : ℝ) * m / (n.choose r))) / 2^k := by
  by_cases hk : k ≤ m
  · have hb := process_maximum_degree_tail (V := Fin n) hr m k hm hk
    simp only [Fintype.card_fin] at hb
    have hm' : m ≤ n.choose r := by simpa only [completeEdges_card,Fintype.card_fin] using hm
    have hi := Hypergeometric.inclusion_ratio_le hm' hk (Nat.choose_pos hn)
    have ht := binomial_term_exp_bound ((n-1).choose (r-1)) k
      ((m:ℝ)/(n.choose r)) (by positivity)
    calc
      _ ≤ (n:ℝ) * (((n-1).choose (r-1)).choose k : ℝ) *
          (((n.choose r-k).choose (m-k) : ℝ) / (n.choose r).choose m) := by
            simpa only [mul_div_assoc] using hb
      _ ≤ (n:ℝ) * (((n-1).choose (r-1)).choose k : ℝ) * ((m:ℝ)/(n.choose r))^k :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ ≤ (n:ℝ) * (Real.exp (2 * ((n-1).choose (r-1)) * ((m:ℝ)/(n.choose r))) / 2^k) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n)
      _ = _ := by
        rw [show (2:ℝ) * ((n-1).choose (r-1)) * ((m:ℝ)/(n.choose r)) =
          2 * (((n-1).choose (r-1) : ℝ) * m / (n.choose r)) by ring]
        ring
  · rw [(processLaw (Fin n) r).event_eq_zero_of_false (by
      rintro σ ⟨v,hv⟩
      have hd : vertexDegree (processState σ m) v ≤ m :=
        (card_filter_le _ _).trans (by rw [processState_card]; exact Nat.min_le_left _ _)
      omega)]
    positivity

/-- A mean of at most `2 log n` gives a concrete inverse-n failure bound. -/
theorem process_maximum_degree_log_bound {n r m : ℕ} (hr : 1 ≤ r) (hn : r ≤ n)
    (hn2 : 2 ≤ n) (hm : m ≤ (completeEdges (Fin n) r).card)
    (hmean : ((n-1).choose (r-1) : ℝ) * m / (n.choose r) ≤ 2 * Real.log n) :
    (processLaw (Fin n) r).event
      (fun σ => ¬ ∀ v, (vertexDegree (processState σ m) v : ℝ) ≤ 20 * Real.log n) ≤
      1 / (n : ℝ) := by
  classical
  let k := Nat.floor (20 * Real.log (n:ℝ)) + 1
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
  have hm1 : (processLaw (Fin n) r).event
      (fun σ => ¬ ∀ v, (vertexDegree (processState σ m) v : ℝ) ≤ 20 * Real.log n) ≤
      (processLaw (Fin n) r).event (fun σ => ∃ v, k ≤ vertexDegree (processState σ m) v) := by
    apply FiniteEntropy.Law.event_mono
    intro σ h
    obtain ⟨v,hv⟩ := not_forall.mp h
    have hv' := (Nat.floor_lt (by positivity : (0:ℝ) ≤ 20*Real.log (n:ℝ))).mpr (lt_of_not_ge hv)
    exact ⟨v,by omega⟩
  apply (hm1.trans (process_maximum_degree_exp_bound hr hn hm)).trans
  have hk : 20 * Real.log (n:ℝ) < (k:ℝ) := by
    simpa only [k,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (20*Real.log (n:ℝ))
  have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hkl : (k:ℝ) * (1/2:ℝ) ≤ (k:ℝ)*Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg k)
  have hpow : (2:ℝ)^k = Real.exp ((k:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  calc
    _ = Real.exp (Real.log n + 2 * (((n-1).choose (r-1) : ℝ) * m / (n.choose r)) -
        (k:ℝ)*Real.log 2) := by
      rw [Real.exp_sub,Real.exp_add,Real.exp_log hnpos,←hpow]
    _ ≤ Real.exp (-Real.log n) := Real.exp_le_exp.mpr (by nlinarith)
    _ = 1/(n:ℝ) := by rw [Real.exp_neg,Real.exp_log hnpos]; simp

/-- The maximum-degree estimate follows once the deterministic comparison time
is valid and has the required mean bound eventually. -/
theorem maximum_degree_probability_tendsto {r : ℕ} (hr : 1 ≤ r) (m : ℕ → ℕ)
    (hm : ∀ᶠ n : ℕ in atTop, m n ≤ (completeEdges (Fin n) r).card)
    (hmean : ∀ᶠ n : ℕ in atTop,
      ((n-1).choose (r-1) : ℝ) * m n / (n.choose r) ≤ 2 * Real.log n) :
    Tendsto (fun n : ℕ => (processLaw (Fin n) r).event
      (fun σ => ¬ ∀ v, (vertexDegree (processState σ (m n)) v : ℝ) ≤ 20 * Real.log n))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n => (processLaw (Fin n) r).event_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
  filter_upwards [hm,hmean,eventually_ge_atTop r,eventually_ge_atTop (2:ℕ)] with n hm hmean hnr hn2
  exact process_maximum_degree_log_bound hr hnr hn2 hm hmean

/-- Actual maximum-degree failure at the upper isolated-vertex comparison time
has probability tending to zero. -/
theorem exceptionalWindow_maximum_degree_tendsto {r : ℕ} (hr : 3 ≤ r) :
    Tendsto (fun n : ℕ => (processLaw (Fin n) r).event
      (fun σ => ¬ ∀ v, (vertexDegree (processState σ (exceptionalWindowHi r n)) v : ℝ) ≤
        20 * Real.log n)) atTop (𝓝 0) := by
  have hr1 : 1 ≤ r := by omega
  apply maximum_degree_probability_tendsto hr1 (exceptionalWindowHi r)
  · filter_upwards [exceptionalWindow_times_le_complete_eventually hr] with n hn
    simpa only [completeEdges_card,Fintype.card_fin] using hn.2
  · have h := (exceptionalWindowHi_mean_ratio_tendsto hr1).eventually
      (gt_mem_nhds (by norm_num : (101/100:ℝ)<2))
    filter_upwards [h,eventually_ge_atTop (2:ℕ)] with n hn hn2
    have hlog : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
    exact le_of_lt ((div_lt_iff₀ hlog).mp hn)

/-- Failure index 2 in the complete exceptional-set reduction. -/
theorem exceptionalFailure_maximum_degree_tendsto {r : ℕ} (hr : 3 ≤ r) :
    Tendsto (fun n : ℕ => (processLaw (Fin n) r).event
      (exceptionalFailure 20 (exceptionalWindowLo r n) (exceptionalWindowHi r n) 2))
      atTop (𝓝 0) := by
  have he (n : ℕ) : exceptionalFailure (V := Fin n) (r := r) 20
      (exceptionalWindowLo r n) (exceptionalWindowHi r n) 2 =
      (fun σ => ¬ ∀ v, (vertexDegree (processState σ (exceptionalWindowHi r n)) v : ℝ) ≤
        20 * Real.log n) := by
    funext σ
    simp only [exceptionalFailure,Fintype.card_fin]
  simpa only [he] using exceptionalWindow_maximum_degree_tendsto hr

end LooseHamilton
