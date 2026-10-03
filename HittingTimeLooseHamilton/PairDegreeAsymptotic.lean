module

public import HittingTimeLooseHamilton.HypergraphDegreeBounds
public import HittingTimeLooseHamilton.HypergeometricInclusionBounds
public import Mathlib

public section

noncomputable section
open Filter Topology Finset
namespace LooseHamilton

lemma pair_incidence_ratio {n r : ℕ} (hr : 2 ≤ r) (hn : r ≤ n) :
    ((n-2).choose (r-2) : ℝ) / (n.choose r : ℝ) =
      (r : ℝ) * (r-1) / ((n : ℝ) * (n-1)) := by
  have h := Nat.choose_mul (n := n) hr
  have he : (n.choose r : ℝ) * (r.choose 2 : ℝ) =
      (n.choose 2 : ℝ) * ((n-2).choose (r-2) : ℝ) := by exact_mod_cast h
  rw [Nat.cast_choose_two, Nat.cast_choose_two] at he
  have hn0 : (n.choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hn))
  have hn1 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn2 : (n : ℝ) - 1 ≠ 0 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast (hr.trans hn)
    linarith
  field_simp
  nlinarith

/-- An explicit bound of order m^3/n^4 for any fixed uniformity. -/
theorem process_pair_degree_three_simple {n r m : ℕ} (hr : 2 ≤ r) (hn : r ≤ n)
    (hm : m ≤ (completeEdges (Fin n) r).card) :
    (processLaw (Fin n) r).event
      (fun σ => ∃ u v, u ≠ v ∧ 3 ≤ pairDegree (processState σ m) u v) ≤
      ((r:ℝ)*(r-1))^3 * (m:ℝ)^3 / ((n:ℝ)*(n-1))^2 := by
  have hnreal : (2:ℝ) ≤ n := by exact_mod_cast (hr.trans hn)
  have hrreal : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hmN : m ≤ n.choose r := by simpa only [completeEdges_card, Fintype.card_fin] using hm
  have hN : 0 < n.choose r := Nat.choose_pos hn
  by_cases h3 : 3 ≤ m
  · have hb := process_pair_degree_three_bound (V := Fin n) hr m hm h3
    simp only [Fintype.card_fin] at hb
    have hi := Hypergeometric.inclusion_ratio_le hmN h3 hN
    have hc : (((n-2).choose (r-2)).choose 3 : ℝ) ≤ ((n-2).choose (r-2) : ℝ)^3 := by
      exact_mod_cast Nat.choose_le_pow ((n-2).choose (r-2)) 3
    have hmul : 0 ≤ (n * (n-1) : ℕ) * (((n-2).choose (r-2)).choose 3 : ℝ) := by positivity
    calc
      _ ≤ (n*(n-1):ℕ) * (((n-2).choose (r-2)).choose 3 : ℝ) *
          (((n.choose r-3).choose (m-3) : ℝ) / (n.choose r).choose m) := by simpa [mul_div_assoc] using hb
      _ ≤ (n*(n-1):ℕ) * (((n-2).choose (r-2)).choose 3 : ℝ) * ((m:ℝ)/(n.choose r))^3 :=
        mul_le_mul_of_nonneg_left hi hmul
      _ ≤ (n*(n-1):ℕ) * ((n-2).choose (r-2):ℝ)^3 * ((m:ℝ)/(n.choose r))^3 := by
        gcongr
      _ = _ := by
        have hi := pair_incidence_ratio hr hn
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
        have ha : (n:ℝ) ≠ 0 := by linarith
        have hb : (n:ℝ)-1 ≠ 0 := by linarith
        calc
          _ = ((n:ℝ)*(n-1)) *
            (((n-2).choose (r-2):ℝ)/(n.choose r))^3 * (m:ℝ)^3 := by ring
          _ = _ := by rw [hi]; field_simp <;> ring
  · rw [(processLaw (Fin n) r).event_eq_zero_of_false (by
      rintro σ ⟨u,v,_,hv⟩
      have hc : pairDegree (processState σ m) u v ≤ m := by
        unfold pairDegree
        exact (card_filter_le _ _).trans (by rw [processState_card]; exact Nat.min_le_left _ _)
      omega)]
    apply div_nonneg
    · apply mul_nonneg
      · exact pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) _
      · positivity
    · positivity

/-- Sampling stops changing after all complete edges have appeared. -/
lemma processState_min_complete {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (σ : EdgeOrder V r) (m : ℕ) :
    processState σ (min m (completeEdges V r).card) = processState σ m := by
  apply eq_of_subset_of_card_le (processState_mono σ (Nat.min_le_left _ _))
  simp only [processState_card, Nat.min_assoc, Nat.min_self, le_refl]

/-- The same finite bound allows arbitrary times, since the process saturates. -/
theorem process_pair_degree_three_simple_all {n r m : ℕ} (hr : 2 ≤ r) (hn : r ≤ n) :
    (processLaw (Fin n) r).event
      (fun σ => ∃ u v, u ≠ v ∧ 3 ≤ pairDegree (processState σ m) u v) ≤
      ((r:ℝ)*(r-1))^3 * (m:ℝ)^3 / ((n:ℝ)*(n-1))^2 := by
  have h := process_pair_degree_three_simple hr hn
    (m := min m (completeEdges (Fin n) r).card) (Nat.min_le_right _ _)
  simp only [processState_min_complete] at h
  apply h.trans
  have hrreal : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : 0 ≤ (r:ℝ)*(r-1) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  gcongr
  exact_mod_cast Nat.min_le_left m (completeEdges (Fin n) r).card

/-- The explicit upper bound tends to zero throughout the n log n time scale. -/
theorem pair_degree_bound_tendsto {r : ℕ} {m : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto (fun n => (m n:ℝ) / ((n:ℝ)*Real.log n)) atTop (𝓝 c)) :
    Tendsto (fun n => ((r:ℝ)*(r-1))^3 * (m n:ℝ)^3 / ((n:ℝ)*(n-1))^2)
      atTop (𝓝 0) := by
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hl : Tendsto (fun n : ℕ => Real.log n ^ 3 / (n:ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero).comp hn
  have hone : Tendsto (fun n : ℕ => 1 - 1/(n:ℝ)) atTop (𝓝 (1:ℝ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
  have hratio : Tendsto (fun n : ℕ => (n:ℝ)/((n:ℝ)-1)) atTop (𝓝 (1:ℝ)) := by
    apply (show Tendsto (fun n : ℕ => (1 - 1/(n:ℝ))⁻¹) atTop (𝓝 (1:ℝ)) by simpa using hone.inv₀ one_ne_zero).congr'
    filter_upwards [eventually_ge_atTop 2] with n hnn
    have ha : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hb : (n:ℝ)-1 ≠ 0 := by
      have : (2:ℝ) ≤ n := by exact_mod_cast hnn
      linarith
    field_simp
  have hlim := (((hm.pow 3).mul hl).mul (hratio.pow 2)).const_mul (((r:ℝ)*(r-1))^3)
  apply (show Tendsto (fun n : ℕ => ((r:ℝ)*(r-1))^3 *
    (((m n:ℝ)/((n:ℝ)*Real.log n))^3 * (Real.log n^3/(n:ℝ)) *
      ((n:ℝ)/((n:ℝ)-1))^2)) atTop (𝓝 0) by simpa using hlim).congr'
  filter_upwards [eventually_ge_atTop 2] with n hnn
  have ha : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hb : (n:ℝ)-1 ≠ 0 := by
      have : (2:ℝ) ≤ n := by exact_mod_cast hnn
      linarith
  have hl : Real.log (n:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1<n)))
  field_simp <;> ring

/-- At the n log n scale, with high probability all pair degrees are at most two. -/
theorem process_pair_degree_three_tendsto_zero {r : ℕ} (hr : 2 ≤ r) {m : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto (fun n => (m n:ℝ)/((n:ℝ)*Real.log n)) atTop (𝓝 c)) :
    Tendsto (fun n => (processLaw (Fin n) r).event
      (fun σ => ∃ u v, u ≠ v ∧ 3 ≤ pairDegree (processState σ (m n)) u v))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => (processLaw (Fin n) r).event_nonneg _)
    ?_ (pair_degree_bound_tendsto (r := r) hm)
  filter_upwards [eventually_ge_atTop r] with n hn
  exact process_pair_degree_three_simple_all hr hn

end LooseHamilton
