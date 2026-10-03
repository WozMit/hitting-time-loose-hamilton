module

public import HittingTimeLooseHamilton.WindowMeanAsymptotics
public import HittingTimeLooseHamilton.PairDegreeAsymptotic

public section

noncomputable section
open Filter Topology
namespace LooseHamilton

lemma nat_div_choose_tendsto_zero {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun n : ℕ => (n:ℝ)/(n.choose r:ℝ)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => ((n:ℝ)*Real.log n)/(n.choose r:ℝ)) atTop (𝓝 0) := by
    have h := (nat_mul_log_div_pow_tendsto_zero hr).div (normalized_nat_choose_tendsto r)
      (by positivity : (1:ℝ)/(r.factorial:ℝ) ≠ 0)
    apply (show Tendsto (fun n : ℕ => (((n:ℝ)*Real.log n)/(n:ℝ)^r)/
      ((n.choose r:ℝ)/(n:ℝ)^r)) atTop (𝓝 0) by convert h using 1 <;> simp).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
  have hlog : Tendsto (fun n : ℕ => (1:ℝ)/Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply (show Tendsto (fun n : ℕ => (((n:ℝ)*Real.log n)/(n.choose r:ℝ)) *
    (1/Real.log n)) atTop (𝓝 0) by simpa using h0.mul hlog).congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hl : Real.log (n:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1<n)))
  by_cases hN : (n.choose r:ℝ) = 0
  · simp [hN]
  · field_simp [hl,hN] <;> ring

lemma exclusive_incidence_ratio {n r : ℕ} (hr : 2 ≤ r) (hn : r ≤ n) :
    ((n-2).choose (r-1):ℝ)/(n.choose r:ℝ) =
      (r:ℝ)/n - (r:ℝ)*(r-1)/((n:ℝ)*(n-1)) := by
  have hs : (n-1).choose (r-1) = (n-2).choose (r-1) + (n-2).choose (r-2) := by
    have hh := Nat.choose_succ_succ (n-2) (r-2)
    simp only [Nat.succ_eq_add_one] at hh
    rw [show n-2+1=n-1 by omega, show r-2+1=r-1 by omega] at hh
    omega
  have he : ((n-1).choose (r-1):ℝ) = ((n-2).choose (r-1):ℝ)+((n-2).choose (r-2):ℝ) := by exact_mod_cast hs
  rw [← vertex_incidence_ratio (by omega) hn, ← pair_incidence_ratio hr hn, he]
  ring

lemma exclusive_support_ratio_tendsto {r : ℕ} (hr : 2 ≤ r) (t : ℕ) :
    Tendsto (fun n : ℕ => (n:ℝ)*((2*((n-2).choose (r-1)):ℕ):ℝ)/(n.choose r:ℝ) -
      (t:ℝ)*(n:ℝ)/(n.choose r:ℝ)) atTop (𝓝 (2*(r:ℝ))) := by
  have hinv : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)-1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (show Tendsto (fun n : ℕ => (n:ℝ)-1) atTop atTop by
        simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1:ℝ) tendsto_natCast_atTop_atTop)
  have hmain : Tendsto (fun n : ℕ => 2*(r:ℝ)-2*((r:ℝ)*(r-1))* (1/((n:ℝ)-1)))
      atTop (𝓝 (2*(r:ℝ))) := by simpa using tendsto_const_nhds.sub (hinv.const_mul (2*((r:ℝ)*(r-1))))
  have hsub := hmain.sub ((nat_div_choose_tendsto_zero hr).const_mul (t:ℝ))
  apply (show Tendsto (fun n : ℕ =>
    (2*(r:ℝ)-2*((r:ℝ)*(r-1))*(1/((n:ℝ)-1))) - (t:ℝ)*((n:ℝ)/(n.choose r:ℝ)))
    atTop (𝓝 (2*(r:ℝ))) by simpa using hsub).congr'
  filter_upwards [eventually_ge_atTop r] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n:ℝ)-1 ≠ 0 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast (hr.trans hn)
    linarith
  rw [Nat.cast_mul, Nat.cast_ofNat]
  symm
  calc
    _ = 2*(n:ℝ)*(((n-2).choose (r-1):ℝ)/(n.choose r:ℝ)) -
      (t:ℝ)*(n:ℝ)/(n.choose r:ℝ) := by ring
    _ = _ := by rw [exclusive_incidence_ratio hr hn]; field_simp [hn0,hn1] <;> ring

lemma endpoint_surrogate_ratio_tendsto {r : ℕ} (hr : 2 ≤ r) (t : ℕ) :
    Tendsto (fun n : ℕ => (((exceptionalWindowLo r n:ℕ):ℝ)-(t:ℝ)) /
      (n.choose r:ℝ) * (((2*((n-2).choose (r-1)):ℕ):ℝ)-(t:ℝ)) / Real.log n)
      atTop (𝓝 (198/100:ℝ)) := by
  have ht : Tendsto (fun n : ℕ => (t:ℝ)/((n:ℝ)*Real.log n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_nat_mul_log_atTop
  have ha := (exceptionalWindowLo_ratio_tendsto r).sub ht
  have h := ha.mul (exclusive_support_ratio_tendsto hr t)
  have hr0 : (r:ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have he : ((99/100:ℝ)/r - 0)*(2*(r:ℝ)) = 198/100 := by field_simp <;> ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hl : Real.log (n:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1<n)))
  by_cases hN : (n.choose r:ℝ) = 0
  · simp [hN]
  · field_simp [hn0,hl,hN] <;> ring

lemma endpoint_candidate_ratio_tendsto {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun n : ℕ => (n:ℝ)*((n-2).choose (r-2):ℝ)*
      ((exceptionalWindowHi r n:ℝ)/(n.choose r:ℝ))/Real.log n)
      atTop (𝓝 ((101/100:ℝ)*((r:ℝ)-1))) := by
  have hnratio : Tendsto (fun n : ℕ => (n:ℝ)/((n:ℝ)-1)) atTop (𝓝 (1:ℝ)) := by
    have hi : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)-1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (show Tendsto (fun n : ℕ => (n:ℝ)-1) atTop atTop by
        simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1:ℝ) tendsto_natCast_atTop_atTop)
    apply (show Tendsto (fun n : ℕ => 1 + 1/((n:ℝ)-1)) atTop (𝓝 (1:ℝ)) by simpa using tendsto_const_nhds.add hi).congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn1 : (n:ℝ)-1 ≠ 0 := by
      have : (2:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    field_simp [hn1] <;> ring
  have h := ((exceptionalWindowHi_ratio_tendsto r).mul hnratio).const_mul ((r:ℝ)*(r-1))
  have hr0 : (r:ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have he : ((r:ℝ)*(r-1))*((101/100/r)*1) = (101/100)*(r-1) := by field_simp <;> ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop r] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  symm
  calc
    _ = (n:ℝ)*(((n-2).choose (r-2):ℝ)/(n.choose r:ℝ))*
      (exceptionalWindowHi r n:ℝ)/Real.log n := by ring
    _ = _ := by
      rw [pair_incidence_ratio hr hn]
      field_simp [hn0] <;> ring

lemma endpoint_candidate_eventually {r : ℕ} (hr : 2 ≤ r) :
    ∀ᶠ n : ℕ in atTop, (n:ℝ)*((n-2).choose (r-2):ℝ)*
      ((exceptionalWindowHi r n:ℝ)/(n.choose r:ℝ)) ≤ (2*(r:ℝ))*Real.log n := by
  have hrreal : (2:ℝ) ≤ r := by exact_mod_cast hr
  have h := (endpoint_candidate_ratio_tendsto hr).eventually
    (gt_mem_nhds (by nlinarith : (101/100:ℝ)*((r:ℝ)-1) < 2*(r:ℝ)))
  filter_upwards [h,eventually_ge_atTop 2] with n hn hn2
  have hl : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<n))
  exact le_of_lt ((div_lt_iff₀ hl).mp hn)

lemma exceptionalWindowLo_tendsto_atTop {r : ℕ} (hr : 1 ≤ r) :
    Tendsto (exceptionalWindowLo r) atTop atTop := by
  have hrreal : (0:ℝ) < r := by exact_mod_cast (by omega : 0<r)
  have h := (exceptionalWindowLo_ratio_tendsto r).pos_mul_atTop
    (by positivity : (0:ℝ) < 99/100/(r:ℝ)) tendsto_nat_mul_log_atTop
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n≠0)
  have hl : Real.log (n:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1<n)))
  field_simp

/-- Deleting any fixed number of prescribed edges leaves a pair-support mean
at least 1.96 log n throughout the early comparison window. -/
lemma endpoint_adjusted_mean_eventually {r : ℕ} (hr : 3 ≤ r) (t : ℕ) :
    ∀ᶠ n : ℕ in atTop, t ≤ exceptionalWindowLo r n ∧ t < n.choose r ∧
      (196/100:ℝ)*Real.log n ≤
        ((exceptionalWindowLo r n-t:ℕ):ℝ)/((n.choose r-t:ℕ):ℝ)*
          ((2*((n-2).choose (r-1))-t:ℕ):ℝ) := by
  have hs := (endpoint_surrogate_ratio_tendsto (by omega : 2≤r) t).eventually
    (lt_mem_nhds (by norm_num : (196/100:ℝ)<198/100))
  have ha := (exceptionalWindowLo_tendsto_atTop (by omega : 1≤r)).eventually
    (eventually_ge_atTop (t+1))
  filter_upwards [hs,ha,exceptionalWindow_times_le_complete_eventually hr,
    eventually_ge_atTop 2] with n hs ha hvalid hn2
  have hta : t ≤ exceptionalWindowLo r n := by omega
  have htN : t < n.choose r := by omega
  have hN : (0:ℝ)<n.choose r := by exact_mod_cast (by omega : 0<n.choose r)
  have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<n))
  have hal : 0 ≤ (exceptionalWindowLo r n:ℝ)-(t:ℝ) := sub_nonneg.mpr (Nat.cast_le.mpr hta)
  have hlow := (lt_div_iff₀ hl).mp hs
  have hsupport : 0 ≤ ((2*((n-2).choose (r-1)):ℕ):ℝ)-(t:ℝ) := by
    by_contra hh
    have hhneg := lt_of_not_ge hh
    have hz := mul_nonpos_of_nonneg_of_nonpos (div_nonneg hal (le_of_lt hN)) (le_of_lt hhneg)
    have : 0 < (196/100:ℝ)*Real.log n := mul_pos (by norm_num) hl
    linarith
  have hts : t ≤ 2*((n-2).choose (r-1)) := Nat.cast_le.mp (sub_nonneg.mp hsupport)
  refine ⟨hta,htN,le_trans (le_of_lt hlow) ?_⟩
  rw [Nat.cast_sub hta, Nat.cast_sub hts]
  apply mul_le_mul_of_nonneg_right ?_ hsupport
  apply div_le_div_of_nonneg_left hal
  · exact_mod_cast (Nat.sub_pos_of_lt htN)
  · exact_mod_cast Nat.sub_le (n.choose r) t
end LooseHamilton
