module

public import HittingTimeLooseHamilton.NormalizationFormula
public import Mathlib

public section

set_option maxHeartbeats 1000000
noncomputable section
open Filter Topology
namespace LooseHamilton

/-- Dividing a fixed descending factorial by the corresponding power gives
one asymptotically. The scale and the argument may be different sequences. -/
theorem normalized_descFactorial_tendsto {A N : ℕ → ℕ} {c : ℝ}
    (hA : Tendsto A atTop atTop) (hN : Tendsto N atTop atTop)
    (hAN : Tendsto (fun n => (A n : ℝ) / N n) atTop (𝓝 c)) (d : ℕ) :
    Tendsto (fun n => ((A n).descFactorial d : ℝ) / (N n : ℝ)^d)
      atTop (𝓝 (c^d)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hd : Tendsto (fun n => (d : ℝ) / N n) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (d : ℝ)).comp hN
    have hs : Tendsto (fun n => ((A n - d : ℕ) : ℝ) / N n) atTop (𝓝 c) := by
      apply (show Tendsto (fun n => (A n : ℝ) / N n - (d : ℝ) / N n) atTop (𝓝 c) by simpa using hAN.sub hd).congr'
      filter_upwards [hA.eventually (eventually_ge_atTop d)] with n hn
      simp [Nat.cast_sub hn, sub_div]
    convert hs.mul ih using 1
    · ext n
      rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
      ring_nf
    · ring_nf

/-- The same normalization for binomial coefficients. -/
theorem normalized_choose_tendsto {A N : ℕ → ℕ} {c : ℝ}
    (hA : Tendsto A atTop atTop) (hN : Tendsto N atTop atTop)
    (hAN : Tendsto (fun n => (A n : ℝ) / N n) atTop (𝓝 c)) (d : ℕ) :
    Tendsto (fun n => ((A n).choose d : ℝ) / (N n : ℝ)^d)
      atTop (𝓝 (c^d / d.factorial)) := by
  have h := (normalized_descFactorial_tendsto hA hN hAN d).div_const (d.factorial : ℝ)
  convert h using 1
  ext n
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hd : (d.factorial : ℝ) ≠ 0 := by positivity
  rw [div_div, mul_comm (d.factorial : ℝ), mul_div_mul_right _ _ hd]

/-- A positive limiting proportion forces the numerator to diverge. -/
theorem tendsto_nat_atTop_of_ratio {A N : ℕ → ℕ} {c : ℝ}
    (hN : Tendsto N atTop atTop)
    (hAN : Tendsto (fun n => (A n : ℝ) / N n) atTop (𝓝 c)) (hc : 0 < c) :
    Tendsto A atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  have h := hAN.pos_mul_atTop hc ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hN)
  apply h.congr'
  filter_upwards [hN.eventually (eventually_ge_atTop 1)] with n hn
  have hne : (N n : ℝ) ≠ 0 := by exact_mod_cast (by omega : N n ≠ 0)
  simp [hne]

/-- Removing a fixed number does not change a normalized asymptotic. -/
theorem normalized_nat_sub_const_tendsto {A N : ℕ → ℕ} {c : ℝ}
    (hA : Tendsto A atTop atTop) (hN : Tendsto N atTop atTop)
    (hAN : Tendsto (fun n => (A n : ℝ) / N n) atTop (𝓝 c)) (d : ℕ) :
    Tendsto (fun n => ((A n - d : ℕ) : ℝ) / N n) atTop (𝓝 c) := by
  have hd := (tendsto_const_div_atTop_nhds_zero_nat (d : ℝ)).comp hN
  apply (show Tendsto (fun n => (A n : ℝ) / N n - (d : ℝ) / N n)
    atTop (𝓝 c) by simpa using hAN.sub hd).congr'
  filter_upwards [hA.eventually (eventually_ge_atTop d)] with n hn
  simp [Nat.cast_sub hn, sub_div]

/-- Subtraction of natural sequences agrees eventually with real subtraction
when their normalized limiting proportions are strictly ordered. -/
theorem normalized_nat_sub_tendsto {A B N : ℕ → ℕ} {a b : ℝ}
    (hN : Tendsto N atTop atTop)
    (hA : Tendsto (fun n => (A n : ℝ) / N n) atTop (𝓝 a))
    (hB : Tendsto (fun n => (B n : ℝ) / N n) atTop (𝓝 b)) (hab : b < a) :
    Tendsto (fun n => ((A n - B n : ℕ) : ℝ) / N n) atTop (𝓝 (a - b)) := by
  have he : ∀ᶠ n in atTop, (B n : ℝ) / N n < (A n : ℝ) / N n :=
    by
      simpa only [sub_pos] using (hA.sub hB).eventually_const_lt (sub_pos.mpr hab)
  apply (hA.sub hB).congr'
  filter_upwards [he, hN.eventually (eventually_ge_atTop 1)] with n hn hNn
  have hp : (0 : ℝ) < N n := by exact_mod_cast (by omega : 0 < N n)
  have hle : B n ≤ A n := by exact_mod_cast (le_of_lt ((div_lt_div_iff_of_pos_right hp).mp hn))
  simp [Nat.cast_sub hle, sub_div]

/-- The number of ordinary slots has the expected linear proportion. -/
theorem normalized_slots_tendsto {r : ℕ} (hr : 3 ≤ r) {N k s : ℕ → ℕ}
    (hN : Tendsto N atTop atTop)
    (hsize : ∀ n, N n = (r - 1) * k n + s n)
    (hs : Tendsto (fun n => (s n : ℝ) / N n) atTop (𝓝 0)) :
    Tendsto (fun n => (k n : ℝ) / N n) atTop (𝓝 (1 / (r - 1 : ℕ))) := by
  have ha : ((r - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : r - 1 ≠ 0)
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hs).div_const ((r - 1 : ℕ) : ℝ)
  apply (show Tendsto (fun n => (1 - (s n : ℝ) / N n) / (r - 1 : ℕ))
    atTop (𝓝 (1 / (r - 1 : ℕ))) by simpa using h).congr'
  filter_upwards [hN.eventually (eventually_ge_atTop 1)] with n hn
  have hne : (N n : ℝ) ≠ 0 := by exact_mod_cast (by omega : N n ≠ 0)
  have he : (N n : ℝ) = (r - 1 : ℕ) * (k n : ℝ) + s n := by exact_mod_cast hsize n
  have har : (r : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  field_simp [ha, hne, har]
  nlinarith

private theorem cancel_normalizing_powers (f u v w t b q z p : ℝ)
    (hz : z ≠ 0) (hp : p ≠ 0) :
    f * (u/z) * (v/z) / ((w/z) * (t/(p*z))) * b * (q/p) =
      f*u*v/(w*t)*(b*q) := by
  by_cases hw : w = 0
  · simp [hw]
  by_cases ht : t = 0
  · simp [ht]
  field_simp <;> ring

/-- The asymptotic assertion of Proposition 2.4 for the explicit complete-host
factor. Only fixed uniformity, the vertex identity, and sparse marked ports
are needed; all size inequalities follow eventually. -/
theorem directedNormalizationFactor_asymptotic {r : ℕ} (hr : 3 ≤ r)
    {N k s : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hsize : ∀ n, N n = (r - 1) * k n + s n)
    (hs : Tendsto (fun n => (s n : ℝ) / N n) atTop (𝓝 0)) :
    Tendsto (fun n => directedNormalizationFactor r (N n) (k n) (s n) *
      (((r : ℝ) - 1)^2 * completeMeanDegree r (N n))) atTop (𝓝 1) := by
  let a : ℝ := (r - 1 : ℕ)
  have ha : 0 < a := by dsimp [a]; exact_mod_cast (by omega : 0 < r - 1)
  have hNN : Tendsto (fun n => (N n : ℝ) / N n) atTop (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hN.eventually (eventually_ge_atTop 1)] with n hn
    have hn' : (N n : ℝ) ≠ 0 := by exact_mod_cast (by omega : N n ≠ 0)
    simp [hn']
  have hk : Tendsto (fun n => (k n : ℝ) / N n) atTop (𝓝 (1/a)) :=
    normalized_slots_tendsto hr hN hsize hs
  have hkTop := tendsto_nat_atTop_of_ratio hN hk (one_div_pos.mpr ha)
  have hks : Tendsto (fun n => ((k n - s n : ℕ) : ℝ) / N n) atTop (𝓝 (1/a)) := by
    simpa using normalized_nat_sub_tendsto hN hk hs (one_div_pos.mpr ha)
  have hksTop := tendsto_nat_atTop_of_ratio hN hks (one_div_pos.mpr ha)
  have hks1 := normalized_nat_sub_const_tendsto hksTop hN hks 1
  have hk1 := normalized_nat_sub_const_tendsto hkTop hN hk 1
  have hs2 : Tendsto (fun n => ((2 * s n : ℕ) : ℝ) / N n) atTop (𝓝 (0 : ℝ)) := by
    simpa [mul_div_assoc] using hs.const_mul 2
  have hv : Tendsto (fun n => ((N n - 2*s n : ℕ) : ℝ) / N n) atTop (𝓝 (1 : ℝ)) := by
    simpa using normalized_nat_sub_tendsto hN hNN hs2 (by norm_num : (0 : ℝ) < 1)
  have hvTop := tendsto_nat_atTop_of_ratio hN hv (by norm_num : (0 : ℝ) < 1)
  have hdesc := normalized_descFactorial_tendsto hvTop hN hv r
  have hN1 := normalized_nat_sub_const_tendsto hN hN hNN 1
  have hN1Top := tendsto_nat_atTop_of_ratio hN hN1 (by norm_num : (0 : ℝ) < 1)
  have hchoose := normalized_choose_tendsto hN1Top hN hN1 (r-1)
  have hden : 1 / a * (1 : ℝ)^r ≠ 0 := by positivity
  have hlim := ((((hks.const_mul ((r-2).factorial : ℝ)).mul hks1).div
    (hk1.mul hdesc) hden).mul_const (a^2)).mul hchoose
  have hfac : ((r-1).factorial : ℝ) = a * ((r-2).factorial : ℝ) := by
    have he : r-1 = (r-2)+1 := by omega
    rw [he, Nat.factorial_succ, Nat.cast_mul, ← he]
  have hc : ((r-2).factorial : ℝ) ≠ 0 := by positivity
  have hlimit : ((r-2).factorial : ℝ) * (1/a) * (1/a) /
    (1/a * (1 : ℝ)^r) * a^2 * ((1 : ℝ)^(r-1) / (r-1).factorial) = 1 := by
    rw [hfac]
    field_simp [ne_of_gt ha, hc]
    ring
  rw [hlimit] at hlim
  apply hlim.congr'
  filter_upwards [hN.eventually (eventually_ge_atTop 1)] with n hn
  have hne : (N n : ℝ) ≠ 0 := by exact_mod_cast (by omega : N n ≠ 0)
  have haeq : a = (r : ℝ) - 1 := by dsimp [a]; rw [Nat.cast_sub (by omega : 1 ≤ r)]; norm_num
  have hpow : (N n : ℝ)^r = (N n : ℝ)^(r-1) * N n := by
    rw [← pow_succ]; congr 1; omega
  dsimp [directedNormalizationFactor, completeMeanDegree]
  rw [haeq, hpow]
  exact cancel_normalizing_powers _ _ _ _ _ _ _ _ _ hne (pow_ne_zero _ hne)

end LooseHamilton
