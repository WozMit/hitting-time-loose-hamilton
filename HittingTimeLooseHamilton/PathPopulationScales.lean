module

public import HittingTimeLooseHamilton.PathTailScales
public import HittingTimeLooseHamilton.WindowMeanAsymptotics
public import HittingTimeLooseHamilton.PairDegreeAsymptotic
public import HittingTimeLooseHamilton.PoissonTailParameters

public section

noncomputable section
namespace LooseHamilton
open Filter

lemma nat_mul_log_div_choose_tendsto_zero {r : ℕ} (hr : 2≤r) :
    Tendsto (fun n : ℕ => (n:ℝ)*Real.log n/(n.choose r:ℝ)) atTop (nhds 0) := by
  have h := (nat_mul_log_div_pow_tendsto_zero hr).div (normalized_nat_choose_tendsto r)
    (by positivity : (1:ℝ)/(r.factorial:ℝ) ≠ 0)
  apply (show Tendsto (fun n : ℕ => (((n:ℝ)*Real.log n)/(n:ℝ)^r)/
    ((n.choose r:ℝ)/(n:ℝ)^r)) atTop (nhds 0) by convert h using 1 <;> simp).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n≠0 by omega)
  field_simp

/-- In the density window the extension reservoir retains half its edges and half each star. -/
theorem eventually_path_population {r : ℕ} (hr : 3≤r) {C : ℝ} (hC : 0≤C) :
    ∀ᶠ n : ℕ in atTop, r≤n ∧ 2≤n ∧
      C*Real.log (n:ℝ) ≤ ((n-1).choose (r-1):ℝ)/2 ∧
      ∀ M : ℕ, (r:ℝ)*M/n ≤ 2*Real.log n →
        (M:ℝ) ≤ (n.choose r:ℝ)/2 := by
  have h := nat_mul_log_div_choose_tendsto_zero (show 2≤r by omega)
  filter_upwards [eventually_ge_atTop r,
    (tendsto_order.mp h).2 (1/4) (by norm_num),
    (tendsto_order.mp h).2 (1/(2*(C+1))) (by positivity)] with n hn h1 h2
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hK : (0:ℝ)<n.choose r := by exact_mod_cast Nat.choose_pos hn
  have hr1 : (1:ℝ)≤r := by exact_mod_cast (show 1≤r by omega)
  have hD : (n:ℝ)*((n-1).choose (r-1):ℝ) = (r:ℝ)*(n.choose r:ℝ) := by
    have hi := vertex_incidence_ratio (show 1≤r by omega) hn
    simpa only [mul_comm] using (div_eq_div_iff hK.ne' hn0.ne').mp hi
  have hl : 0≤Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
  have h2' := (div_lt_iff₀ hK).mp h2
  have h2'' := mul_lt_mul_of_pos_right h2' (by positivity : 0<2*(C+1))
  have hcancel : 1/(2*(C+1))*(n.choose r:ℝ)*(2*(C+1)) = n.choose r := by field_simp
  rw [hcancel] at h2''
  refine ⟨hn,by omega,?_,?_⟩
  · apply (mul_le_mul_iff_right₀ hn0).mp
    nlinarith [mul_nonneg hK.le (sub_nonneg.mpr hr1),mul_nonneg hn0.le hl]
  · intro M hM
    have hm := (div_le_iff₀ hn0).mp hM
    have h1' := (div_lt_iff₀ hK).mp h1
    have hM0 : (0:ℝ)≤M := by positivity
    nlinarith [mul_nonneg hM0 (sub_nonneg.mpr hr1)]

/-- Sampling j-M missing edges gives at most twice the complete-host incidence mean. -/
lemma path_population_mean_upper {K M j D μ : ℝ}
    (hK : 0<K) (hM : 0≤M) (hhalf : M≤K/2) (hMj : M≤j)
    (hD : 0≤D) (hmean : D*j/K≤μ) : D*(j-M)/(K-M)≤2*μ := by
  have hden : 0<K-M := by linarith
  apply (div_le_iff₀ hden).mpr
  have hmean' := (div_le_iff₀ hK).mp hmean
  have hj : 0≤j := hM.trans hMj
  have hμ : 0≤μ := (div_nonneg (mul_nonneg hD hj) hK.le).trans hmean
  nlinarith [mul_nonneg hD hM,mul_nonneg hμ (sub_nonneg.mpr hhalf)]

/-- After j reaches twice M, a reservoir retaining half each star has mean at least μ/4. -/
lemma path_population_mean_lower {K M j D D' μ : ℝ}
    (hK : 0<K) (hM : 0≤M) (hhalf : M≤K/2) (hMj : 2*M≤j)
    (hD : 0≤D) (hstar : D/2≤D') (hmean : μ≤D*j/K) :
    μ/4 ≤ D'*(j-M)/(K-M) := by
  have hden : 0<K-M := by linarith
  have hj : 0≤j-M := by linarith
  have hmean' := (le_div_iff₀ hK).mp hmean
  by_cases hμ : 0≤μ
  · apply (le_div_iff₀ hden).mpr
    have hprod := mul_le_mul_of_nonneg_right hstar hj
    nlinarith [mul_nonneg hD (show 0≤j-2*M by linarith),mul_nonneg hμ hM]
  · exact (by linarith : μ/4≤0).trans (div_nonneg (mul_nonneg (by linarith) hj) hden.le)
lemma path_vertex_mean_upper {n r M j : ℕ} (hr : 1≤r) (hn : r≤n)
    (hhalf : (M:ℝ)≤(n.choose r:ℝ)/2) (hj : M≤j) :
    ((n-1).choose (r-1):ℝ)*((j:ℝ)-M)/((n.choose r:ℝ)-M) ≤ 2*((r:ℝ)*j/n) := by
  have hK : (0:ℝ)<n.choose r := by exact_mod_cast Nat.choose_pos hn
  apply path_population_mean_upper hK (Nat.cast_nonneg _) hhalf
    (by exact_mod_cast hj) (Nat.cast_nonneg _)
  have hi := vertex_incidence_ratio hr hn
  calc
    _ = (((n-1).choose (r-1):ℝ)/(n.choose r:ℝ))*(j:ℝ) := by ring
    _ = (r:ℝ)*j/n := by rw [hi]; ring
    _ ≤ (r:ℝ)*j/n := le_rfl

lemma path_pair_mean_upper {n r M j : ℕ} (hr : 2≤r) (hn : r≤n)
    (hhalf : (M:ℝ)≤(n.choose r:ℝ)/2) (hj : M≤j) :
    ((n-2).choose (r-2):ℝ)*((j:ℝ)-M)/((n.choose r:ℝ)-M) ≤
      4*((r:ℝ)-1)*((r:ℝ)*j/n)/(n:ℝ) := by
  have hK : (0:ℝ)<n.choose r := by exact_mod_cast Nat.choose_pos hn
  have hn2 : (2:ℝ)≤n := by exact_mod_cast hr.trans hn
  have hr2 : (2:ℝ)≤r := by exact_mod_cast hr
  have hn0 : (0:ℝ)<n := by linarith
  have hn1 : 0<(n:ℝ)-1 := by linarith
  have hi := pair_incidence_ratio hr hn
  have hmean : ((n-2).choose (r-2):ℝ)*(j:ℝ)/(n.choose r:ℝ) ≤
      2*((r:ℝ)-1)*((r:ℝ)*j/n)/(n:ℝ) := by
    calc
      _ = (((n-2).choose (r-2):ℝ)/(n.choose r:ℝ))*(j:ℝ) := by ring
      _ = ((r:ℝ)*((r:ℝ)-1)/((n:ℝ)*((n:ℝ)-1)))*(j:ℝ) := by rw [hi]
      _ ≤ _ := by
        rw [div_mul_eq_mul_div]
        have hden : (n:ℝ)*((n:ℝ)-1) > 0 := mul_pos hn0 hn1
        apply (div_le_iff₀ hden).mpr
        have hp : 0≤(r:ℝ)*((r:ℝ)-1)*(j:ℝ) := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (Nat.cast_nonneg _)
        have he : 2*((r:ℝ)-1)*((r:ℝ)*j/n)/(n:ℝ)*((n:ℝ)*((n:ℝ)-1)) = 2*((r:ℝ)-1)*((r:ℝ)*j)*((n:ℝ)-1)/(n:ℝ) := by field_simp <;> ring
        rw [he]
        apply (le_div_iff₀ hn0).mpr
        nlinarith [mul_nonneg hp (show 0≤(n:ℝ)-2 by linarith)]
  have h := path_population_mean_upper hK (Nat.cast_nonneg _) hhalf
    (by exact_mod_cast hj) (Nat.cast_nonneg _) hmean
  convert h using 1 <;> ring
end LooseHamilton
