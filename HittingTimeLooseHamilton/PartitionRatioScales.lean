module

public import HittingTimeLooseHamilton.PartitionRatioFinite
public import HittingTimeLooseHamilton.PartitionUnionDecay
public import HittingTimeLooseHamilton.PathRegularityModels

public section

/-! Uniform complete-host partition bias in the manuscript's size window. -/
noncomputable section
namespace LooseHamilton
open Filter Topology

@[expose] def partitionBiasEnvelope (r : ℕ) (L : ℝ) (n : ℕ) : ℝ :=
  6*(r.choose 2:ℝ)*(r:ℝ)*(L*(n:ℝ)^(-9/10:ℝ)+(r:ℝ)*(n:ℝ)^(-1:ℝ))

lemma partitionBiasEnvelope_log_tendsto (r : ℕ) (L : ℝ) :
    Tendsto (fun n => partitionBiasEnvelope r L n*Real.log n) atTop (𝓝 0) := by
  have h1 := (tendsto_nat_rpow_mul_log_pow (by norm_num : (-9/10:ℝ)<0) 1).const_mul L
  have h2 := (tendsto_nat_rpow_mul_log_pow (by norm_num : (-1:ℝ)<0) 1).const_mul (r:ℝ)
  have h := (h1.add h2).const_mul (6*(r.choose 2:ℝ)*(r:ℝ))
  simp only [mul_zero,add_zero,pow_one] at h
  convert h using 1
  ext n
  unfold partitionBiasEnvelope
  ring

lemma junctionFraction_bounds {r : ℕ} (hr : 3≤r) :
    0≤junctionFraction r ∧ junctionFraction r≤1 ∧ privateFraction r=1-junctionFraction r := by
  have hr' : (3:ℝ)≤r := by exact_mod_cast hr
  have hd : 0<(r:ℝ)-1 := by linarith
  unfold junctionFraction privateFraction
  refine ⟨by positivity, (div_le_one hd).mpr (by linarith), ?_⟩
  field_simp <;> ring

lemma completePartitionRatio_bias_eventually {r : ℕ} (hr : 3≤r) (L : ℝ) (hL : 0≤L) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, k≤n →
      |(k:ℝ)-junctionFraction r*n|≤L*(n:ℝ)^(1/10:ℝ) →
      |completePartitionRatio r n k-partitionDensity r|≤(Real.log n)^(-1/8:ℝ) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (max 1 (2*r*r)),
    hlog.eventually (eventually_ge_atTop 1),
    (tendsto_order.mp (partitionBiasEnvelope_log_tendsto r L)).2 1 (by norm_num)]
      with n hn hl henv
  have hn1 : 1≤n := (le_max_left _ _).trans hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hnr : (2:ℝ)*r*r≤n := by exact_mod_cast ((le_max_right _ _).trans hn)
  have hden : 1/2≤normalizedFalling n n r := by
    have hh := normalizedFalling_error (show 0<n by omega) le_rfl (by norm_num : (0:ℝ)≤1) le_rfl r
    simp only [div_self (ne_of_gt hn0),sub_self,abs_zero,zero_add,one_pow] at hh
    have hu : (r:ℝ)*((r:ℝ)/n)≤1/2 := by
      rw [←mul_div_assoc]
      apply (div_le_iff₀ hn0).mpr
      nlinarith
    have hh' := (abs_le.mp (hh.trans hu)).1
    linarith
  intro k hkn hk
  obtain ⟨ha0,ha1,hb⟩ := junctionFraction_bounds hr
  have he : |(k:ℝ)/n-junctionFraction r|≤L*(n:ℝ)^(1/10:ℝ)/n := by
    have hid : (k:ℝ)/n-junctionFraction r=((k:ℝ)-junctionFraction r*n)/n := by field_simp <;> ring
    rw [hid,abs_div,abs_of_pos hn0]
    exact div_le_div_of_nonneg_right hk hn0.le
  have hbound := completePartitionRatio_error (show 2≤r by omega) (show 0<n by omega) hkn ha0 ha1 he hden
  have hp1 : (n:ℝ)^(1/10:ℝ)/n=(n:ℝ)^(-9/10:ℝ) := by
    calc
      _ = (n:ℝ)^(1/10:ℝ)/(n:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_sub hn0]; norm_num
  have hp2 : (1:ℝ)/n=(n:ℝ)^(-1:ℝ) := by rw [Real.rpow_neg_one,one_div]
  have hid : 6*(r.choose 2:ℝ)*(r:ℝ)*(L*(n:ℝ)^(1/10:ℝ)/n+(r:ℝ)/n)=partitionBiasEnvelope r L n := by
    unfold partitionBiasEnvelope
    rw [mul_div_assoc,hp1,div_eq_mul_one_div (r:ℝ),hp2]
  rw [hid] at hbound
  have htheta : (r.choose 2:ℝ)*(junctionFraction r)^2*(1-junctionFraction r)^(r-2)=partitionDensity r := by
    simp only [partitionDensity,hb]
  rw [htheta] at hbound
  have hupper : partitionBiasEnvelope r L n≤1/Real.log n := by
    apply (le_div_iff₀ (show 0<Real.log (n:ℝ) by linarith)).mpr
    exact henv.le
  apply hbound.trans (hupper.trans _)
  simpa only [Real.rpow_neg_one,one_div] using
    Real.rpow_le_rpow_of_exponent_le hl (by norm_num : (-1:ℝ)≤ -1/8)
end LooseHamilton
