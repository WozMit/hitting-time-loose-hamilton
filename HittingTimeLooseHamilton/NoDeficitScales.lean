module

public import HittingTimeLooseHamilton.ExceptionalSetAsymptotics
public import HittingTimeLooseHamilton.Setup

public section

noncomputable section
namespace LooseHamilton
open Filter

lemma noDeficit_power_bound {n a : ℕ} {x : ℝ}
    (hn : 0<n) (hl : 8/epsilon≤Real.log (n:ℝ)) (hx : 0≤x)
    (hbase : x≤Real.exp (-Real.log (n:ℝ)/2))
    (ha : epsilon/2*Real.log (n:ℝ)≤a) :
    (n:ℝ)*x^a≤Real.exp (-(epsilon/8)*(Real.log n)^2) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have heps : 0<epsilon := by unfold epsilon; norm_num
  have hl0 : 0≤Real.log (n:ℝ) := le_trans (by positivity) hl
  have hp : x^a≤Real.exp (-Real.log (n:ℝ)/2)^a := by gcongr
  have hexp : Real.exp (-Real.log (n:ℝ)/2)^a = Real.exp ((a:ℝ)*(-Real.log n/2)) :=
    (Real.exp_nat_mul _ _).symm
  rw [hexp] at hp
  calc
    _ ≤ (n:ℝ)*Real.exp ((a:ℝ)*(-Real.log n/2)) := mul_le_mul_of_nonneg_left hp hn0.le
    _ = Real.exp (Real.log n+(a:ℝ)*(-Real.log n/2)) := by rw [Real.exp_add,Real.exp_log hn0]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hal := mul_le_mul_of_nonneg_right ha hl0
      have hlarge := (div_le_iff₀ heps).mp hl
      have hlarge' := mul_le_mul_of_nonneg_right hlarge hl0
      nlinarith only [hal,hlarge']

/-- Even the crude bound choose(D,a) ≤ D^a gives a log-squared tail, uniformly in ν≤log n. -/
theorem eventually_noDeficit_binomial_tail {C : ℝ} (hC : 0≤C) :
    ∀ᶠ n : ℕ in atTop, 0<n ∧ ∀ (D : ℕ) (q ν : ℝ),
      (D:ℝ)≤C*Real.log n → 0≤q → q≤C*ν/n → 0≤ν → ν≤Real.log n →
      (n:ℝ)*(D.choose (Nat.floor (epsilon*Real.log n)):ℝ)*
        q^(Nat.floor (epsilon*Real.log n)) ≤
          Real.exp (-(epsilon/8)*(Real.log n)^2) := by
  have hsmall := (tendsto_nat_rpow_mul_log_pow (by norm_num : (-1/2:ℝ)<0) 2).const_mul (C^2)
  simp only [mul_zero] at hsmall
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (1:ℕ),hlog.eventually (eventually_ge_atTop (8/epsilon)),
    (tendsto_order.mp hsmall).2 1 (by norm_num)] with n hn hl hs
  change 8/epsilon≤Real.log (n:ℝ) at hl
  have hn0 : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hl0 : 0≤Real.log (n:ℝ) := by unfold epsilon at hl; linarith
  have hp : (n:ℝ)^(-1/2:ℝ)*(n:ℝ)^(1/2:ℝ)=1 := by rw [←Real.rpow_add hn0]; norm_num
  have he : Real.exp (-Real.log (n:ℝ)/2) = (n:ℝ)^(1/2:ℝ)/(n:ℝ) := by
    have hid : (n:ℝ)^(1/2:ℝ)/(n:ℝ) = (n:ℝ)^(-1/2:ℝ) := by
      calc
        _ = (n:ℝ)^(1/2:ℝ)/(n:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_sub hn0]; norm_num
    rw [hid,Real.rpow_def_of_pos hn0]
    congr 1
    ring
  have hB : C^2*(Real.log n)^2≤(n:ℝ)^(1/2:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hs.le (Real.rpow_nonneg hn0.le (1/2:ℝ))
    have hleft : C^2*((n:ℝ)^(-1/2:ℝ)*(Real.log n)^2)*(n:ℝ)^(1/2:ℝ)=C^2*(Real.log n)^2 := by
      calc
        _ = C^2*(Real.log n)^2*((n:ℝ)^(-1/2:ℝ)*(n:ℝ)^(1/2:ℝ)) := by ring
        _ = _ := by rw [hp,mul_one]
    rw [hleft,one_mul] at hh
    exact hh
  refine ⟨by omega,?_⟩
  intro D q ν hD hq hqbound hν hνlog
  have hbase : (D:ℝ)*q≤Real.exp (-Real.log (n:ℝ)/2) := by
    rw [he]
    have h1 := mul_le_mul hD hqbound hq (mul_nonneg hC hl0)
    have h2 := mul_le_mul_of_nonneg_left hνlog (mul_nonneg (sq_nonneg C) hl0)
    apply (le_div_iff₀ hn0).mpr
    have h1' : (D:ℝ)*q*(n:ℝ)≤C^2*Real.log n*ν := by
      have hh := mul_le_mul_of_nonneg_right h1 hn0.le
      field_simp at hh
      nlinarith only [hh]
    nlinarith only [h1',h2,hB]
  have ha : epsilon/2*Real.log (n:ℝ)≤(Nat.floor (epsilon*Real.log n):ℝ) := by
    have hf := Nat.lt_floor_add_one (epsilon*Real.log (n:ℝ))
    unfold epsilon at hl hf ⊢
    linarith
  have hpow := noDeficit_power_bound (show 0<n by omega) hl (mul_nonneg (Nat.cast_nonneg D) hq) hbase ha
  have hchoose : (D.choose (Nat.floor (epsilon*Real.log n)):ℝ)≤(D:ℝ)^(Nat.floor (epsilon*Real.log n)) := by
    exact_mod_cast Nat.choose_le_pow D (Nat.floor (epsilon*Real.log n))
  calc
    _ ≤ (n:ℝ)*(D:ℝ)^(Nat.floor (epsilon*Real.log n))*q^(Nat.floor (epsilon*Real.log n)) := by gcongr
    _ = (n:ℝ)*((D:ℝ)*q)^(Nat.floor (epsilon*Real.log n)) := by rw [mul_pow]; ring
    _ ≤ _ := hpow

lemma noDeficit_protected_bound {n : ℕ} {B D q C Ck ν : ℝ}
    (hn : 0<n) (hB0 : 0≤B) (hD0 : 0≤D) (hq0 : 0≤q)
    (hB : B≤(n:ℝ)^(1/4:ℝ)) (hD : D≤C*Real.log n) (hq : q≤Ck*ν/n) :
    B*D*q≤C*Ck*ν*(n:ℝ)^(-3/4:ℝ)*Real.log n := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hC : 0≤C*Real.log (n:ℝ) := hD0.trans hD
  have hh := mul_le_mul (mul_le_mul hB hD hD0 (Real.rpow_nonneg hn0.le _)) hq hq0
    (mul_nonneg (Real.rpow_nonneg hn0.le _) hC)
  have he : (n:ℝ)^(1/4:ℝ)/(n:ℝ)=(n:ℝ)^(-3/4:ℝ) := by
    calc
      _ = (n:ℝ)^(1/4:ℝ)/(n:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_sub hn0]; norm_num
  convert hh using 1
  calc
    _ = C*Ck*ν*((n:ℝ)^(1/4:ℝ)/(n:ℝ))*Real.log n := by rw [he]
    _ = _ := by ring

lemma noDeficit_batch_ratio {n m k : ℕ} {ν Ck : ℝ}
    (hn : 0<n) (hm : 0<m) (hk : 0<k) (hν : 0≤ν)
    (hscale : (n:ℝ)≤Ck*k) :
    (Nat.floor (ν*m/k):ℝ)/(m:ℝ) ≤ Ck*ν/n := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hm0 : (0:ℝ)<m := by exact_mod_cast hm
  have hk0 : (0:ℝ)<k := by exact_mod_cast hk
  have hf := Nat.floor_le (show 0≤ν*(m:ℝ)/(k:ℝ) by positivity)
  apply (div_le_iff₀ hm0).mpr
  apply hf.trans
  apply (div_le_iff₀ hk0).mpr
  have hh := mul_le_mul_of_nonneg_right hscale (mul_nonneg hν hm0.le)
  apply (mul_le_mul_iff_left₀ hn0).mp
  field_simp
  nlinarith only [mul_le_mul_of_nonneg_right hscale hν]
/-- Separate fixed degree and sampling constants can be used without changing the exponent. -/
theorem eventually_noDeficit_binomial_tail_two_constants {C K : ℝ} (hC : 0≤C) :
    ∀ᶠ n : ℕ in atTop, 0<n ∧ ∀ (D : ℕ) (q ν : ℝ),
      (D:ℝ)≤C*Real.log n → 0≤q → q≤K*ν/n → 0≤ν → ν≤Real.log n →
      (n:ℝ)*(D.choose (Nat.floor (epsilon*Real.log n)):ℝ)*
        q^(Nat.floor (epsilon*Real.log n)) ≤
          Real.exp (-(epsilon/8)*(Real.log n)^2) := by
  filter_upwards [eventually_noDeficit_binomial_tail (hC.trans (le_max_left C K))] with n hn
  refine ⟨hn.1,?_⟩
  intro D q ν hD hq hqbound hν hνlog
  apply hn.2 D q ν
  · exact hD.trans (mul_le_mul_of_nonneg_right (le_max_left C K) (hν.trans hνlog))
  · exact hq
  · exact hqbound.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right C K) hν) (Nat.cast_nonneg n))
  · exact hν
  · exact hνlog

/-- Linear cycle length guarantees that the prescribed batch is a valid subset size. -/
theorem eventually_noDeficit_batch_valid {K : ℝ} (hK : 0<K) :
    ∀ᶠ n : ℕ in atTop, 0<n ∧ ∀ (m k : ℕ) (ν : ℝ),
      (n:ℝ)≤K*k → 0≤ν → ν≤Real.log n →
        0<k ∧ Nat.floor (ν*m/k)≤m := by
  have hsmall := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul K
  simp only [mul_zero] at hsmall
  filter_upwards [eventually_ge_atTop (1:ℕ),(tendsto_order.mp hsmall).2 1 (by norm_num)] with n hn hs
  have hn0 : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hs' : K*Real.log (n:ℝ)≤n := by
    have hh : K*Real.log (n:ℝ)/(n:ℝ)≤1 := by simpa [mul_div_assoc] using hs.le
    simpa using (div_le_iff₀ hn0).mp hh
  refine ⟨by omega,?_⟩
  intro m k ν hscale hν hνlog
  have hk0 : (0:ℝ)<k := by nlinarith only [hscale,hn0,hK]
  have hνk : ν≤(k:ℝ) := by
    apply hνlog.trans
    exact (mul_le_mul_iff_right₀ hK).mp (hs'.trans hscale)
  refine ⟨by exact_mod_cast hk0,?_⟩
  have hf := Nat.floor_le (show 0≤ν*(m:ℝ)/(k:ℝ) by positivity)
  have hv : ν*(m:ℝ)/(k:ℝ)≤m := by
    apply (div_le_iff₀ hk0).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hνk (show (0:ℝ)≤m by positivity)]
  exact_mod_cast hf.trans hv

lemma noDeficit_protected_error_tendsto_zero (C : ℝ) :
    Tendsto (fun n : ℕ => C*(n:ℝ)^(-3/4:ℝ)*(Real.log n)^2) atTop (nhds 0) := by
  simpa only [mul_zero,mul_assoc] using
    (tendsto_nat_rpow_mul_log_pow (by norm_num : (-3/4:ℝ)<0) 2).const_mul C

lemma noDeficit_exponential_error_tendsto_zero :
    Tendsto (fun n : ℕ => Real.exp (-(epsilon/8)*(Real.log (n:ℝ))^2)) atTop (nhds 0) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hpow : Tendsto (fun n : ℕ => (Real.log (n:ℝ))^2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2:ℕ)≠0)).comp hlog
  have hpos : 0<epsilon/8 := by unfold epsilon; norm_num
  have h := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hpow.const_mul_atTop hpos))
  simpa only [Function.comp_def,neg_mul] using h
end LooseHamilton
