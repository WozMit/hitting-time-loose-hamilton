module

public import HittingTimeLooseHamilton.ExceptionalSetAsymptotics

public section

/-! Scalar bounds for a root-link occupancy tail after bounded prescriptions and one swap. -/
noncomputable section
namespace LooseHamilton
open Filter

lemma rootLink_choose_le_two_pow (q a : ℕ) : (q.choose a:ℝ)≤(2:ℝ)^q := by
  by_cases hq : q=0
  · subst q
    cases a <;> simp
  · exact_mod_cast (Nat.choose_le_two_pow q a)

/-- Includes density zero: no positivity assumption on the bad-set density is needed. -/
lemma rootLink_power_tail {q q' a : ℕ} {ρ : ℝ}
    (hq : q'≤q) (ha : q≤2*a) (hρ : 0≤ρ) (hsmall : 8*ρ≤1) :
    (q'.choose a:ℝ)*(2*ρ)^a ≤ (8*ρ)^((q:ℝ)/4) := by
  have hc : (q'.choose a:ℝ)≤(2:ℝ)^(2*a) := by
    apply (rootLink_choose_le_two_pow q' a).trans
    exact pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (hq.trans ha)
  calc
    _ ≤ (2:ℝ)^(2*a)*(2*ρ)^a := mul_le_mul_of_nonneg_right hc (pow_nonneg (by positivity) _)
    _ = (8*ρ)^a := by rw [pow_mul,←mul_pow]; norm_num; congr 1 <;> ring
    _ = (8*ρ)^(a:ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_ge' (by positivity) hsmall (by positivity)
      have ha' : (q:ℝ)≤2*(a:ℝ) := by exact_mod_cast ha
      have ha0 : (0:ℝ)≤a := by positivity
      linarith

/-- Removing at most h prescribed elements and losing one hit to a swap leaves enough hits. -/
lemma rootLink_threshold_margin (q h : ℕ) (hq : 12*(h+1)≤q) :
    q≤2*(((2*q+2)/3)-h-1) := by omega

lemma rootLink_prescribed_tail {q q' h : ℕ} {ρ : ℝ}
    (hq' : q'≤q) (hq : 12*(h+1)≤q) (hρ : 0≤ρ) (hsmall : 8*ρ≤1) :
    (q'.choose (((2*q+2)/3)-h-1):ℝ)*(2*ρ)^(((2*q+2)/3)-h-1) ≤
      (8*ρ)^((q:ℝ)/4) :=
  rootLink_power_tail hq' (rootLink_threshold_margin q h hq) hρ hsmall

/-- Deleting a bounded part of a universe at least twice that size doubles density at most. -/
lemma rootLink_remaining_density {U h B ρ : ℝ}
    (hU : 0<U) (hh : 2*h≤U) (hρ : 0≤ρ) (hB : B≤ρ*U) :
    B/(U-h)≤2*ρ := by
  have hden : 0<U-h := by linarith
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hB,mul_le_mul_of_nonneg_left hh hρ]

lemma eventually_rootLink_sample_large {c : ℝ} (hc : 0<c) (h : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℕ,
      c*Real.log (n:ℝ)≤q → 12*(h+1)≤q := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hlog.eventually (eventually_ge_atTop ((12*((h:ℝ)+1))/c))] with n hn
  change (12*((h:ℝ)+1))/c≤Real.log (n:ℝ) at hn
  intro q hq
  have hh : (12*((h:ℝ)+1))≤c*Real.log (n:ℝ) := by
    have hh := (div_le_iff₀ hc).mp hn
    nlinarith only [hh]
  exact_mod_cast hh.trans hq

/-- The displayed bound tends to zero when the density is at most 1/16 and q≥c log n. -/
lemma rootLink_uniform_error_tendsto_zero {c : ℝ} (hc : 0<c) :
    Tendsto (fun n : ℕ => (1/2:ℝ)^(c*Real.log (n:ℝ)/4)) atTop (nhds 0) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hneg : (c/4)*Real.log (1/2:ℝ)<0 := by
    apply mul_neg_of_pos_of_neg (by positivity)
    exact Real.log_neg (by norm_num) (by norm_num)
  have h := Real.tendsto_exp_atBot.comp (hlog.const_mul_atTop_of_neg hneg)
  apply h.congr'
  filter_upwards [] with n
  change Real.exp ((c/4)*Real.log (1/2:ℝ)*Real.log (n:ℝ)) = (1/2:ℝ)^(c*Real.log (n:ℝ)/4)
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<1/2)]
  congr 1
  ring

lemma rootLink_uniform_error_bound {c : ℝ} {n q : ℕ} {ρ : ℝ}
    (hc : 0≤c) (hl : 0≤Real.log (n:ℝ)) (hq : c*Real.log n≤q)
    (hρ : 0≤ρ) (hsmall : 8*ρ≤1/2) :
    (8*ρ)^((q:ℝ)/4) ≤ (1/2:ℝ)^(c*Real.log n/4) := by
  calc
    _ ≤ (1/2:ℝ)^((q:ℝ)/4) := Real.rpow_le_rpow (by positivity) hsmall (by positivity)
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge' (by norm_num) (by norm_num)
      (by positivity) (by linarith)
/-- A concrete sufficient size bound for the link universe after a bounded number of deletions. -/
lemma rootLink_choose_universe_large {n d h : ℕ} (hd : 1≤d) (hn : d≤n)
    (hlarge : 2*h*d≤n) : 2*h≤n.choose d := by
  have hid : n.choose d*d=n*((n-1).choose (d-1)) := by
    simpa only [Nat.choose_one_right] using (Nat.choose_mul hd)
  have hpos : 1≤(n-1).choose (d-1) := Nat.choose_pos (Nat.sub_le_sub_right hn 1)
  have hmul : n≤n.choose d*d := by rw [hid]; nlinarith only [Nat.mul_le_mul_left n hpos]
  have hh := hlarge.trans hmul
  exact Nat.le_of_mul_le_mul_right hh (by omega)

lemma eventually_rootLink_universe_large (d h t : ℕ) (hd : 1≤d) :
    ∀ᶠ n : ℕ in atTop, 2*h≤(n-t).choose d := by
  filter_upwards [eventually_ge_atTop (t+max d (2*h*d))] with n hn
  apply rootLink_choose_universe_large hd <;> omega
end LooseHamilton
