module

public import HittingTimeLooseHamilton.PathIncidenceAggregation

public section

/-! Polynomial union factors for incidence regularity. -/
noncomputable section
namespace LooseHamilton
open Filter Topology

lemma incidence_polynomial_union_bound (n r : ℕ) (hn : 1 ≤ n) :
    (2*(n:ℝ)+(n:ℝ)^2)*((n.choose r:ℝ)+1)*(n:ℝ)^(-((r:ℝ)+5)) ≤
      6*(n:ℝ)^(-3:ℝ) := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have h1 : 2*(n:ℝ)+(n:ℝ)^2 ≤ 3*(n:ℝ)^2 := by nlinarith
  have h2 : (n.choose r:ℝ)+1 ≤ 2*(n:ℝ)^r := by
    have hc : (n.choose r:ℝ) ≤ (n:ℝ)^r := by exact_mod_cast Nat.choose_le_pow n r
    have hp := one_le_pow₀ hn1 (n:=r)
    linarith
  calc
    _ ≤ (3*(n:ℝ)^2)*(2*(n:ℝ)^r)*(n:ℝ)^(-((r:ℝ)+5)) := by gcongr
    _ = _ := by
      rw [show (n:ℝ)^2 = (n:ℝ)^(2:ℝ) by norm_num,
        show (n:ℝ)^r = (n:ℝ)^(r:ℝ) by rw [Real.rpow_natCast]]
      calc
        _ = 6*((n:ℝ)^(2:ℝ)*(n:ℝ)^(r:ℝ)*(n:ℝ)^(-((r:ℝ)+5))) := by ring
        _ = _ := by rw [←Real.rpow_add hn0,←Real.rpow_add hn0]; congr 2; ring

@[expose] def pathIncidenceError (r n : ℕ) : ℝ := terminalRegularityError r n + 6*(n:ℝ)^(-3:ℝ)

lemma pathIncidenceError_tendsto (r : ℕ) : Tendsto (pathIncidenceError r) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (n:ℝ)^(-3:ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3)).comp tendsto_natCast_atTop_atTop
  unfold pathIncidenceError
  simpa only [mul_zero,add_zero] using (terminalRegularityError_tendsto r).add (hpow.const_mul 6)
end LooseHamilton
