module

public import HittingTimeLooseHamilton.StoppedCountingVariance
public import HittingTimeLooseHamilton.TerminalFeasibility

public section

noncomputable section
open scoped BigOperators
namespace LooseHamilton.FirstFailureRates
open Finset Filter

/-- A finite reciprocal-square tail estimate, uniform in its upper endpoint. -/
theorem reciprocal_square_sum_le {M K : ℕ} (hM : 0 < M) (hMK : M ≤ K) :
    (∑ j ∈ Ioc M K, (1 / (j : ℝ)) ^ 2) ≤ 1 / (M : ℝ) := by
  have hstrong : (∑ j ∈ Ioc M K, (1 / (j : ℝ)) ^ 2) ≤
      1 / (M : ℝ) - 1 / (K : ℝ) := by
    induction K, hMK using Nat.le_induction with
    | base => simp
    | succ K hMK ih =>
      rw [sum_Ioc_succ_top hMK]
      have hK : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le hM hMK)
      have hs : (1 / ((K+1 : ℕ) : ℝ)) ^ 2 ≤ 1 / (K : ℝ) - 1 / ((K+1 : ℕ) : ℝ) := by
        push_cast
        rw [div_pow, one_pow]
        apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < (K:ℝ)+1))).mpr
        apply (mul_le_mul_iff_left₀ hK).mp
        have he : (1/(K:ℝ)-1/((K:ℝ)+1))*((K:ℝ)+1)^2*(K:ℝ) = (K:ℝ)+1 := by
          field_simp <;> ring
        rw [he]
        linarith
      linarith
  exact hstrong.trans (sub_le_self _ (by positivity))

/-- The stopped quadratic budget is at most C0² k²/M. -/
theorem variance_le {M K : ℕ} (hM : 0<M) (hMK : M≤K) (C0 : ℝ) (k : ℕ) :
    StoppedCounting.variance C0 k M K ≤ (C0*k)^2 / M := by
  have he : StoppedCounting.variance C0 k M K =
      (C0*k)^2 * ∑ j ∈ Ioc M K, (1/(j:ℝ))^2 := by
    simp only [StoppedCounting.variance, mul_sum]
    apply sum_congr rfl
    intro j hj
    ring
  rw [he]
  simpa only [mul_one_div] using
    mul_le_mul_of_nonneg_left (reciprocal_square_sum_le hM hMK) (sq_nonneg (C0*k))

/-- Uniform stopped-budget and small-cap bounds throughout the core density window. -/
theorem eventually_core_budget (r : ℕ) (hr : 3 ≤ r) (C0 : ℝ) (hC0 : 0 ≤ C0) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (ell : Fin N → ℕ)
      (markers : Finset (Finset (Fin N))) (offset : ℝ),
      CoreAdmissible r m ell markers offset →
      0 < m ∧ C0 * ordinaryEdgeCount r markers / m ≤ (1/2:ℝ) ∧
      StoppedCounting.variance C0 (ordinaryEdgeCount r markers) m
        (completeEdges (Fin N) r).card ≤ (2*r*C0^2) * ((N:ℝ)/Real.log N) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_feasibility_parameters 0, eventually_ge_atTop (1:ℕ),
    hlog.eventually (eventually_ge_atTop (4*C0*r))] with N hparam hN hlarge
  intro m ell markers offset hadm
  have hN0 : (0:ℝ)<N := by exact_mod_cast hN
  have hr0 : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hL : 0 < Real.log (N:ℝ) := by linarith [hparam.1]
  have hd := hparam.2.1 (meanDegree (V:=Fin N) r m) (by simpa using hadm.density_window)
  simp only [meanDegree, Fintype.card_fin] at hd
  have hd' := (le_div_iff₀ hN0).mp hd
  have hdensity : (N:ℝ)*Real.log N ≤ 2*r*m := by nlinarith
  have hmR : (0:ℝ) < m := by
    have : 0 < (r:ℝ)*m := by nlinarith
    exact pos_of_mul_pos_right this (Nat.cast_nonneg _)
  have hm : 0 < m := by exact_mod_cast hmR
  have hk : (ordinaryEdgeCount r markers:ℝ) ≤ N := by
    unfold ordinaryEdgeCount
    simp only [Fintype.card_fin]
    exact_mod_cast ((Nat.div_le_self (N-markers.card) (r-1)).trans (Nat.sub_le N _))
  have hk0 : (0:ℝ) ≤ ordinaryEdgeCount r markers := Nat.cast_nonneg _
  have hcap : C0 * ordinaryEdgeCount r markers / m ≤ (1/2:ℝ) := by
    apply (div_le_iff₀ hmR).mpr
    have hmul : C0 * ordinaryEdgeCount r markers ≤ C0*N := mul_le_mul_of_nonneg_left hk hC0
    have hh : (4*C0*r)*(N:ℝ) ≤ (N:ℝ)*Real.log N := by nlinarith
    nlinarith
  refine ⟨hm,hcap,?_⟩
  obtain ⟨F⟩ := hadm.feasible
  have hv := variance_le hm (terminal_size_le F) C0 (ordinaryEdgeCount r markers)
  apply hv.trans
  apply (div_le_iff₀ hmR).mpr
  apply (mul_le_mul_iff_left₀ hL).mp
  have he : ((2*(r:ℝ)*C0^2)*((N:ℝ)/Real.log N)*(m:ℝ))*Real.log N =
      2*r*C0^2*N*m := by field_simp
  rw [he]
  have hs : (ordinaryEdgeCount r markers:ℝ)^2 ≤ (N:ℝ)^2 := by nlinarith
  have hs' := mul_le_mul_of_nonneg_left hs (mul_nonneg (sq_nonneg C0) hL.le)
  have hd' := mul_le_mul_of_nonneg_left hdensity (mul_nonneg (sq_nonneg C0) hN0.le)
  nlinarith
end LooseHamilton.FirstFailureRates
