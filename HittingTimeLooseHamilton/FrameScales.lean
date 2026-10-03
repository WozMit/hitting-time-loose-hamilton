module

public import HittingTimeLooseHamilton.ExceptionalSetAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

public section

/-! The three iterated logarithms and the exact Section 7 scales. -/
noncomputable section
namespace LooseHamilton.FrameScales
open Filter Topology

@[expose] def L1 (N : ℕ) : ℝ := Real.log (N:ℝ)
@[expose] def L2 (N : ℕ) : ℝ := Real.log (L1 N)
@[expose] def L3 (N : ℕ) : ℝ := Real.log (L2 N)
@[expose] def alpha (N : ℕ) : ℝ := (L3 N)^(-1/100:ℝ)
@[expose] def nu (N : ℕ) : ℝ := L3 N/100
@[expose] def rho (N : ℕ) : ℝ := (alpha N)^(1/8:ℝ)

lemma L1_tendsto : Tendsto L1 atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
lemma L2_tendsto : Tendsto L2 atTop atTop := Real.tendsto_log_atTop.comp L1_tendsto
lemma L3_tendsto : Tendsto L3 atTop atTop := Real.tendsto_log_atTop.comp L2_tendsto
lemma nu_tendsto : Tendsto nu atTop atTop := L3_tendsto.atTop_div_const (by norm_num)
lemma alpha_tendsto_zero : Tendsto alpha atTop (nhds 0) := by
  unfold alpha
  simpa only [Function.comp_def,neg_div] using
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/100)).comp L3_tendsto
lemma rho_tendsto_zero : Tendsto rho atTop (nhds 0) := by
  have h := alpha_tendsto_zero.rpow_const (p := (1/8:ℝ)) (Or.inr (by norm_num))
  unfold rho
  simpa [Real.zero_rpow (by norm_num : (1/8:ℝ)≠0)] using h

lemma eventual_range : ∀ᶠN in atTop,
    0<L1 N ∧ 0<L2 N ∧ 1<L3 N ∧ 0<alpha N ∧ alpha N<1 ∧
      0<nu N ∧ 0<rho N ∧ rho N<1 := by
  filter_upwards [L1_tendsto.eventually (eventually_gt_atTop 0),
    L2_tendsto.eventually (eventually_gt_atTop 0),
    L3_tendsto.eventually (eventually_gt_atTop 1)] with N h1 h2 h3
  have ha : 0<alpha N := Real.rpow_pos_of_pos (by linarith) _
  have ha1 : alpha N<1 := Real.rpow_lt_one_of_one_lt_of_neg h3 (by norm_num)
  refine ⟨h1,h2,h3,ha,ha1,?_,Real.rpow_pos_of_pos ha _,?_⟩
  · exact div_pos (by linarith) (by norm_num)
  · exact Real.rpow_lt_one ha.le ha1 (by norm_num)

lemma nu_div_vertices_tendsto_zero :
    Tendsto (fun N => nu N/(N:ℝ)) atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)/(N:ℝ)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hupper := hlog.div_const 100
  simp only [zero_div] at hupper
  apply squeeze_zero' _ _ hupper
  · filter_upwards [eventual_range] with N hN
    exact div_nonneg hN.2.2.2.2.2.1.le (Nat.cast_nonneg _)
  · filter_upwards [eventual_range] with N hN
    have h21 : L2 N≤L1 N := by
      have h := Real.log_le_sub_one_of_pos hN.1
      dsimp [L2]; linarith
    have h32 : L3 N≤L2 N := by
      have h := Real.log_le_sub_one_of_pos hN.2.1
      dsimp [L3]; linarith
    have hh := div_le_div_of_nonneg_right (h32.trans h21) (by norm_num : (0:ℝ)≤100)
    have hf := div_le_div_of_nonneg_right hh (Nat.cast_nonneg N : (0:ℝ)≤N)
    simpa only [nu,L1,div_div,mul_comm] using hf
end LooseHamilton.FrameScales
