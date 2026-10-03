module

public import HittingTimeLooseHamilton.BiasedRoleParametersLimit
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

public section

noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open Filter Topology
variable {r : ℕ}

lemma log_inv_eta_tendsto_atTop (hr : 3 ≤ r) (D : ℕ → BiasedRoleInstance r)
    (hη : Tendsto (fun n => (D n).η) atTop (nhds 0)) :
    Tendsto (fun n => Real.log (1/(D n).η)) atTop atTop := by
  have hw : Tendsto (fun n => (D n).η) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hη,Eventually.of_forall (fun n => (D n).η_pos hr)⟩
  have hi := tendsto_inv_nhdsGT_zero.comp hw
  simpa only [one_div, Function.comp_def] using Real.tendsto_log_atTop.comp hi

lemma error_tendsto_zero (hr : 3 ≤ r) (D : ℕ → BiasedRoleInstance r)
    (ξ δ : ℕ → ℝ)
    (hμ : Tendsto (fun n => (D n).μ) atTop atTop)
    (hs : Tendsto (fun n => ((D n).s:ℝ)/(D n).N) atTop (nhds 0))
    (hη : Tendsto (fun n => (D n).η) atTop (nhds 0))
    (hξ : Tendsto ξ atTop (nhds 0)) (hδ : Tendsto δ atTop (nhds 0)) :
    Tendsto (fun n => biasedRoleError r (D n).N (D n).s (ξ n) (δ n) (D n).η)
      atTop (nhds 0) := by
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hexp : (0:ℝ)<1/(2*((r:ℝ)-1)) := one_div_pos.mpr (by linarith)
  have hp : Tendsto (fun n => (D n).η ^ (1/(2*((r:ℝ)-1)))) atTop (nhds 0) := by
    have hh := (Real.continuousAt_rpow_const 0 _ (Or.inr hexp.le)).tendsto.comp hη
    simpa only [Real.zero_rpow hexp.ne', Function.comp_def] using hh
  have hi : Tendsto (fun n => 1/Real.log (1/(D n).η)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (log_inv_eta_tendsto_atTop hr D hη)
  have hn : Tendsto (fun n => Real.log ((D n).N:ℝ)/(D n).N) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (N_real_tendsto_atTop D hμ)
  simpa only [biasedRoleError,zero_add,add_zero] using ((((hξ.add hδ).add hs).add hp).add hi).add hn

lemma error_eventually_nonneg (hr : 3 ≤ r) (D : ℕ → BiasedRoleInstance r)
    (ξ δ : ℕ → ℝ)
    (hη : Tendsto (fun n => (D n).η) atTop (nhds 0))
    (hξ : ∀ᶠ n in atTop, 0 ≤ ξ n)
    (hδ : ∀ᶠ n in atTop, (D n).partitionBound (δ n)) :
    ∀ᶠ n in atTop, 0 ≤ biasedRoleError r (D n).N (D n).s (ξ n) (δ n) (D n).η := by
  filter_upwards [hξ,hδ,hη.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hxn hdn hen
  have hd := (D n).partitionBound_nonneg hr hdn
  have hp := (D n).η_pos hr
  have hlog : 0 ≤ Real.log (1/(D n).η) :=
    Real.log_nonneg (by exact (one_le_div hp).mpr hen.le)
  have hN : (1:ℝ)≤(D n).N := by exact_mod_cast (D n).N_pos
  unfold biasedRoleError
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg hxn hd)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) (Real.rpow_nonneg hp.le _))
    (div_nonneg (by norm_num) hlog))
    (div_nonneg (Real.log_nonneg hN) (Nat.cast_nonneg _))

/-- The sparse-marker and logarithmic rounding costs fit inside N times the
printed error, with an absolute constant. -/
lemma error_controls_rounding (hr : 3 ≤ r) (D : BiasedRoleInstance r)
    {ξ δ : ℝ} (hξ : 0≤ξ) (hδ : D.partitionBound δ)
    (hη : D.η < 1) (hlogN : 1 ≤ Real.log (D.N:ℝ)) :
    (D.s:ℝ)+Real.log ((D.N:ℝ)+1)+1 ≤
      4*(D.N:ℝ)*biasedRoleError r D.N D.s ξ δ D.η := by
  have hp := D.η_pos hr
  have hd := D.partitionBound_nonneg hr hδ
  have hn : (0:ℝ)<D.N := Nat.cast_pos.mpr D.N_pos
  have hn1 : (1:ℝ)≤D.N := by exact_mod_cast D.N_pos
  have hli : 0≤1/Real.log (1/D.η) := div_nonneg (by norm_num)
    (Real.log_nonneg ((one_le_div hp).mpr hη.le))
  have hpow : 0≤D.η^(1/(2*((r:ℝ)-1))) := Real.rpow_nonneg hp.le _
  have hsN : 0≤(D.s:ℝ)/D.N := div_nonneg (Nat.cast_nonneg _) hn.le
  have hlN : 0≤Real.log (D.N:ℝ)/D.N := div_nonneg (by linarith) hn.le
  have hE : (D.s:ℝ)/D.N+Real.log (D.N:ℝ)/D.N ≤
      biasedRoleError r D.N D.s ξ δ D.η := by unfold biasedRoleError; linarith
  have hm := mul_le_mul_of_nonneg_left hE hn.le
  have hm' : (D.s:ℝ)+Real.log (D.N:ℝ) ≤
      (D.N:ℝ)*biasedRoleError r D.N D.s ξ δ D.η := by
    simpa only [mul_add,mul_div_cancel₀ _ hn.ne'] using hm
  have hadd : Real.log ((D.N:ℝ)+1) ≤ Real.log (D.N:ℝ)+1 := by
    have hh := Real.log_le_log (by positivity : (0:ℝ)<(D.N:ℝ)+1)
      (show (D.N:ℝ)+1≤2*(D.N:ℝ) by linarith)
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hn.ne'] at hh
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  nlinarith [(show (0:ℝ)≤D.s from Nat.cast_nonneg _)]

end LooseHamilton.BiasedRoleInstance
