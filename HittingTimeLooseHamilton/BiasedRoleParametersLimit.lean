module

public import HittingTimeLooseHamilton.BiasedRoleParameters
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

public section

noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open Filter Topology
variable {r : ℕ}

lemma N_tendsto_atTop (D : ℕ → BiasedRoleInstance r)
    (hμ : Tendsto (fun n => (D n).μ) atTop atTop) :
    Tendsto (fun n => (D n).N) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  filter_upwards [hμ.eventually (eventually_gt_atTop ((r:ℝ)*2^K))] with n hn
  by_contra h
  have hNK : (D n).N ≤ K := by omega
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hNK
  have hm := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg r : (0:ℝ)≤r)
  linarith [(D n).μ_le_exponential]

lemma N_real_tendsto_atTop (D : ℕ → BiasedRoleInstance r)
    (hμ : Tendsto (fun n => (D n).μ) atTop atTop) :
    Tendsto (fun n => ((D n).N:ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (N_tendsto_atTop D hμ)

/-- One common eventual range used by all subsequent entropy estimates. -/
lemma eventually_sparse_marker_range (hr : 3 ≤ r) (D : ℕ → BiasedRoleInstance r)
    (hs : Tendsto (fun n => ((D n).s:ℝ)/(D n).N) atTop (nhds 0)) :
    ∀ᶠ n in atTop, (D n).s < (D n).k ∧ 3*(D n).s ≤ (D n).N ∧
      ((D n).N:ℝ)/(2*((r:ℝ)-1)) ≤ (D n).k := by
  have hrR : (3:ℝ) ≤ r := by exact_mod_cast hr
  have hc : (0:ℝ) < 1/(4*r) := by positivity
  filter_upwards [hs.eventually (gt_mem_nhds hc)] with n hn
  have hN : (0:ℝ)<(D n).N := Nat.cast_pos.mpr (D n).N_pos
  have hbook : ((D n).N:ℝ)=((r:ℝ)-1)*(D n).k+(D n).s := by
    have h := congrArg (fun m : ℕ => (m:ℝ)) ((D n).vertex_bookkeeping hr)
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (show 1≤r by omega),Nat.cast_one] using h
  have hsmall : ((D n).s:ℝ)*(4*r) < (D n).N := by
    have hh := (div_lt_iff₀ hN).mp hn
    have hh' := (lt_div_iff₀ (show (0:ℝ)<4*r by positivity)).mp (show ((D n).s:ℝ)<(D n).N/(4*r) by simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hh)
    exact hh'
  have hs0 : (0:ℝ)≤(D n).s := Nat.cast_nonneg _
  have hk0 : (0:ℝ)≤(D n).k := Nat.cast_nonneg _
  have hsk : ((D n).s:ℝ)<(D n).k := by nlinarith
  have h3 : 3*((D n).s:ℝ)≤(D n).N := by nlinarith
  refine ⟨by exact_mod_cast hsk,by exact_mod_cast h3,?_⟩
  apply (div_le_iff₀ (show (0:ℝ)<2*((r:ℝ)-1) by linarith)).2
  nlinarith

lemma k_tendsto_atTop (hr : 3 ≤ r) (D : ℕ → BiasedRoleInstance r)
    (hμ : Tendsto (fun n => (D n).μ) atTop atTop)
    (hs : Tendsto (fun n => ((D n).s:ℝ)/(D n).N) atTop (nhds 0)) :
    Tendsto (fun n => (D n).k) atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R:=ℝ)).mp
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have htop := (N_real_tendsto_atTop D hμ).atTop_div_const (show (0:ℝ)<2*((r:ℝ)-1) by linarith)
  apply tendsto_atTop_mono' atTop _ htop
  filter_upwards [eventually_sparse_marker_range hr D hs] with n hn
  exact hn.2.2

lemma eventually_mu_one (D : ℕ → BiasedRoleInstance r)
    (hμ : Tendsto (fun n => (D n).μ) atTop atTop) :
    ∀ᶠ n in atTop, 1 ≤ (D n).μ := hμ.eventually (eventually_ge_atTop 1)

end LooseHamilton.BiasedRoleInstance
