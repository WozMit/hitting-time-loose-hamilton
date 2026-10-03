module

public import HittingTimeLooseHamilton.BiasedRoleParametersError

public section

noncomputable section
namespace LooseHamilton

/-- Each displayed summand is controlled by the complete printed error. -/
theorem biasedRoleError_term_bounds (r N s : ℕ) (ξ δ η : ℝ)
    (hN : 1≤N) (hξ : 0≤ξ) (hδ : 0≤δ) (hη0 : 0<η) (hη1 : η<1) :
    let E := biasedRoleError r N s ξ δ η
    0≤E ∧ ξ≤E ∧ δ≤E ∧ (s:ℝ)/N≤E ∧
      η^(1/(2*((r:ℝ)-1)))≤E ∧ 1/Real.log (1/η)≤E ∧
      Real.log (N:ℝ)/N≤E ∧ δ+(s:ℝ)/N≤E := by
  have hNR : (1:ℝ)≤N := by exact_mod_cast hN
  have hs : 0≤(s:ℝ)/N := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hp : 0≤η^(1/(2*((r:ℝ)-1))) := Real.rpow_nonneg hη0.le _
  have hi : 0≤1/Real.log (1/η) := div_nonneg (by norm_num)
    (Real.log_nonneg ((one_le_div hη0).mpr hη1.le))
  have hl : 0≤Real.log (N:ℝ)/N := div_nonneg (Real.log_nonneg hNR) (Nat.cast_nonneg _)
  dsimp only [biasedRoleError]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

namespace BiasedRoleInstance
open Filter Topology
variable {r : ℕ}

lemma k_le_N (D : BiasedRoleInstance r) (hr : 3≤r) : D.k≤D.N := by
  have h := D.vertex_bookkeeping hr
  have hm := Nat.mul_le_mul_right D.k (show 1≤r-1 by omega)
  nlinarith

lemma rk_le_two_N (D : BiasedRoleInstance r) (hr : 3≤r) : r*D.k≤2*D.N := by
  have h := D.vertex_bookkeeping hr
  have hk := D.k_le_N hr
  have he : r*D.k=(r-1)*D.k+D.k := by
    have hr1 : r=(r-1)+1 := by omega
    calc
      r*D.k=((r-1)+1)*D.k := congrArg (fun z => z*D.k) hr1
      _ = _ := by rw [Nat.add_mul,Nat.one_mul]
  omega

lemma error_term_bounds (D : BiasedRoleInstance r) (hr : 3≤r)
    {ξ δ : ℝ} (hξ : 0≤ξ) (hδ : D.partitionBound δ) (hη : D.η<1) :
    let E := biasedRoleError r D.N D.s ξ δ D.η
    0≤E ∧ ξ≤E ∧ δ≤E ∧ (D.s:ℝ)/D.N≤E ∧
      D.η^(1/(2*((r:ℝ)-1)))≤E ∧ 1/Real.log (1/D.η)≤E ∧
      Real.log (D.N:ℝ)/D.N≤E ∧ δ+(D.s:ℝ)/D.N≤E :=
  biasedRoleError_term_bounds r D.N D.s ξ δ D.η D.N_pos hξ
    (D.partitionBound_nonneg hr hδ) (D.η_pos hr) hη

lemma eventually_log_N_one (D : ℕ → BiasedRoleInstance r)
    (hμ : Tendsto (fun n => (D n).μ) atTop atTop) :
    ∀ᶠ n in atTop, 1≤Real.log ((D n).N:ℝ) :=
  (Real.tendsto_log_atTop.comp (N_real_tendsto_atTop D hμ)).eventually (eventually_ge_atTop 1)

lemma error_eventually_le_one (hr : 3≤r) (D : ℕ → BiasedRoleInstance r)
    (ξ δ : ℕ → ℝ)
    (hμ : Tendsto (fun n => (D n).μ) atTop atTop)
    (hs : Tendsto (fun n => ((D n).s:ℝ)/(D n).N) atTop (nhds 0))
    (hη : Tendsto (fun n => (D n).η) atTop (nhds 0))
    (hξ : Tendsto ξ atTop (nhds 0)) (hδ : Tendsto δ atTop (nhds 0)) :
    ∀ᶠ n in atTop, biasedRoleError r (D n).N (D n).s (ξ n) (δ n) (D n).η≤1 := by
  filter_upwards [(error_tendsto_zero hr D ξ δ hμ hs hη hξ hδ).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  exact hn.le

end BiasedRoleInstance
end LooseHamilton
