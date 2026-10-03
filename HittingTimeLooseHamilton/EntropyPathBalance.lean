module

public import HittingTimeLooseHamilton.EntropyPathRatesLimit
public import HittingTimeLooseHamilton.EntropyPathRegularity
public import HittingTimeLooseHamilton.BiasedRoleMain

public section

/-! The explicit Section 6 entropy estimate on path-regular hosts. -/
noncomputable section
namespace LooseHamilton
open Filter BiasedRoleInstance

/-- The host may vary arbitrarily along the sequence. Uniform path regularity
and the printed entropy budget imply the explicit log-log rate. -/
theorem entropy_path_role_balance (r : ℕ) (hr : 3≤r) (C : ℝ) (hC : 0<C)
    (B L : ℝ) :
    ∃ K : ℝ, 0<K ∧ ∀ D : ℕ→BiasedRoleInstance r, ∀ ξ : ℕ→ℝ,
      Tendsto (fun n => (D n).μ) atTop atTop →
      (∀ᶠ n in atTop, ((D n).s:ℝ)≤L*((D n).N:ℝ)^(1/10:ℝ)) →
      (∀ᶠ n in atTop, PathGraphUpperRegular r C L (D n).host) →
      (∀ᶠ n in atTop, 0≤ξ n ∧ ξ n≤B/Real.sqrt (Real.log ((D n).N:ℝ))) →
      (∀ᶠ n in atTop, (D n).entropyBound (ξ n)) →
      ∀ᶠ n in atTop, (D n).deviation≤K*(D n).N/
        Real.sqrt (Real.log (Real.log ((D n).N:ℝ))) := by
  obtain ⟨K,hK,hmain⟩ := theorem61 r hr C hC
  refine ⟨4*K,by positivity,?_⟩
  intro D ξ hμ hs hreg hx hent
  have hN := N_tendsto_atTop D hμ
  have hNr := N_real_tendsto_atTop D hμ
  let δ : ℕ→ℝ := fun n => C*(Real.log ((D n).N:ℝ))^(-1/8:ℝ)
  have hs0 := tendsto_marker_ratio_of_power_envelope (fun n => (D n).N)
    (fun n => (D n).s) hN L hs
  have hξ := tendsto_zero_of_sqrt_log_envelope (fun n => (D n).N) hN ξ B
    (hx.mono fun _ h => h.1) (hx.mono fun _ h => h.2)
  have hδ : Tendsto δ atTop (nhds 0) := by
    simpa only [δ, neg_div] using tendsto_log_power_envelope (fun n => (D n).N) hN C
      (1/8) (by norm_num)
  have heta0 : ∀ᶠ n in atTop, 0≤(D n).η :=
    Eventually.of_forall (fun n => ((D n).η_pos hr).le)
  have hetab : ∀ᶠ n in atTop, (D n).η≤C*(Real.log ((D n).N:ℝ))^(-1/4:ℝ) :=
    hreg.mono (fun n h => (D n).regular_eta_le hr h)
  have hη := tendsto_zero_of_log_power_envelope (fun n => (D n).N) hN
    (fun n => (D n).η) C (1/4) (by norm_num) heta0 (by simpa only [neg_div] using hetab)
  have hp : ∀ᶠ n in atTop, (D n).partitionBound (δ n) := by
    filter_upwards [hreg,hs] with n hn hsn
    exact (D n).regular_partitionBound hr hn hsn
  have hb := hmain D ξ δ hμ hs0 hη hδ hξ (hx.mono fun _ h => h.1)
    (hreg.mono fun _ h => h.upper_degree) hp hent
  have he := hN.eventually (eventually_biasedRoleError_le_inv_loglog r hr C B L hC)
  have hlog : ∀ᶠ n in atTop, 0<Real.log (Real.log ((D n).N:ℝ)) :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hNr)).eventually
      (eventually_gt_atTop 0)
  filter_upwards [hb,he,hlog,hs,hx,hetab] with n hb he hl hs hx heta
  have herr := he (D n).s (ξ n) (δ n) (D n).η hs hx.2 (le_refl _)
    ((D n).η_pos hr) heta
  have hsq : Real.sqrt (biasedRoleError r (D n).N (D n).s (ξ n) (δ n) (D n).η)
      ≤ 4/Real.sqrt (Real.log (Real.log ((D n).N:ℝ))) := by
    calc
      _ ≤ Real.sqrt (13/Real.log (Real.log ((D n).N:ℝ))) := Real.sqrt_le_sqrt herr
      _ = Real.sqrt 13 / Real.sqrt (Real.log (Real.log ((D n).N:ℝ))) := Real.sqrt_div (by norm_num) _
      _ ≤ _ := div_le_div_of_nonneg_right (by apply Real.sqrt_le_iff.mpr; norm_num)
        (Real.sqrt_nonneg _)
  calc
    _ ≤ K*(D n).N*Real.sqrt (biasedRoleError r (D n).N (D n).s (ξ n) (δ n) (D n).η) := hb
    _ ≤ K*(D n).N*(4/Real.sqrt (Real.log (Real.log ((D n).N:ℝ)))) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring
end LooseHamilton
