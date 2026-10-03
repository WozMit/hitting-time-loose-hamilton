module

public import HittingTimeLooseHamilton.EntropyPathExceptional
public import HittingTimeLooseHamilton.FrameScales

public section

/-! Uniformity in the relative tolerance for the entropy exceptional-role estimate.
The eventual index below is independent of the tolerance, permitting the shrinking
candidate tolerance used in Section 8. -/
noncomputable section
namespace LooseHamilton
open Filter BiasedRoleInstance

/-- A single eventual set works simultaneously for every positive tolerance.
The constant is chosen before the host sequence and the entropy-error sequence. -/
theorem entropy_path_exceptional_roles_uniform (r : ℕ) (hr : 3≤r)
    (C : ℝ) (hC : 0<C) (B L : ℝ) :
    ∃ K : ℝ, 0<K ∧ ∀ D : ℕ→BiasedRoleInstance r, ∀ ξ : ℕ→ℝ,
      Tendsto (fun n => (D n).μ) atTop atTop →
      (∀ᶠ n in atTop, ((D n).s:ℝ)≤L*((D n).N:ℝ)^(1/10:ℝ)) →
      (∀ᶠ n in atTop, PathGraphUpperRegular r C L (D n).host) →
      (∀ᶠ n in atTop, 0≤ξ n ∧ ξ n≤B/Real.sqrt (Real.log ((D n).N:ℝ))) →
      (∀ᶠ n in atTop, (D n).entropyBound (ξ n)) →
      ∀ᶠ n in atTop, ∀ t : ℝ, 0<t →
        (D n).exceptionalProportion t≤
          K/(t*Real.sqrt (Real.log (Real.log ((D n).N:ℝ)))) := by
  obtain ⟨K,hK,hbal⟩ := entropy_path_role_balance r hr C hC B L
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hr1 : (0:ℝ)<(r:ℝ)-1 := by linarith
  have hr0 : (0:ℝ)<r := by linarith
  refine ⟨2*((r:ℝ)-1)*K,by positivity,?_⟩
  intro D ξ hμ hs hreg hx hent
  have hN := N_tendsto_atTop D hμ
  have hNr := N_real_tendsto_atTop D hμ
  have hs0 := tendsto_marker_ratio_of_power_envelope (fun n => (D n).N)
    (fun n => (D n).s) hN L hs
  have hsmall := hs0.eventually
    (gt_mem_nhds (show (0:ℝ)<1/(4*(r:ℝ)*C) by positivity))
  have hlog := (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hNr)).eventually
    (eventually_gt_atTop 0)
  filter_upwards [hbal D ξ hμ hs hreg hx hent,hreg,hsmall,hlog] with n hn hreg hs hl
  intro t ht
  exact (D n).exceptionalProportion_rate hr hK.le (Real.sqrt_pos.mpr hl) ht
    ((D n).eligible_half_of_marker_ratio hr hC hreg.upper_degree hs.le) hn

/-- The same constant works for an arbitrary varying positive tolerance,
including tolerances tending to zero. -/
theorem entropy_path_exceptional_roles_varying (r : ℕ) (hr : 3≤r)
    (C : ℝ) (hC : 0<C) (B L : ℝ) :
    ∃ K : ℝ, 0<K ∧ ∀ D : ℕ→BiasedRoleInstance r, ∀ ξ t : ℕ→ℝ,
      Tendsto (fun n => (D n).μ) atTop atTop →
      (∀ᶠ n in atTop, ((D n).s:ℝ)≤L*((D n).N:ℝ)^(1/10:ℝ)) →
      (∀ᶠ n in atTop, PathGraphUpperRegular r C L (D n).host) →
      (∀ᶠ n in atTop, 0≤ξ n ∧ ξ n≤B/Real.sqrt (Real.log ((D n).N:ℝ))) →
      (∀ᶠ n in atTop, (D n).entropyBound (ξ n)) →
      (∀ᶠ n in atTop, 0<t n) →
      ∀ᶠ n in atTop,
        (D n).exceptionalProportion (t n)≤
          K/(t n*Real.sqrt (Real.log (Real.log ((D n).N:ℝ)))) := by
  obtain ⟨K,hK,huniform⟩ := entropy_path_exceptional_roles_uniform r hr C hC B L
  refine ⟨K,hK,?_⟩
  intro D ξ t hμ hs hreg hx hent ht
  filter_upwards [huniform D ξ hμ hs hreg hx hent,ht] with n hn htn
  exact hn (t n) htn

/-- The tolerance alpha/100 used for candidate roles is allowed to shrink
with the host size; its positivity is a conclusion of the scale estimates. -/
theorem entropy_path_exceptional_roles_candidate_tolerance (r : ℕ) (hr : 3≤r)
    (C : ℝ) (hC : 0<C) (B L : ℝ) :
    ∃ K : ℝ, 0<K ∧ ∀ D : ℕ→BiasedRoleInstance r, ∀ ξ : ℕ→ℝ,
      Tendsto (fun n => (D n).μ) atTop atTop →
      (∀ᶠ n in atTop, ((D n).s:ℝ)≤L*((D n).N:ℝ)^(1/10:ℝ)) →
      (∀ᶠ n in atTop, PathGraphUpperRegular r C L (D n).host) →
      (∀ᶠ n in atTop, 0≤ξ n ∧ ξ n≤B/Real.sqrt (Real.log ((D n).N:ℝ))) →
      (∀ᶠ n in atTop, (D n).entropyBound (ξ n)) →
      ∀ᶠ n in atTop,
        (D n).exceptionalProportion (FrameScales.alpha (D n).N/100)≤
          K/((FrameScales.alpha (D n).N/100)*
            Real.sqrt (Real.log (Real.log ((D n).N:ℝ)))) := by
  obtain ⟨K,hK,hvary⟩ := entropy_path_exceptional_roles_varying r hr C hC B L
  refine ⟨K,hK,?_⟩
  intro D ξ hμ hs hreg hx hent
  apply hvary D ξ (fun n => FrameScales.alpha (D n).N/100) hμ hs hreg hx hent
  filter_upwards [(N_tendsto_atTop D hμ).eventually FrameScales.eventual_range] with n hn
  exact div_pos hn.2.2.2.1 (by norm_num)

end LooseHamilton
