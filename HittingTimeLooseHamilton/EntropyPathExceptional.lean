module

public import HittingTimeLooseHamilton.EntropyPathBalance
public import HittingTimeLooseHamilton.EntropyExceptionalRate

public section

noncomputable section
namespace LooseHamilton
open Filter BiasedRoleInstance

lemma BiasedRoleInstance.eligible_half_of_marker_ratio {r : ℕ}
    (D : BiasedRoleInstance r) (hr : 3≤r) {C : ℝ} (hC : 0<C)
    (hdeg : ∀ v, (vertexDegree D.host v:ℝ)≤C*D.μ)
    (hs : (D.s:ℝ)/D.N ≤ 1/(4*(r:ℝ)*C)) :
    (D.host.card:ℝ)/2≤D.eligibleEdges.card := by
  apply D.eligible_edge_half hdeg
  have hN : (0:ℝ)<D.N := Nat.cast_pos.mpr D.N_pos
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hr1 : (0:ℝ)<(r:ℝ)-1 := by linarith
  have hr0 : (0:ℝ)<r := by linarith
  have hμ := D.μ_pos hr
  have hm : (r:ℝ)*(D.host.card:ℝ)=D.μ*D.N := by
    unfold μ meanDegree
    simp only [Fintype.card_fin]
    field_simp
  have hs' := (div_le_iff₀ hN).mp hs
  have hs'' := mul_le_mul_of_nonneg_right hs' (show 0≤4*(r:ℝ)*C by positivity)
  have he : 1/(4*(r:ℝ)*C)*(D.N:ℝ)*(4*(r:ℝ)*C)=D.N := by field_simp
  rw [he] at hs''
  have ht := mul_le_mul_of_nonneg_right hs'' hμ.le
  apply (mul_le_mul_iff_right₀ (show (0:ℝ)<r by linarith)).mp
  nlinarith [hm]

/-- At every fixed positive relative tolerance, the exceptional fraction of
existing eligible directed roles has the printed iterated-logarithm rate. -/
theorem entropy_path_exceptional_roles (r : ℕ) (hr : 3≤r) (C : ℝ) (hC : 0<C)
    (B L : ℝ) :
    ∃ K : ℝ, 0<K ∧ ∀ D : ℕ→BiasedRoleInstance r, ∀ ξ : ℕ→ℝ,
      Tendsto (fun n => (D n).μ) atTop atTop →
      (∀ᶠ n in atTop, ((D n).s:ℝ)≤L*((D n).N:ℝ)^(1/10:ℝ)) →
      (∀ᶠ n in atTop, PathGraphUpperRegular r C L (D n).host) →
      (∀ᶠ n in atTop, 0≤ξ n ∧ ξ n≤B/Real.sqrt (Real.log ((D n).N:ℝ))) →
      (∀ᶠ n in atTop, (D n).entropyBound (ξ n)) →
      ∀ t : ℝ, 0<t → ∀ᶠ n in atTop,
        (D n).exceptionalProportion t≤K/(t*Real.sqrt (Real.log (Real.log ((D n).N:ℝ)))) := by
  obtain ⟨K,hK,hbal⟩ := entropy_path_role_balance r hr C hC B L
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hr1 : (0:ℝ)<(r:ℝ)-1 := by linarith
  have hr0 : (0:ℝ)<r := by linarith
  refine ⟨2*((r:ℝ)-1)*K,by positivity,?_⟩
  intro D ξ hμ hs hreg hx hent t ht
  have hN := N_tendsto_atTop D hμ
  have hNr := N_real_tendsto_atTop D hμ
  have hs0 := tendsto_marker_ratio_of_power_envelope (fun n => (D n).N)
    (fun n => (D n).s) hN L hs
  have hsmall := hs0.eventually (gt_mem_nhds (show (0:ℝ)<1/(4*(r:ℝ)*C) by positivity))
  have hlog := (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hNr)).eventually
    (eventually_gt_atTop 0)
  filter_upwards [hbal D ξ hμ hs hreg hx hent,hreg,hsmall,hlog] with n hn hreg hs hl
  exact (D n).exceptionalProportion_rate hr hK.le (Real.sqrt_pos.mpr hl) ht
    ((D n).eligible_half_of_marker_ratio hr hC hreg.upper_degree hs.le) hn
end LooseHamilton
