module

public import HittingTimeLooseHamilton.BiasedRoleRelativeBudget
public import HittingTimeLooseHamilton.BiasedRoleErrorBounds
public import HittingTimeLooseHamilton.BiasedEntropyMeanConstants

public section

/-! Final assembly of the role deviation bound from the uniform three-deficit budget. -/
noncomputable section
namespace LooseHamilton
open Filter FiniteEntropy BiasedRoleInstance

/-- Intermediate entropy budget, with its constant uniform over all input sequences.
This is discharged by `eventual_entropy_deficit_bound` when proving Theorem 6.1. -/
@[expose] def EntropyDeficitBound : Prop :=
  ∀ r : ℕ, ∀ hr : 3≤r, ∀ C : ℝ, 0<C →
    ∃ B : ℝ, 0<B ∧ ∀ D : ℕ→BiasedRoleInstance r, ∀ ξ δ : ℕ→ℝ,
      Tendsto (fun n => (D n).μ) atTop atTop →
      Tendsto (fun n => ((D n).s:ℝ)/(D n).N) atTop (nhds 0) →
      Tendsto (fun n => (D n).η) atTop (nhds 0) →
      Tendsto δ atTop (nhds 0) → Tendsto ξ atTop (nhds 0) →
      (∀ᶠ n in atTop,0≤ξ n) →
      (∀ᶠ n in atTop,∀v,(vertexDegree (D n).host v:ℝ)≤C*(D n).μ) →
      (∀ᶠ n in atTop,(D n).partitionBound (δ n)) →
      (∀ᶠ n in atTop,(D n).entropyBound (ξ n)) →
      ∀ᶠ n in atTop,(D n).entropyDeficit hr≤B*(D n).N*
        biasedRoleError r (D n).N (D n).s (ξ n) (δ n) (D n).η

/-- The uniform constant is chosen before the host, matching and distribution
sequences. The only entropy hypothesis is on the original connected cycles. -/
theorem theorem61_of_entropy_deficit_bound (hbudget_all : EntropyDeficitBound) : Theorem61 := by
  intro r hr C hC
  obtain ⟨B,hB,hbudget⟩ := hbudget_all r hr C hC
  obtain ⟨J,hJ,hjunction⟩ := junctionDeficit_budget r hr
  let R := cloneRelativeConstant r C
  let b := (privateFraction r)^(r-2)
  have hR : 0<R := cloneRelativeConstant_pos hr C hC.le
  have hb : 0<b := privateFraction_pow_pos hr
  have hi : 0<b⁻¹ := inv_pos.mpr hb
  let A := 2+C+B+4*J+R+b⁻¹
  have hA : 2≤A := by dsimp [A]; linarith
  have hA0 : 0<A := by linarith
  have hCA : C≤A := by dsimp [A]; linarith
  have hBA : B≤A := by dsimp [A]; linarith
  have hBJA : B+4*J≤A := by dsimp [A]; linarith
  have hRA : R≤A := by dsimp [A]; linarith
  have hiA : b⁻¹≤A := by dsimp [A]; linarith
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hr1 : (0:ℝ)≤(r:ℝ)-1 := by linarith
  refine ⟨4*A+A^2+2*(r:ℝ)*((r:ℝ)-1)*A^3, by positivity, ?_⟩
  intro D ξ δ hμ hs hη hδ hξ hx hdeg hpart hent
  have hbud := hbudget D ξ δ hμ hs hη hδ hξ hx hdeg hpart hent
  have hE0 := error_eventually_nonneg hr D ξ δ hη hx hpart
  have hE1 := error_eventually_le_one hr D ξ δ hμ hs hη hξ hδ
  have hμ1 := eventually_mu_one D hμ
  have hsmall := eventually_sparse_marker_range hr D hs
  have hlog := eventually_log_N_one D hμ
  have heta := hη.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hbud,hE0,hE1,hμ1,hsmall,hlog,hx,hdeg,hpart,heta]
    with n hbud hE0 hE1 hμ1 hsmall hlog hx hdeg hpart heta
  let T := D n
  let E := biasedRoleError r T.N T.s (ξ n) (δ n) T.η
  change T.s<T.k ∧ 3*T.s≤T.N ∧ _ at hsmall
  have hN : (0:ℝ)<T.N := Nat.cast_pos.mpr T.N_pos
  have hmu : 0<T.μ := T.μ_pos hr
  have hrole := T.roleDeficit_nonneg hr
  have hlocal := T.meanLocalDeficit_nonneg hr
  have hdegree := T.meanDegreeDeficit_nonneg hr
  have hrole_le : T.roleDeficit≤T.entropyDeficit hr := by
    unfold entropyDeficit
    linarith
  have hloc_le : T.meanLocalDeficit hr+T.meanDegreeDeficit hr≤T.entropyDeficit hr := by
    unfold entropyDeficit
    linarith
  have hL : T.meanLocalDeficit hr+T.meanDegreeDeficit hr≤A*T.N*E := by
    calc
      _ ≤ T.entropyDeficit hr := hloc_le
      _ ≤ B*T.N*E := hbud
      _ ≤ A*T.N*E := by gcongr
  have hround := error_controls_rounding hr T hx hpart heta hlog
  have hj := hjunction T hsmall.1 (by have hh := hsmall.2.1; omega)
  have hbits : T.junctionDeficit hr≤A*T.N*E := by
    have hjr := mul_le_mul_of_nonneg_left hround hJ
    have hb' : T.roleDeficit≤B*T.N*E := hrole_le.trans hbud
    have hmul := mul_le_mul_of_nonneg_right hBJA (mul_nonneg hN.le hE0)
    change _ ≤ 4*(T.N:ℝ)*E at hround
    change _ ≤ T.roleDeficit+J*((T.s:ℝ)+Real.log ((T.N:ℝ)+1)+1) at hj
    nlinarith only [hj,hjr,hb',hmul]
  have hterms := T.error_term_bounds hr hx hpart heta
  have hsE : δ n+(T.s:ℝ)/T.N≤E := hterms.2.2.2.2.2.2.2
  have ht0 := T.meanRelativeError_le hr C (δ n) hC.le hμ1 hdeg
    (by have hh := hsmall.2.1; omega) hpart
  have ht : T.meanRelativeError hr≤A*E := by
    calc
      _ ≤ R*(δ n+(T.s:ℝ)/T.N) := ht0
      _ ≤ R*E := mul_le_mul_of_nonneg_left hsE hR.le
      _ ≤ A*E := mul_le_mul_of_nonneg_right hRA hE0
  have hv : ((r*T.k:ℕ):ℝ)≤A*T.N := by
    have hn : ((r*T.k:ℕ):ℝ)≤2*T.N := by exact_mod_cast T.rk_le_two_N hr
    exact hn.trans (mul_le_mul_of_nonneg_right hA hN.le)
  have hlam : T.μ/A≤T.cloneLambda0 := by
    apply (div_le_iff₀ hA0).mpr
    have hm := mul_le_mul_of_nonneg_left hiA hb.le
    have hba : 1≤b*A := by simpa only [mul_inv_cancel₀ hb.ne'] using hm
    change T.μ≤(b*T.μ)*A
    nlinarith only [mul_le_mul_of_nonneg_left hba hmu.le]
  exact T.finite_entropy_balance hr A C E hA hC.le hCA hE0 hE1 hdeg hv hL ht hbits hlam
end LooseHamilton
