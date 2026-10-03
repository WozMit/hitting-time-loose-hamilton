module

public import HittingTimeLooseHamilton.FrameSampledAbnormalCounting
public import HittingTimeLooseHamilton.FrameSampledAbnormalConditional
public import HittingTimeLooseHamilton.FrameSampledRoleCountingBounds
public import HittingTimeLooseHamilton.FrameSampledEntropyUniform

public section

/-! Actual sampled abnormal-role expectation under the original source event. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival Filter FrameScales
open scoped BigOperators
local instance sampledAbnormalMeanPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable

/-- The common main-survival indicator stays outside the sampled role count.
The constant and threshold precede all frames, times, boundaries and exposures. -/
theorem inherited_sampled_bad_mean_eventually (r b : ℕ) (hr : 3 ≤ r)
    (C B L : ℝ) (hC : 0 < C) (hB : 0 ≤ B) (hL : 0 < L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (M : ℕ) (ell : Fin N → ℕ) (original : Finset (Finset (Fin N)))
        (offset : ℝ), CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card ≤ b →
      ∀ (j h : ℕ) (c : ℝ) (ω : Outcome (Fin N) r M ell),
        4*r ≤ h → M ≤ j → j ≤ (completeEdges (Fin N) r).card →
        InheritedRegularity original j h c C L ω →
        f.entropyBudget (extensionState ω.1 ω.2 j) B →
      let H := extensionState ω.1 ω.2 j
      ∃ hτ : batchSize f D H ≤ (unexposed f D H).card,
      (hostBatchLaw hτ).finiteMean (fun T => mainSampledBadCount f D H T.val) ≤
        K*(batchSize f D H:ℝ)*
          (1/(alpha N*Real.sqrt (L2 N))+(L2 N)^(-24/25:ℝ)/(alpha N/100000)^2) := by
  classical
  obtain ⟨Ke,hKe,hevent⟩ := inherited_sampled_source_entropy_eventually r b hr C B L hC hB hL
  obtain ⟨Kf,hKf,hfailure⟩ := inherited_sampled_normal_bad_eventually r b hr C B hC hB
  let Rr : ℝ := (r*(r-1):ℕ)
  refine ⟨Ke+Rr*Kf, by dsimp [Rr]; positivity, ?_⟩
  filter_upwards [hevent,hfailure,inherited_sampling_parameters_eventually r b hr C hC.le,
    eventual_range] with N hent hfail hsam hscale
  intro M ell original offset hadm f D hD j h c ω hh hMj hj hreg hbudget
  dsimp only
  let H := extensionState ω.1 ω.2 j
  have hs := hsam M ell original offset hadm f D hD j h c L ω hMj hj hreg
  obtain ⟨_,_,_,_,hm,_,ht,_,ht4,_⟩ := hs
  change 0 < (unexposed f D H).card at hm
  change 1 ≤ batchSize f D H at ht
  change 4*batchSize f D H ≤ (unexposed f D H).card at ht4
  have hτ : batchSize f D H ≤ (unexposed f D H).card := by omega
  refine ⟨hτ,?_⟩
  let R := sampleableRoles f D H
  let edge := fun a : Finset (Fin N) × Fin N × Fin N => a.1 ∪ {a.2.1,a.2.2}
  let Bad := fun a : Finset (Fin N) × Fin N × Fin N => alpha N/100 < |frameNormalizedCount f H a-1|
  let P := fun T : SimpleHypergraph (Fin N) => fun a : Finset (Fin N) × Fin N × Fin N =>
    MainCountSurvives f D H T ∧ alpha N/4 < |frameNormalizedCount f (rawRemainder f D H T) a-1|
  let p0 : ℝ := (L2 N)^(-24/25:ℝ)/(alpha N/100000)^2
  have hp0 : 0 ≤ p0 := div_nonneg (Real.rpow_nonneg hscale.2.1.le _) (sq_nonneg _)
  have hR : ∀ a ∈ R, edge a ∈ unexposed f D H := fun _ ha => (mem_filter.mp ha).2
  have hsmall (a : Finset (Fin N) × Fin N × Fin N) (ha : a ∈ R) (hn : ¬ Bad a) :
      (hostBatchLaw (show batchSize f D H-1 ≤ ((unexposed f D H).erase (edge a)).card by
        rw [card_erase_of_mem (hR a ha)]; omega)).event
        (fun T => P (insert (edge a) T.val) a) ≤ Kf*p0 := by
    have hc : f.LegalCandidate a := by simpa only [Frame.candidates, mem_filter, mem_univ, true_and]
      using (mem_filter.mp ha).1
    have hh' := hfail M ell original offset hadm f D hD j h c L ω hh hMj hj hreg hbudget a hc
      (le_of_not_gt hn) (hR a ha) ht hτ
    rw [candidate_batch_conditional_law (hR a ha) ht hτ (fun T => P T a)] at hh'
    convert hh' using 1 <;> dsimp [p0] <;> ring
  have hmean := sampled_role_failure_mean ht hτ R edge hR Bad P (Kf*p0) (by positivity) hsmall
  have hgate : (hostBatchLaw hτ).finiteMean (fun T => mainSampledBadCount f D H T.val) =
      ∑ T, (hostBatchLaw hτ).mass T*((R.filter (fun a => edge a ∈ T.val ∧ P T.val a)).card:ℝ) := by
    unfold FiniteEntropy.Law.finiteMean
    apply sum_congr rfl
    intro T _
    dsimp only
    rw [mainSampledBadCount_eq f D H T.val (mem_powersetCard.mp T.property).1]
  rw [hgate]
  calc
    _ ≤ ((batchSize f D H:ℝ)/(unexposed f D H).card)*
        ((R.filter Bad).card+Kf*p0*R.card) := by
      convert hmean using 1
      apply Finset.sum_congr rfl
      intro T _
      congr 3
      ext a
      simp only [mem_filter]
    _ ≤ _ := by
      have hsource := hent M ell original offset hadm f D hD j h c ω hh hMj hj hreg hbudget
      have hbadcard : ((R.filter Bad).card:ℝ) ≤ (f.existingExceptional H (alpha N/100)).card := by
        exact_mod_cast card_le_card (sampleable_sourceBad_subset f D H (alpha N/100))
      have hrolecard : (R.card:ℝ) ≤ (unexposed f D H).card*Rr := by
        change ((f.restrictedExistingCandidates (unexposed f D H)).card:ℝ) ≤
          (unexposed f D H).card*((r*(r-1):ℕ):ℝ)
        exact_mod_cast f.restrictedExistingCandidates_card_le (by omega) H (unexposed f D H)
          (batch_subset_raw f D H _ (Subset.refl _))
      have hrole : ((batchSize f D H:ℝ)/(unexposed f D H).card)*(Kf*p0*R.card) ≤
          (batchSize f D H:ℝ)*Rr*Kf*p0 := by
        have hmR : (0:ℝ) < (unexposed f D H).card := Nat.cast_pos.mpr hm
        calc
          _ ≤ ((batchSize f D H:ℝ)/(unexposed f D H).card)*
              (Kf*p0*((unexposed f D H).card*Rr)) := by gcongr
          _ = _ := by field_simp [hmR.ne'] <;> ring
      have hsource' : ((batchSize f D H:ℝ)/(unexposed f D H).card)*(R.filter Bad).card ≤
          Ke*(batchSize f D H:ℝ)/(alpha N*Real.sqrt (L2 N)) :=
        (mul_le_mul_of_nonneg_left hbadcard (by positivity)).trans hsource
      have hsum := add_le_add hsource' hrole
      have hden : 0 ≤ 1/(alpha N*Real.sqrt (L2 N)) :=
        div_nonneg zero_le_one (mul_nonneg hscale.2.2.2.1.le (Real.sqrt_nonneg _))
      have hτR : (0:ℝ) ≤ batchSize f D H := Nat.cast_nonneg _
      have hcross1 := mul_nonneg (mul_nonneg hKe.le hτR) hp0
      have hcross2 := mul_nonneg (mul_nonneg (mul_nonneg (show 0 ≤ Rr by dsimp [Rr]; positivity) hKf.le) hτR) hden
      dsimp only [p0,H] at hsum hcross1 hcross2 ⊢
      convert (hsum.trans (le_add_of_nonneg_right (add_nonneg hcross1 hcross2))) using 1 <;> ring

end LooseHamilton.CandidateBalance
