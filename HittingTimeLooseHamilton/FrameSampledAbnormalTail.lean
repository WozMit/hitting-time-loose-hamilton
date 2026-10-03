module

public import HittingTimeLooseHamilton.FrameSampledAbnormalMean
public import HittingTimeLooseHamilton.FrameSampledAbnormalMarkov
public import HittingTimeLooseHamilton.FrameMainRemainderConcentration

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival Filter FrameScales

lemma event_le_main_complement_add {Ω : Type*} [Fintype Ω]
    (p : FiniteEntropy.Law Ω) (Main Bad : Ω → Prop) :
    p.event Bad ≤ p.event (fun x => ¬ Main x)+p.event (fun x => Main x ∧ Bad x) := by
  classical
  unfold FiniteEntropy.Law.event
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro x _
  by_cases hm : Main x <;> by_cases hb : Bad x <;> simp [hm,hb,p.nonneg x]

/-- Markov after gating by the common main event, followed by a single
unconditional main-failure bound. Both sampled role and sampled edge counts
obey the resulting tail estimate. -/
theorem inherited_sampled_bad_tail_eventually (r b : ℕ) (hr : 3 ≤ r)
    (C B L : ℝ) (hC : 0 < C) (hB : 0 ≤ B) (hL : 0 < L) :
    ∃ Km Kg : ℝ, 0 < Km ∧ 0 < Kg ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (M : ℕ) (ell : Fin N → ℕ) (original : Finset (Finset (Fin N)))
        (offset : ℝ), CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card ≤ b →
      ∀ (j h : ℕ) (c : ℝ) (ω : Outcome (Fin N) r M ell),
        4*r ≤ h → M ≤ j → j ≤ (completeEdges (Fin N) r).card →
        InheritedRegularity original j h c C L ω →
        f.entropyBudget (extensionState ω.1 ω.2 j) B →
      let H := extensionState ω.1 ω.2 j
      let p0 := (L2 N)^(-24/25:ℝ)/(alpha N/100000)^2
      let q0 := (1/(alpha N*Real.sqrt (L2 N))+p0)/(alpha N)^2
      ∃ hτ : batchSize f D H ≤ (unexposed f D H).card,
      (hostBatchLaw hτ).event (fun T => MainCountSurvives f D H T.val ∧
        (alpha N)^2*batchSize f D H < ((sampledBadRoles f D H T.val).card:ℝ)) ≤ Kg*q0 ∧
      (hostBatchLaw hτ).event (fun T =>
        (alpha N)^2*batchSize f D H < ((sampledBadRoles f D H T.val).card:ℝ)) ≤ Km*p0+Kg*q0 ∧
      (hostBatchLaw hτ).event (fun T =>
        (alpha N)^2*batchSize f D H < ((sampledBadEdges f D H T.val).card:ℝ)) ≤ Km*p0+Kg*q0 := by
  obtain ⟨Kg,hKg,hmean⟩ := inherited_sampled_bad_mean_eventually r b hr C B L hC hB hL
  obtain ⟨Km,hKm,hmain⟩ := inherited_main_remainder_concentration_eventually r b hr C B hC hB
  refine ⟨Km,Kg,hKm,hKg,?_⟩
  filter_upwards [hmean,hmain,eventual_range] with N hmeanN hmainN hR
  intro M ell original offset hadm f D hD j h c ω hh hMj hj hreg hbudget
  dsimp only
  let H := extensionState ω.1 ω.2 j
  obtain ⟨hτ,hm⟩ := hmeanN M ell original offset hadm f D hD j h c ω hh hMj hj hreg hbudget
  obtain ⟨htpos,_,hmainfail⟩ := hmainN M ell original offset hadm f D hD j h c L ω hh hMj hj hreg hbudget
  change 1 ≤ batchSize f D H at htpos
  have hgated := sampledBadRoles_tail_of_mean f D H (τ := batchSize f D H) hτ (by omega) hR.2.2.2.1
    (Kg*(1/(alpha N*Real.sqrt (L2 N))+(L2 N)^(-24/25:ℝ)/(alpha N/100000)^2))
    (by convert hm using 1 <;> ring)
  have hmainfail' : (hostBatchLaw hτ).event (fun T => ¬ MainCountSurvives f D H T.val) ≤
      Km*((L2 N)^(-24/25:ℝ)/(alpha N/100000)^2) := by
    simpa only [MainCountSurvives,not_le,mul_div_assoc] using hmainfail
  have hgated' : (hostBatchLaw hτ).event (fun T => MainCountSurvives f D H T.val ∧
      (alpha N)^2*batchSize f D H < ((sampledBadRoles f D H T.val).card:ℝ)) ≤
      Kg*((1/(alpha N*Real.sqrt (L2 N))+(L2 N)^(-24/25:ℝ)/(alpha N/100000)^2)/(alpha N)^2) := by
    convert hgated using 1 <;> ring
  have hall := (event_le_main_complement_add (hostBatchLaw hτ)
    (fun T => MainCountSurvives f D H T.val)
    (fun T => (alpha N)^2*batchSize f D H < ((sampledBadRoles f D H T.val).card:ℝ))).trans
    (add_le_add hmainfail' hgated')
  refine ⟨hτ,hgated',hall,?_⟩
  apply le_trans _ hall
  apply FiniteEntropy.Law.event_mono
  intro T hT
  exact hT.trans_le (Nat.cast_le.mpr (sampledBadEdges_card_le f D H T.val))

end LooseHamilton.CandidateBalance
