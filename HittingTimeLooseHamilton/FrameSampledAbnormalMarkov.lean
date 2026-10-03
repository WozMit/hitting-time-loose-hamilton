module

public import HittingTimeLooseHamilton.FrameSampledAbnormalDefinitions
public import HittingTimeLooseHamilton.FiniteMomentBounds

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival
variable {N r : ℕ} {original : Finset (Finset (Fin N))}

/-- Markov is applied after multiplying by the single unconditional
main-survival indicator. No conditional main-survival estimate is used. -/
theorem sampledBadRoles_markov (f : Frame r original) (D : Finset (Fin N))
    (H : SimpleHypergraph (Fin N)) {τ : ℕ}
    (hτ : τ≤(unexposed f D H).card) (ht : 0<τ) (ha : 0<FrameScales.alpha N) :
    (hostBatchLaw hτ).event (fun T => MainCountSurvives f D H T.val ∧
      (FrameScales.alpha N)^2*τ < ((sampledBadRoles f D H T.val).card:ℝ)) ≤
    (hostBatchLaw hτ).finiteMean (fun T => mainSampledBadCount f D H T.val) /
      ((FrameScales.alpha N)^2*τ) := by
  have hpos : 0<(FrameScales.alpha N)^2*(τ:ℝ) :=
    mul_pos (sq_pos_of_pos ha) (Nat.cast_pos.mpr ht)
  apply le_trans _ ((hostBatchLaw hτ).finite_markov
    (fun T => mainSampledBadCount_nonneg f D H T.val) hpos)
  apply FiniteEntropy.Law.event_mono
  intro T hT
  classical
  simpa only [mainSampledBadCount,if_pos hT.1] using hT.2.le

/-- Cancelling the batch size in the gated Markov bound. -/
theorem sampledBadRoles_tail_of_mean (f : Frame r original) (D : Finset (Fin N))
    (H : SimpleHypergraph (Fin N)) {τ : ℕ}
    (hτ : τ≤(unexposed f D H).card) (ht : 0<τ) (ha : 0<FrameScales.alpha N)
    (R : ℝ) (hmean : (hostBatchLaw hτ).finiteMean
      (fun T => mainSampledBadCount f D H T.val) ≤ (τ:ℝ)*R) :
    (hostBatchLaw hτ).event (fun T => MainCountSurvives f D H T.val ∧
      (FrameScales.alpha N)^2*τ < ((sampledBadRoles f D H T.val).card:ℝ)) ≤
      R/(FrameScales.alpha N)^2 := by
  apply (sampledBadRoles_markov f D H hτ ht ha).trans
  have hh := div_le_div_of_nonneg_right hmean
    (mul_nonneg (sq_nonneg (FrameScales.alpha N)) (Nat.cast_nonneg τ))
  have ht' : (τ:ℝ)≠0 := by exact_mod_cast ht.ne'
  convert hh using 1
  field_simp
  <;> ring

/-- A sampled edge is counted once even if several directed roles witness
its abnormality. -/
@[expose] def sampledBadEdges (f : Frame r original) (D : Finset (Fin N))
    (H T : SimpleHypergraph (Fin N)) : SimpleHypergraph (Fin N) :=
  (sampledBadRoles f D H T).image (fun c => c.1∪{c.2.1,c.2.2})

lemma sampledBadEdges_card_le (f : Frame r original) (D : Finset (Fin N))
    (H T : SimpleHypergraph (Fin N)) :
    (sampledBadEdges f D H T).card≤(sampledBadRoles f D H T).card := card_image_le

lemma sampledBadEdges_subset (f : Frame r original) (D : Finset (Fin N))
    (H T : SimpleHypergraph (Fin N)) : sampledBadEdges f D H T⊆T := by
  classical
  intro e he
  obtain ⟨c,hc,rfl⟩ := mem_image.mp he
  exact (mem_filter.mp hc).2.1
/-- The same Markov estimate controls sampled edges with an abnormal role. -/
theorem sampledBadEdges_tail_of_mean (f : Frame r original) (D : Finset (Fin N))
    (H : SimpleHypergraph (Fin N)) {τ : ℕ}
    (hτ : τ≤(unexposed f D H).card) (ht : 0<τ) (ha : 0<FrameScales.alpha N)
    (R : ℝ) (hmean : (hostBatchLaw hτ).finiteMean
      (fun T => mainSampledBadCount f D H T.val) ≤ (τ:ℝ)*R) :
    (hostBatchLaw hτ).event (fun T => MainCountSurvives f D H T.val ∧
      (FrameScales.alpha N)^2*τ < ((sampledBadEdges f D H T.val).card:ℝ)) ≤
      R/(FrameScales.alpha N)^2 := by
  apply le_trans _ (sampledBadRoles_tail_of_mean f D H hτ ht ha R hmean)
  apply FiniteEntropy.Law.event_mono
  intro T hT
  refine ⟨hT.1,hT.2.trans_le ?_⟩
  exact_mod_cast sampledBadEdges_card_le f D H T.val
end LooseHamilton.CandidateBalance
