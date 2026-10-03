module

public import HittingTimeLooseHamilton.FrameMainConcentration
public import HittingTimeLooseHamilton.FrameConditionalCompletionRemainder

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset Filter AuxiliaryFrame FrameScales FrameSurvival

/-- Feasibility and actual main-family concentration on the retained-boundary
raw remainder, packaged without an additional batch-feasibility premise. -/
@[expose] def MainConcentrationBound {N r : ℕ} {original : Finset (Finset (Fin N))}
    (f : Frame r original) (D : Finset (Fin N)) (H : SimpleHypergraph (Fin N))
    (K : ℝ) : Prop :=
  ∃ htpos : 1≤batchSize f D H, ∃ hτ : batchSize f D H≤(unexposed f D H).card,
    (hostBatchLaw hτ).event (fun T =>
      (alpha N/100000)*(CandidateLogSurvival.zeta (unexposed f D H).card
        f.k (batchSize f D H)*f.cycleCount H) <
      |(f.cycleCount (rawRemainder f D H T.val):ℝ)-
        CandidateLogSurvival.zeta (unexposed f D H).card f.k (batchSize f D H)*
          f.cycleCount H|) ≤ K*(L2 N)^(-24/25:ℝ)/(alpha N/100000)^2

theorem inherited_main_remainder_concentration_eventually (r b : ℕ) (hr : 3≤r)
    (C B : ℝ) (hC : 0<C) (hB : 0≤B) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (M : ℕ) (ell : Fin N→ℕ) (original : Finset (Finset (Fin N))) (offset : ℝ),
        CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card≤b →
      ∀ (j h : ℕ) (c L : ℝ) (ω : Outcome (Fin N) r M ell),
        4*r≤h → M≤j → j≤(completeEdges (Fin N) r).card →
        InheritedRegularity original j h c C L ω →
        f.entropyBudget (extensionState ω.1 ω.2 j) B →
        MainConcentrationBound f D (extensionState ω.1 ω.2 j) K := by
  obtain ⟨K,hK,hconc⟩ := inherited_main_concentration_eventually r b hr C B hC hB
  refine ⟨K,hK,?_⟩
  filter_upwards [hconc,inherited_sampling_parameters_eventually r b hr C hC.le]
    with N hc hp
  intro M ell original offset hadm f D hD j h c L ω hh hMj hj hreg hbudget
  let H := extensionState ω.1 ω.2 j
  have hs := hp M ell original offset hadm f D hD j h c L ω hMj hj hreg
  obtain ⟨_,_,_,_,_,_,htpos,_,ht4,_⟩ := hs
  have hτ : batchSize f D H≤(unexposed f D H).card := by dsimp [H]; omega
  refine ⟨htpos,hτ,?_⟩
  have he (T : HostBatch (unexposed f D H) (batchSize f D H)) :
      f.cycleCount (rawRemainder f D H T.val)=f.cycleCount (H\T.val) :=
    congrArg Finset.card (rawRemainder_cycleFamily f D H T.val
      (mem_powersetCard.mp T.property).1)
  have bound := hc M ell original offset hadm f D hD j h c L ω hh hMj hj hreg hbudget hτ
  convert bound using 1
  congr 1
  ext T
  rw [he]
end LooseHamilton.CandidateBalance
