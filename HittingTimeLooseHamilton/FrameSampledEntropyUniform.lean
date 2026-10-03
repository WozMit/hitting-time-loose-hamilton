module

public import HittingTimeLooseHamilton.FrameSampledEntropyParameters
public import HittingTimeLooseHamilton.FrameEntropyInheritedRate

public section

/-! Source entropy weighted by the exact sampling inclusion probability.
All source role directions and the original-size logarithmic scale are retained. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame Filter FrameScales

/-- The expected contribution of source-exceptional roles is bounded without
conditioning the main family or paying a reciprocal event probability.
The count includes all existing raw roles, so it also bounds those in J0. -/
theorem inherited_sampled_source_entropy_eventually (r b : ℕ) (hr : 3≤r)
    (C B L : ℝ) (hC : 0<C) (hB : 0≤B) (hL : 0<L) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (M : ℕ) (ell : Fin N→ℕ) (original : Finset (Finset (Fin N)))
        (offset : ℝ), CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card≤b →
      ∀ (j h : ℕ) (c : ℝ) (ω : Outcome (Fin N) r M ell),
        4*r≤h → M≤j → j≤(completeEdges (Fin N) r).card →
        InheritedRegularity original j h c C L ω →
        f.entropyBudget (extensionState ω.1 ω.2 j) B →
      let H := extensionState ω.1 ω.2 j
      ((batchSize f D H:ℝ)/(unexposed f D H).card)*
        ((f.existingExceptional H (alpha N/100)).card:ℝ) ≤
      K*(batchSize f D H:ℝ)/(alpha N*Real.sqrt (L2 N)) := by
  obtain ⟨K,hK,he⟩ := inherited_existingExceptional_eventually r hr C B L hC hB hL
  refine ⟨200*K,by positivity,?_⟩
  filter_upwards [he,inherited_raw_le_twice_unexposed_eventually r b hr C hC.le,
    eventual_range] with N hent hraw hR
  intro M ell original offset hadm f D hD j h c ω hh hMj hj hreg hb H
  have hr' := hraw M ell original offset hadm f D hD j h c L ω hMj hj hreg
  have hc := hent M ell original offset hadm f j h c ω hh hMj hj hreg hb
    (alpha N/100) (div_pos hR.2.2.2.1 (by norm_num))
  apply source_entropy_sampling_weight (f.m H) (unexposed f D H).card
    (batchSize f D H) (f.existingExceptional H (alpha N/100)).card K (alpha N)
    (Real.sqrt (L2 N)) (Nat.cast_pos.mpr hr'.1) (Nat.cast_nonneg _) hK.le
    hR.2.2.2.1 (Real.sqrt_pos.mpr hR.2.1) hr'.2
  exact hc

end LooseHamilton.CandidateBalance
