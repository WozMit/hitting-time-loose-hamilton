module

public import HittingTimeLooseHamilton.FrameRestrictedParametersUniform
public import HittingTimeLooseHamilton.FrameRestrictedKParameters
public import HittingTimeLooseHamilton.FrameBatchParameters
public import HittingTimeLooseHamilton.FrameCandidateCountsUniform

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame Filter

/-- All sampling estimates hold at a common threshold, before the frame, time,
boundary and exposure outcome are chosen. -/
theorem inherited_sampling_parameters_eventually (r b : ℕ) (hr : 3 ≤ r)
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (ell : Fin N → ℕ)
      (original : Finset (Finset (Fin N))) (offset : ℝ),
      CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card ≤ b →
      ∀ (j h : ℕ) (c L : ℝ) (ω : Outcome (Fin N) r M ell),
      M ≤ j → j ≤ (completeEdges (Fin N) r).card →
      InheritedRegularity original j h c C L ω →
      let H := extensionState ω.1 ω.2 j
      Real.log N/2 ≤ f.mu H ∧
      (N:ℝ) ≤ (8*((r:ℝ)-1))*f.k ∧ (f.k:ℝ) ≤ N ∧
      (0 ≤ 1-(unexposed f D H).card/(f.m H:ℝ) ∧
       1-(unexposed f D H).card/(f.m H:ℝ) ≤ 2*(b:ℝ)*C*r/N) ∧
      0 < (unexposed f D H).card ∧ 1 ≤ f.k ∧ 1 ≤ batchSize f D H ∧
      4*f.k ≤ (unexposed f D H).card ∧
      4*batchSize f D H ≤ (unexposed f D H).card ∧
      FrameScales.nu N*FrameScales.L1 N/(16*(r:ℝ)) ≤ (batchSize f D H:ℝ) ∧
      (f.n.choose r:ℝ)*(r*(r-1):ℕ)/2 ≤ f.candidates.card ∧
      ((f.boundaryCandidates D).card:ℝ)/f.candidates.card ≤ 4*(b:ℝ)*r/N := by
  obtain ⟨N₀,hcount⟩ := Frame.uniform_candidate_counts r (by omega)
  filter_upwards [inherited_frame_density_eventually r b C hC,
    inherited_boundary_ratio_eventually r b C hC,
    eventually_frame_batch_parameters r hr,
    eventually_ge_atTop (16*r), eventually_ge_atTop N₀,
    FrameScales.L1_tendsto.eventually (eventually_ge_atTop (0:ℝ))]
    with N hd hl hb hN hN₀ hlog
  intro M ell original offset hadm f D hD j h c L ω hMj hj hreg
  let H := extensionState ω.1 ω.2 j
  have hd' := hd M ell original offset hadm f D hD j h c L ω hMj hj hreg
  have hl' := hl M ell original offset hadm f D hD j h c L ω hMj hj hreg
  have hk := frame_k_comparison_unconditional f hr (by simpa using hN)
  simp only [Fintype.card_fin] at hk
  have hrpos : 0 < (r:ℝ) := by exact_mod_cast (show 0<r by omega)
  have hdweak : (N:ℝ)*FrameScales.L1 N/(8*(r:ℝ)) ≤ (unexposed f D H).card := by
    apply le_trans _ hd'.2.1
    change (N:ℝ)*Real.log N/(8*(r:ℝ)) ≤ (N:ℝ)*Real.log N/(2*(r:ℝ))
    apply div_le_div_of_nonneg_left (by change 0 ≤ (N:ℝ)*FrameScales.L1 N; positivity)
      (by positivity) (by nlinarith)
  have hb' := hb (unexposed f D H).card f.k hk.1 hk.2.1 hdweak
  have hc := hcount (Fin N) original (by simpa using hN₀)
    hadm.marker_matching (by simpa using hadm.markers_small) f
  refine ⟨hd'.2.2,hk.1,hk.2.1,hl',hb'.1,hb'.2.1,?_,hb'.2.2.2.1,?_,?_,hc.1,?_⟩
  · simpa only [batchSize, FrameSurvival.batchSize, Fintype.card_fin] using hb'.2.2.1
  · simpa only [batchSize, FrameSurvival.batchSize, Fintype.card_fin] using hb'.2.2.2.2.1
  · simpa only [batchSize, FrameSurvival.batchSize, Fintype.card_fin] using hb'.2.2.2.2.2
  · apply (hc.2 D).trans
    simp only [Fintype.card_fin]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hD)
        (by norm_num : (0:ℝ)≤4)) (Nat.cast_nonneg r)) (Nat.cast_nonneg N)
end LooseHamilton.CandidateBalance
