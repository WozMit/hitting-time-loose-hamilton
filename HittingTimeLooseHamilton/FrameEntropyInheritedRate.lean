module

public import HittingTimeLooseHamilton.FrameEntropyCountUniform
public import HittingTimeLooseHamilton.FrameEntropyInheritedRegularity
public import HittingTimeLooseHamilton.FrameRestrictedParametersUniform
public import HittingTimeLooseHamilton.PartitionWindowEnlargement
public import HittingTimeLooseHamilton.FrameEntropyWindowScales

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Filter Finset AuxiliaryFrame

/-- Item 30.7 for the actual extension-process host. The constants and size
threshold precede the frame, time, outcome and positive tolerance. All inputs
are the original admissibility, inherited regularity and imposed frame budget. -/
theorem inherited_existingExceptional_eventually (r : ℕ) (hr : 3≤r)
    (C B L : ℝ) (hC : 0<C) (hB : 0≤B) (hL : 0<L) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (M : ℕ) (ell : Fin N → ℕ) (original : Finset (Finset (Fin N)))
        (offset : ℝ), CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (j h : ℕ) (c : ℝ) (ω : Outcome (Fin N) r M ell),
        4*r ≤ h → M≤j → j≤(completeEdges (Fin N) r).card →
        InheritedRegularity original j h c C L ω →
        f.entropyBudget (extensionState ω.1 ω.2 j) B →
        ∀ t : ℝ, 0<t →
          ((f.existingExceptional (extensionState ω.1 ω.2 j) t).card:ℝ) ≤
            K*(f.m (extensionState ω.1 ω.2 j):ℝ)/
              (t*Real.sqrt (Real.log (Real.log (N:ℝ)))) := by
  obtain ⟨K,hK,hbound⟩ := Frame.existingExceptional_uniform_rate r hr (2*C) B
    (by positivity) hB
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp (eventually_partition_window_enlargement L 6 hL)
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,inherited_frame_density_eventually r 0 C hC.le,
    eventually_ge_atTop (n₀+4*r)] with N hbound hd hN
  intro M ell original offset hadm f j h c ω hh hMj hj hreg hbudget t ht
  let H := extensionState ω.1 ω.2 j
  have hden := hd M ell original offset hadm f ∅ (by simp) j h c L ω hMj hj hreg
  have hn : n₀≤f.n := by
    have ha := f.n_add_deleted
    have hb := f.val.deleted_card_le
    simp only [Fintype.card_fin] at ha
    omega
  have hwin := hn₀ f.n hn
  have hreg' := (f.entropyInstance_inherited_regular j h c C L ω hh hreg hbudget.1).enlarge_window
    hr hC.le (by
      change 1 ≤ L*(Fintype.card (Fin f.n):ℝ)^(1/10:ℝ)
      rw [Fintype.card_fin]
      exact hwin.1) (by
      change 6*(Fintype.card (Fin f.n):ℝ)^(1/10:ℝ)+1 ≤
        (Fintype.card (Fin f.n):ℝ)*Real.log (Fintype.card (Fin f.n):ℝ)^(-1/8:ℝ)
      rw [Fintype.card_fin]
      exact hwin.2)
  let d : Frame.EntropyFrameInput r (2*C) B N :=
    { original := original
      frame := f
      host := H
      budget := hbudget
      markers_small := by simpa using hadm.markers_small
      density := hden.2.2
      regular := hreg' }
  exact hbound d t ht
end LooseHamilton.CandidateBalance
