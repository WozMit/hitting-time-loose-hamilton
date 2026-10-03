module

public import HittingTimeLooseHamilton.PartitionWindowEnlargement
public import HittingTimeLooseHamilton.FrameEntropyWindowScales
public import HittingTimeLooseHamilton.FrameEntropyInheritedRegularity

public section

noncomputable section
namespace LooseHamilton
open Finset Filter AuxiliaryFrame

/-- A single original-size threshold enlarges all actual frame partition windows
from any fixed positive L to six, the constant accommodating all frame markers. -/
theorem eventually_frame_window_six (r : ℕ) (hr : 3 ≤ r) (C L : ℝ)
    (hC : 0 ≤ C) (hL : 0 < L) :
    ∀ᶠ N : ℕ in atTop, ∀ {original : Finset (Finset (Fin N))}
      (F : Frame r original) (H : SimpleHypergraph (Fin N))
      (hcycles : (F.cycleFamily H).Nonempty),
      PathGraphUpperRegular r C L (F.entropyInstance H hcycles).host →
      PathGraphUpperRegular r (2*C) 6 (F.entropyInstance H hcycles).host := by
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp (eventually_partition_window_enlargement L 6 hL)
  filter_upwards [eventually_ge_atTop (n₀+4*r)] with N hN
  intro original F H hcycles hreg
  have hn := F.n_lower
  simp only [Fintype.card_fin] at hn
  have hs := hn₀ F.n (by omega)
  apply hreg.enlarge_window hr hC
  · change 1 ≤ L*(Fintype.card (Fin F.n):ℝ)^(1/10:ℝ)
    rw [Fintype.card_fin]
    exact hs.1
  · change 6*(Fintype.card (Fin F.n):ℝ)^(1/10:ℝ)+1 ≤
      (Fintype.card (Fin F.n):ℝ)*Real.log (Fintype.card (Fin F.n):ℝ)^(-1/8:ℝ)
    rw [Fintype.card_fin]
    exact hs.2

/-- Applied directly to the inherited event, without imposing L ≥ 6. -/
theorem eventually_inherited_frame_window_six (r : ℕ) (hr : 3 ≤ r) (C L : ℝ)
    (hC : 0 ≤ C) (hL : 0 < L) :
    ∀ᶠ N : ℕ in atTop, ∀ {M : ℕ} {ell : Fin N → ℕ}
      {original : Finset (Finset (Fin N))} (F : Frame r original)
      (j h : ℕ) (c : ℝ) (ω : CandidateBalance.Outcome (Fin N) r M ell),
      4*r ≤ h → CandidateBalance.InheritedRegularity original j h c C L ω →
      ∀ hcycles : (F.cycleFamily (extensionState ω.1 ω.2 j)).Nonempty,
      PathGraphUpperRegular r (2*C) 6
        (F.entropyInstance (extensionState ω.1 ω.2 j) hcycles).host := by
  filter_upwards [eventually_frame_window_six r hr C L hC hL] with N hN
  intro M ell original F j h c ω hh hreg hcycles
  exact hN F _ hcycles (F.entropyInstance_inherited_regular j h c C L ω hh hreg hcycles)

end LooseHamilton
