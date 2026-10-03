module

public import HittingTimeLooseHamilton.BootstrapCompletionMaximum
public import HittingTimeLooseHamilton.BootstrapActualBudgets
public import HittingTimeLooseHamilton.BootstrapPrivateAdmissibleParameters

public section

/-! The original frame's balance follows from the benchmark event, with no
entropy or candidate-balance premise. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace LooseHamilton.BootstrapOriginalBalance
open Finset Filter AuxiliaryFrame BootstrapCatalogue

theorem eventually_original_balance (r : ℕ) (hr : 3 ≤ r) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (ell : Fin N → ℕ)
      (M : Finset (Finset (Fin N))) (offset : ℝ),
      CoreAdmissible r m ell M offset →
      ∀ (h hR : ℕ) (c C L cRoot : ℝ)
      (tests : RootFreeTestIndexing.RootTestIndex r M → RegisteredRootTest (Fin N) r hR)
      (ω : CandidateBalance.Outcome (Fin N) r m ell),
      RootFreeCommonEvent tests h c C L 2 cRoot ω →
      ∀ j : ℕ, m ≤ j → j ≤ (completeEdges (Fin N) r).card →
      let H := extensionState ω.1 ω.2 j
      let X := cycleCount r M H (originalPorts M)
      0 < X → logarithmicBaseline r (ordinaryEdgeCount r M) j M -
        (N:ℝ)/Real.sqrt (Real.log N) ≤ Real.log (X:ℝ) →
      ∀ F : Frame r M, F.val.deleted = ∅ → F.markers = M → F.val.relative = none →
      ¬F.candidateBad H (FrameScales.alpha N) := by
  have ha : 0 < 1/(2*(r:ℝ)) := by positivity
  filter_upwards [BootstrapActualBudgets.eventually_all_frames r hr _ ha,
    eventually_terminal_mean_lower, eventually_ge_atTop 1] with N hbudget hterminal hN
  intro m ell M offset hadm h hR c C L cRoot tests ω hω j hj hK H X hX hAX F hd hm hrel
  have hcard : H.card = j := extensionState_card ω.1 ω.2 j hj hK
  have hlower := BootstrapPrivateAdmissibleParameters.later_time_lower (V:=Fin N) hr
    (by simpa using (show 0<N by omega)) hj (by simpa using hterminal r m ell M offset hadm)
  have hupper : H.card ≤ N.choose r := by
    simpa only [completeEdges_card,Fintype.card_fin] using card_le_card
      (extensionState_subset ω.1 ω.2 j)
  have hcount : F.cycleCount H = X := F.original_cycleCount hr hrel hd hm H
  have hcut : (X:ℝ)*(N:ℝ)^(-(100*(r:ℝ))) ≤ F.cycleCount H := by
    rw [hcount]
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by have h : (0:ℝ) ≤ r := Nat.cast_nonneg r; linarith))
      (Nat.cast_nonneg X)).trans_eq (mul_one _)
  have hb := hbudget (ordinaryEdgeCount r M) M (by simpa using hadm.vertex_bookkeeping)
    hadm.marker_matching hadm.markers_nonempty (by simpa using hadm.markers_small) H
    (by simpa only [Fintype.card_fin,hcard] using hlower) hupper X hX
    (by simpa only [hcard] using hAX) F hcut
  simpa only [Frame.candidateBadAtScale,Fintype.card_fin] using hω.candidates F j hj hK hb

end LooseHamilton.BootstrapOriginalBalance
