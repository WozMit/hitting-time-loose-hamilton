module

public import HittingTimeLooseHamilton.BootstrapActualBudgets
public import HittingTimeLooseHamilton.BootstrapEndpointLiftedBadSet
public import HittingTimeLooseHamilton.BootstrapPrivateAdmissibleParameters
public import HittingTimeLooseHamilton.BootstrapSourceCutoffs

public section

/-! Endpoint core candidate balance on the fixed common event. The cut weight
and the actual ambient frame count are identified before the entropy budget is used. -/
noncomputable section
namespace LooseHamilton.BootstrapEndpointCommonEvent
open Finset Filter BootstrapBases BootstrapCatalogue

/-- A retained large source and a retained cut give the ambient core cutoff. -/
theorem core_cutoff_of_source_and_cut {N r X W Z : ℕ} (hN : 0 < N)
    (hsource : (X : ℝ)/(N : ℝ)^(3*r) ≤ W)
    (hcut : (W : ℝ)/(N : ℝ)^(2*r+2) ≤ Z) :
    (X : ℝ)/(N : ℝ)^(5*r+2) ≤ Z :=
  (BootstrapSourceCutoffs.polynomial_cut_lower_bound hN hsource).trans hcut

/-- Every retained cut of a positive ambient source has positive weight. -/
theorem positive_core_of_cutoff {N r X Z : ℕ} (hN : 0 < N) (hX : 0 < X)
    (hcut : (X : ℝ)/(N : ℝ)^(5*r+2) ≤ Z) : 0 < Z := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have hz : (0 : ℝ) < Z := (div_pos hx (pow_pos hn _)).trans_le hcut
  exact_mod_cast hz

/-- Uniform balance for every literal endpoint core with the retained-cut cutoff. -/
theorem eventually_core_candidates (r : ℕ) (hr : 3 ≤ r) (a : ℝ) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, ∀ original : Finset (Finset (Fin N)),
      N = (r-1)*k+original.card → ∀ hM : IsPairMatching original,
      1 ≤ original.card → (original.card : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) →
      ∀ m h hR : ℕ, ∀ ell : Fin N → ℕ, ∀ c C L cRoot : ℝ,
      ∀ tests : RootFreeTestIndexing.RootTestIndex r original → RegisteredRootTest (Fin N) r hR,
      ∀ ω : CandidateBalance.Outcome (Fin N) r m ell,
      RootFreeCommonEvent tests h c C L 2 cRoot ω →
      ∀ j : ℕ, m ≤ j → j ≤ (completeEdges (Fin N) r).card →
      a*N*Real.log N ≤ (extensionState ω.1 ω.2 j).card →
      ∀ X : ℕ, 0 < X → logarithmicBaseline r k (extensionState ω.1 ω.2 j).card original -
        (N : ℝ)/Real.sqrt (Real.log N) ≤ Real.log (X : ℝ) →
      ∀ b : Base original, ∀ F : AuxiliaryFrame.Frame r original,
      ∀ P : Finset ↥(active b), ∀ y z : ↥(active b),
      ∀ l : RootFreeEndpointLabel ↥(active b),
      BootstrapEndpointLiftedBadSet.CoreShape hM b P y z l F →
      (X : ℝ)/(N : ℝ)^(5*r+2) ≤
        rootFreeEndpointX r (restrictEdges (active b) (markers hM b))
          (fixedPortHost (inducedHost (active b) (extensionState ω.1 ω.2 j)) (fixedPorts b))
          P y z l →
      ¬ F.candidateBad (extensionState ω.1 ω.2 j) (FrameScales.alpha N) := by
  filter_upwards [BootstrapActualBudgets.eventually_all_frames r hr a ha,
    eventually_ge_atTop 1] with N hb hN
  intro k original hsize hM hs hsbound m h hR ell c C L cRoot tests ω hω j hj hK hlow
    X hX hAX b F P y z l hshape hcut
  have hH := extensionState_subset ω.1 ω.2 j
  have hcard : (extensionState ω.1 ω.2 j).card ≤ N.choose r := by
    simpa only [completeEdges_card, Fintype.card_fin] using card_le_card hH
  have hbudget := hb k original hsize hM hs hsbound _ hlow hcard X hX hAX F
  have hw := BootstrapSourceCutoffs.generous_cut_lower_bound (by omega : 1 ≤ r)
    hN (Nat.cast_nonneg X) hcut
  rw [← BootstrapEndpointLiftedBadSet.source_count hM b P y z l F hshape _ hH] at hw
  have hh := hω.candidates F j hj hK (hbudget hw)
  simpa only [AuxiliaryFrame.Frame.candidateBadAtScale,Fintype.card_fin] using hh

/-- On admissible cores, the entropy and time gates follow from the ambient
benchmark and retained-cut cutoff; no additional budget assumption is needed. -/
theorem eventually_admissible_core_candidates (r : ℕ) (hr : 3 ≤ r) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (ell : Fin N → ℕ)
      (original : Finset (Finset (Fin N))) (offset : ℝ)
      (hadm : CoreAdmissible r m ell original offset),
      ∀ (h hR : ℕ) (c C L cRoot : ℝ),
      ∀ tests : RootFreeTestIndexing.RootTestIndex r original → RegisteredRootTest (Fin N) r hR,
      ∀ ω : CandidateBalance.Outcome (Fin N) r m ell,
      RootFreeCommonEvent tests h c C L 2 cRoot ω →
      ∀ j : ℕ, m ≤ j → j ≤ (completeEdges (Fin N) r).card →
      let H := extensionState ω.1 ω.2 j
      let X := cycleCount r original H (originalPorts original)
      0 < X → logarithmicBaseline r (ordinaryEdgeCount r original) j original -
        (N : ℝ)/Real.sqrt (Real.log N) ≤ Real.log (X : ℝ) →
      ∀ b : Base original, ∀ F : AuxiliaryFrame.Frame r original,
      ∀ P : Finset ↥(active b), ∀ y z : ↥(active b),
      ∀ l : RootFreeEndpointLabel ↥(active b),
      BootstrapEndpointLiftedBadSet.CoreShape hadm.marker_matching b P y z l F →
      (X : ℝ)/(N : ℝ)^(5*r+2) ≤
        rootFreeEndpointX r (restrictEdges (active b) (markers hadm.marker_matching b))
          (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z l →
      ¬ F.candidateBad H (FrameScales.alpha N) := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have ha : (0 : ℝ) < 1/(2*(r : ℝ)) := by positivity
  filter_upwards [eventually_core_candidates r hr (1/(2*(r : ℝ))) ha,
    eventually_terminal_mean_lower, eventually_gt_atTop (0 : ℕ)] with N hcan hmean hN
  intro m ell original offset hadm h hR c C L cRoot tests ω hω j hj hK H X hX hAX
    b F P y z l hshape hcut
  have hm : Real.log (Fintype.card (Fin N) : ℝ)/2 ≤ meanDegree (V := Fin N) r m := by
    simpa using hmean r m ell original offset hadm
  have hcard := extensionState_card ω.1 ω.2 j hj hK
  have hlow := BootstrapPrivateAdmissibleParameters.later_time_lower hr
    (by simpa using hN : 0 < Fintype.card (Fin N)) hj hm
  exact hcan (ordinaryEdgeCount r original) original
    (by simpa using hadm.vertex_bookkeeping) hadm.marker_matching hadm.markers_nonempty
    (by simpa using hadm.markers_small) m h hR ell c C L cRoot tests ω hω j hj hK
    (by simpa only [hcard,Fintype.card_fin] using hlow) X hX
    (by simpa only [hcard] using hAX) b F P y z l hshape hcut

end LooseHamilton.BootstrapEndpointCommonEvent
