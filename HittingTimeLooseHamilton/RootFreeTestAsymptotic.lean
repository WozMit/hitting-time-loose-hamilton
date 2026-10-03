module

public import HittingTimeLooseHamilton.RootFreeTestProbability
public import HittingTimeLooseHamilton.CommonEventScales
public import HittingTimeLooseHamilton.RootLinkCoordinates

public section

/-! Uniform root-free adaptive tests at the manuscript's density scale. -/
noncomputable section
namespace LooseHamilton
open Filter Finset FrameScales

/-- The actual root-test failure event. Its test is a function of root-free
observations; root regularity restrictions are event intersections. -/
@[expose] def RootFreeTestFailure {V : Type*} [Fintype V] [DecidableEq V]
    (r M : ℕ) (ell : V → ℕ) (m : ℕ) (y : V) (R : SimpleHypergraph V)
    (Γ : SimpleHypergraph V × SimpleHypergraph V → SimpleHypergraph V)
    (N : ℕ) (c : ℝ) (ω : TerminalState V r M ell × MissingOrder V r M) : Prop :=
  R ⊆ (rootSamplingPair r M ell m ω).2 ∧
  (∑ v, rootAdjustedDeficit y ell (rootFreePairObservation r M ell m y ω).1 v) ≤ 1 ∧
  c*L1 N ≤ ((m-(rootFreePairObservation r M ell m y ω).2.card:ℕ):ℝ) ∧
  rootLinkDensity r y (Γ (rootFreePairObservation r M ell m y ω)) ≤ rho N ∧
  RootLinkBad (Γ (rootFreePairObservation r M ell m y ω))
    (m-(rootFreePairObservation r M ell m y ω).2.card) (rootSamplingPair r M ell m ω)

/-- One size threshold works for every vertex universe, time, root,
prescription and root-free test. Only the fixed parameters `r,c,h` affect it. -/
theorem root_free_test_probability_eventually {r : ℕ} (hr : 3 ≤ r)
    {c : ℝ} (hc : 0 < c) (h : ℕ) :
    ∀ᶠ N in atTop, ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V=N →
      ∀ (M : ℕ) (ell : V → ℕ), [Nonempty (TerminalState V r M ell)] →
      ∀ (m : ℕ), M ≤ m → m ≤ (completeEdges V r).card →
      ∀ (y : V) (R : SimpleHypergraph V)
        (Γ : SimpleHypergraph V × SimpleHypergraph V → SimpleHypergraph V),
      R ⊆ rootEdgeUniverse r y → R.card ≤ h →
      (∀ data, Γ data ⊆ rootEdgeUniverse r y) →
      (extensionLaw r M ell).event (RootFreeTestFailure r M ell m y R Γ N c) ≤
        Real.exp (-(c/6400)*L1 N*Real.log (L3 N)) := by
  filter_upwards [eventually_rootLink_sample_large hc h,
    eventually_rootLink_universe_large (r-1) h 1 (by omega),
    eventually_ge_atTop r, eventually_rho_small, eventually_root_power_bound hc]
    with N hsample huniv hnr hrho hpower
  intro V _ _ hVN M ell _ m hMm hm y R Γ hR hRh hΓ
  have hqceil : c*L1 N ≤ (Nat.ceil (c*L1 N):ℝ) := Nat.le_ceil _
  have hqmin : 12*(h+1) ≤ Nat.ceil (c*L1 N) := hsample _ hqceil
  have hU : 0 < (rootEdgeUniverse r y).card := by
    rw [rootEdgeUniverse_card r (by omega) y,hVN]
    exact Nat.choose_pos (by omega)
  have hh : 2*h ≤ (rootEdgeUniverse r y).card := by
    rw [rootEdgeUniverse_card r (by omega) y,hVN]
    exact huniv
  have hb := root_free_adaptive_test_probability r M ell m hMm hm y R Γ h
    (Nat.ceil (c*L1 N)) (rho N) hR hRh hU hh hqmin hrho.1.le hrho.2 hΓ
  apply le_trans _ (hb.trans (hpower _ hqceil))
  apply (extensionLaw r M ell).event_mono
  intro ω hω
  exact ⟨hω.1,hω.2.1,Nat.ceil_le.mpr hω.2.2.1,hω.2.2.2⟩
end LooseHamilton
