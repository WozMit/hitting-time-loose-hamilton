module

public import HittingTimeLooseHamilton.SequentialCompletionGates
public import HittingTimeLooseHamilton.SequentialCompletionFailures

public section

/-! Actual failed-label estimates on the single fixed common event. -/
noncomputable section
namespace LooseHamilton.BootstrapSequentialMobility
open Finset Filter BootstrapBases BootstrapCatalogue BootstrapConstants SequentialCompletion

structure Bounds {N r : ℕ} {M : Finset (Finset (Fin N))}
    (hM : IsPairMatching M) (b : Base M) (H : SimpleHypergraph (Fin N))
    (X c : ℝ) : Prop where
  ordinary : ∀ (s : State ↥(active b) (r-2)),
    s.Valid (r:=r) (restrictEdges (active b) (markers hM b)) →
    EndpointSourcePorts (fixedPorts b) (restrictEdges (active b) (markers hM b)) s.first s.second →
    X/(N:ℝ)^(2*r) ≤ (s.weight r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)):ℝ) →
    fixedPorts b = originalPorts (restrictEdges (active b) (markers hM b)) →
    ∀ labels : Finset (Finset ↥(active b) × ↥(active b) × ↥(active b)),
    (∀ l ∈ labels, l.1.card = r-2) →
    ((labels.filter (fun l => (completionCount r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) l.1 {l.2.1,l.2.2}:ℝ) <
      privateFactor r c ^ (r-2) * endpointFactor r c ^ 2 *
        (s.weight r (restrictEdges (active b) (markers hM b))
          (fixedPortHost (inducedHost (active b) H) (fixedPorts b)):ℝ))).card:ℝ) ≤
      (r:ℝ)*exceptionBound r N (fixedPorts b).card*(N:ℝ)^(r-1)
  port : ∀ (s : State ↥(active b) (r-2)),
    s.Valid (r:=r) (restrictEdges (active b) (markers hM b)) →
    EndpointSourcePorts (fixedPorts b) (restrictEdges (active b) (markers hM b)) s.first s.second →
    X/(N:ℝ)^(2*r) ≤ (s.weight r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)):ℝ) →
    ∀ labels : Finset (Finset ↥(active b) × ↥(active b) × ↥(active b)),
    (∀ l ∈ labels, l.1.card = r-2 ∧ l.2.2 = s.second) →
    ((labels.filter (fun l => (completionCount r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) l.1 {l.2.1,l.2.2}:ℝ) <
      privateFactor r c ^ (r-2) * endpointFactor r c *
        (s.weight r (restrictEdges (active b) (markers hM b))
          (fixedPortHost (inducedHost (active b) H) (fixedPorts b)):ℝ))).card:ℝ) ≤
      ((r-1:ℕ):ℝ)*exceptionBound r N (fixedPorts b).card*(N:ℝ)^(r-2)

theorem of_inputs {N r : ℕ} {M : Finset (Finset (Fin N))}
    (hr : 3 ≤ r) (hM : IsPairMatching M) (b : Base M) (H : SimpleHypergraph (Fin N))
    (X c : ℝ) (hc : 0<c) (ha : 0 ≤ FrameScales.alpha N)
    (inputs : BootstrapSequentialInputs.Inputs (r:=r) hM b H X c) :
    Bounds (r:=r) hM b H X c := by
  classical
  have hN : Fintype.card ↥(active b) ≤ N := by
    simpa using (BootstrapEndpointCutParameters.base_card_bounds b).2
  constructor
  · intro s hs hp hlarge hU labels hlabels
    have hV : 0 < Fintype.card ↥(active b) := Fintype.card_pos_iff.mpr ⟨s.first⟩
    apply ordinary_failed_labels hr s _ _ _ c hc labels hlabels
      (exceptionBound r N (fixedPorts b).card) (exceptionBound_nonneg r N _ ha) hV hN
    intro k hk p hpath
    exact step_bad_card_le hr hM b H X c hc inputs ha s hs hp hlarge 2
      (Or.inr rfl) (fun _ => hU) k hk p hpath
  · intro s hs hp hlarge labels hlabels
    have hV : 0 < Fintype.card ↥(active b) := Fintype.card_pos_iff.mpr ⟨s.first⟩
    apply port_failed_labels hr s _ _ _ c hc labels hlabels
      (exceptionBound r N (fixedPorts b).card) (exceptionBound_nonneg r N _ ha) hV hN
    intro k hk p hpath
    exact step_bad_card_le hr hM b H X c hc inputs ha s hs hp hlarge 1
      (Or.inl rfl) (by intro h; omega) k hk p hpath

/-- Uniform sequential mobility for all genuine residual sources. Both exact
products and the failed-label cardinal estimates follow from the common event;
there is no additional per-step mobility or counting hypothesis. -/
theorem eventually_sequential_mobility (r : ℕ) (hr : 3 ≤ r) (c : ℝ) (hc : 0<c) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (ell : Fin N → ℕ)
      (original : Finset (Finset (Fin N))) (offset : ℝ)
      (hadm : CoreAdmissible r m ell original offset),
      ∃ hroom : 2*original.card+2 ≤ Fintype.card (Fin N),
      ∀ (h hR : ℕ) (cPort C L : ℝ)
        (ω : CandidateBalance.Outcome (Fin N) r m ell),
      RootFreeCommonEvent
        (fixedRegistry (h:=hR) hadm.marker_matching hr hroom
          (rootThreshold r) (rootThreshold r) cPort)
        h c C L 2 (rootConstant c) ω →
      ∀ j : ℕ, m ≤ j → j ≤ (completeEdges (Fin N) r).card →
      let H := extensionState ω.1 ω.2 j
      let X := cycleCount r original H (originalPorts original)
      0 < X → logarithmicBaseline r (ordinaryEdgeCount r original) j original -
        (N:ℝ)/Real.sqrt (Real.log N) ≤ Real.log (X:ℝ) →
      ∀ b : Base original, Bounds (r:=r) hadm.marker_matching b H X c := by
  filter_upwards [BootstrapSequentialInputs.eventually_inputs r hr c hc,
    FrameScales.eventual_range] with N hi hscale
  intro m ell original offset hadm
  obtain ⟨hroom,hi⟩ := hi m ell original offset hadm
  refine ⟨hroom, ?_⟩
  intro h hR cPort C L ω hω j hj hK H X hX hAX b
  exact of_inputs hr hadm.marker_matching b H X c hc hscale.2.2.2.1.le
    (hi h hR cPort C L ω hω j hj hK hX hAX b)

end LooseHamilton.BootstrapSequentialMobility
