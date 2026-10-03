module

public import HittingTimeLooseHamilton.FrameCoarseMainBudget
public import HittingTimeLooseHamilton.FrameCoarseMainTransport
public import HittingTimeLooseHamilton.FrameEntropyInheritedRegularity
public import HittingTimeLooseHamilton.FrameRestrictedParametersUniform

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Filter

/-- Inputs retain the actual raw host and prescribed-direction family. Only
vertex degree control, rather than full partition regularity, is required. -/
structure CoarseMainInput (r : ℕ) (C B : ℝ) (N : ℕ) where
  original : Finset (Finset (Fin N))
  frame : Frame r original
  host : SimpleHypergraph (Fin N)
  budget : frame.entropyBudget host B
  density : Real.log N/2 ≤ frame.mu host
  degree : ∀v, (vertexDegree (frame.entropyInstance host budget.1).host v:ℝ) ≤ C*frame.mu host

/-- One threshold works simultaneously for all actual main frame families. -/
theorem main_uniformOverlap_eventually (r : ℕ) (hr : 3≤r)
    (C B : ℝ) (hC : 0<C) (hB : 0≤B) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ d : CoarseMainInput r C B N,
        IndexedSurvival.uniformOverlap (d.frame.cycleFamily d.host) id ≤
          K*(N:ℝ)/Real.log (d.frame.mu d.host) := by
  classical
  obtain ⟨K,hK,hseq⟩ := entropyInstance_coarse_overlap r hr C B hC hB
  refine ⟨K,hK,?_⟩
  by_contra hbad
  have hbad' : ∀ i : ℕ, ∃ N : ℕ, i≤N ∧ ∃ d : CoarseMainInput r C B N,
      ¬ IndexedSurvival.uniformOverlap (d.frame.cycleFamily d.host) id ≤
        K*(N:ℝ)/Real.log (d.frame.mu d.host) := by
    simpa only [eventually_atTop,not_exists,not_forall,not_le,Classical.not_imp,
      exists_prop] using hbad
  choose N hN d hfail using hbad'
  have hNt : Tendsto N atTop atTop := tendsto_atTop_mono hN tendsto_id
  have hmu : Tendsto (fun i => (d i).frame.mu (d i).host) atTop atTop := by
    apply tendsto_atTop_mono (fun i => (d i).density)
    exact (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hNt)).atTop_div_const
      (by norm_num : (0:ℝ)<2)
  have hh := hseq N hNt (fun i => (d i).original) (fun i => (d i).frame)
    (fun i => (d i).host) (fun i => (d i).budget) hmu
    (Eventually.of_forall (fun i => (d i).degree))
  obtain ⟨i,hi⟩ := hh.exists
  apply hfail i
  rw [(d i).frame.uniformOverlap_eq_entropyInstance (d i).host (d i).budget.1]
  exact hi
end LooseHamilton.AuxiliaryFrame.Frame
namespace LooseHamilton.CandidateBalance
open Filter AuxiliaryFrame

/-- The actual extension process supplies every hypothesis of the coarse
main-family overlap theorem; no overlap premise is added. -/
theorem inherited_main_overlap_eventually (r : ℕ) (hr : 3≤r)
    (C B : ℝ) (hC : 0<C) (hB : 0≤B) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (M : ℕ) (ell : Fin N → ℕ) (original : Finset (Finset (Fin N)))
        (offset : ℝ), CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (j h : ℕ) (c L : ℝ) (ω : Outcome (Fin N) r M ell),
        4*r≤h → M≤j → j≤(completeEdges (Fin N) r).card →
        InheritedRegularity original j h c C L ω →
        f.entropyBudget (extensionState ω.1 ω.2 j) B →
        IndexedSurvival.uniformOverlap (f.cycleFamily (extensionState ω.1 ω.2 j)) id ≤
          K*(N:ℝ)/Real.log (f.mu (extensionState ω.1 ω.2 j)) := by
  obtain ⟨K,hK,hbound⟩ := Frame.main_uniformOverlap_eventually r hr C B hC hB
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,inherited_frame_density_eventually r 0 C hC.le]
    with N hb hd
  intro M ell original offset hadm f j h c L ω hh hMj hj hreg hbudget
  let H := extensionState ω.1 ω.2 j
  have hden := hd M ell original offset hadm f ∅ (by simp) j h c L ω hMj hj hreg
  have hupper := f.entropyInstance_inherited_regular j h c C L ω hh hreg hbudget.1
  let d : Frame.CoarseMainInput r C B N :=
    { original := original
      frame := f
      host := H
      budget := hbudget
      density := hden.2.2
      degree := by
        intro v
        have hv := hupper.upper_degree v
        change _ ≤ C*(f.entropyInstance H hbudget.1).μ at hv
        rw [f.entropyInstance_mu] at hv
        exact hv }
  exact hb d
end LooseHamilton.CandidateBalance
