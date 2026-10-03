module

public import HittingTimeLooseHamilton.FrameFinalRecordUniform
public import HittingTimeLooseHamilton.FrameBoundaryIntegration

public section

/-! The repaired uniform candidate-balance theorem, with exactly the unchanged
specification from CandidateBalanceSpecification. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame Filter FrameScales Topology

/-- Proposition 8.1 (uniform candidate balance), in the exact previously fixed
formal statement. The rate depends only on r; the single threshold precedes
all terminal data, labelled frames, times and feasible boundary records. -/
theorem uniform_candidate_balance : UniformCandidateBalance := by
  intro r hr
  refine ⟨finalRate r,finalRate_pos (by omega),?_⟩
  intro B offset c C L hB _ _ hC hL h boundaryBound hh
  have he := record_exponential_bound_eventually r boundaryBound hr C B L offset hC hB hL
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp he
  refine ⟨N₀,?_⟩
  intro N hN M ell original admissible f j hMj hj
  letI := admissible.feasible
  have hrecords := hN₀ N hN M ell original admissible
  constructor
  · have hp := complement_bounds_unconditional j f (∅ : Finset (Fin N))
      (BadSource f j h c C L B) (errorBound N (finalRate r)) (by
        intro A0 B0 hb
        exact hrecords f ∅ (by simp) j h c hh hMj hj A0 B0 hb)
    simpa only [Fintype.card_fin] using hp
  · intro b hb hfeasible
    have hp := complement_bounds_boundary j f b hfeasible
      (BadSource f j h c C L B) (errorBound N (finalRate r)) (by
        intro A0 B0 he
        exact hrecords f b.vertices hb j h c hh hMj hj A0 B0 he)
    simpa only [Fintype.card_fin] using hp

/-- Manuscript-number alias of the exact uniform candidate-balance theorem. -/
theorem proposition81 : UniformCandidateBalance := uniform_candidate_balance

end LooseHamilton.CandidateBalance

namespace LooseHamilton
/-- Proposition 8.1, with the unchanged repaired specification. -/
theorem proposition81 : CandidateBalance.UniformCandidateBalance :=
  CandidateBalance.uniform_candidate_balance
end LooseHamilton
