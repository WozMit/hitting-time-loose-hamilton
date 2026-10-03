module

public import HittingTimeLooseHamilton.FirstFailureStatement

public section

noncomputable section
namespace LooseHamilton.FirstFailure

theorem not_pathFailure_iff {N : ℕ} (r m : ℕ)
    (markers : Finset (Finset (Fin N))) (D B : ℝ)
    (H : ℕ → SimpleHypergraph (Fin N)) :
    ¬ PathFailure r m markers D B H ↔
      ∀ j : ℕ, m ≤ j → j ≤ (completeEdges (Fin N) r).card →
        0 < cycleCount r markers (H j) (originalPorts markers) ∧
        logarithmicBaseline r (ordinaryEdgeCount r markers) j markers - B ≤
          Real.log (cycleCount r markers (H j) (originalPorts markers) : ℝ) ∧
        ∀ e ∈ H j, cycleMarginal r markers (H j) (originalPorts markers) e ≤
          D * (ordinaryEdgeCount r markers : ℝ) / j := by
  constructor
  · intro hn j hj hK
    refine ⟨Nat.pos_of_ne_zero (fun hz => hn ⟨j,hj,hK,Or.inl hz⟩), ?_, ?_⟩
    · exact le_of_not_gt (fun hl => hn ⟨j,hj,hK,Or.inr (Or.inl hl)⟩)
    · intro e he
      exact le_of_not_gt (fun hq => hn ⟨j,hj,hK,Or.inr (Or.inr ⟨e,he,hq⟩)⟩)
  · intro h ⟨j,hj,hK,hbad⟩
    obtain ⟨hp,hl,hq⟩ := h j hj hK
    rcases hbad with hz | hd | ⟨e,he,hviol⟩
    · exact (Nat.ne_of_gt hp) hz
    · exact (not_lt_of_ge hl) hd
    · exact (not_lt_of_ge (hq e he)) hviol

end LooseHamilton.FirstFailure
