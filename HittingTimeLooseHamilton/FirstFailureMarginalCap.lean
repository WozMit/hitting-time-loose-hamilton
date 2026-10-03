module

public import HittingTimeLooseHamilton.UniformMarginalCap

public section

noncomputable section
namespace LooseHamilton.FirstFailure

/-- Increasing the cap coefficient only shrinks the whole-path failure event. -/
theorem marginal_failure_mono {N r m : ℕ} {ell : Fin N → ℕ}
    (markers : Finset (Finset (Fin N))) {D D' : ℝ} (hD : D ≤ D')
    (ω : CandidateBalance.Outcome (Fin N) r m ell)
    (h : UniformMarginalCap.Failure markers D' ω) :
    UniformMarginalCap.Failure markers D ω := by
  obtain ⟨j,hj,hK,hA,e,he,hq⟩ := h
  refine ⟨j,hj,hK,hA,e,he,lt_of_le_of_lt ?_ hq⟩
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

end LooseHamilton.FirstFailure
