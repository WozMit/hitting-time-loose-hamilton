module

public import HittingTimeLooseHamilton

public section

/-! # Solution of the advertised hitting-time statement -/

noncomputable section
namespace HittingTimeLooseHamilton

/-- Proportion of complete edge orders for which the two hitting times
are equal. -/
@[expose] def hittingTimeProbability (n r : ℕ) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun σ : LooseHamilton.EdgeOrder (Fin n) r =>
    LooseHamilton.tauLooseHamilton σ = LooseHamilton.tauOne σ)).card : ℝ) /
      Fintype.card (LooseHamilton.EdgeOrder (Fin n) r)

/-- For every fixed r >= 3, asymptotically almost surely loose Hamiltonicity
appears exactly when the last isolated vertex disappears. Writing n=(r-1)q
parametrizes all vertex counts satisfying the necessary divisibility condition. -/
theorem main_result (r : ℕ) (hr : 3 ≤ r) :
    Filter.Tendsto (fun q : ℕ => hittingTimeProbability ((r - 1) * q) r)
      Filter.atTop (nhds 1) := by
  classical
  have probability_eq (n : ℕ) :
      hittingTimeProbability n r = LooseHamilton.hittingTimeProbability (Fin n) r := by
    symm
    have h := FiniteEntropy.Law.uniform_event (fun σ : LooseHamilton.EdgeOrder (Fin n) r =>
      LooseHamilton.tauLooseHamilton σ = LooseHamilton.tauOne σ)
    exact h
  simpa only [probability_eq] using LooseHamilton.theorem11 r hr

end HittingTimeLooseHamilton
