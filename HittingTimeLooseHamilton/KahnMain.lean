module

public import HittingTimeLooseHamilton.KahnReduction
public import HittingTimeLooseHamilton.KahnMatchingEntropy
public import HittingTimeLooseHamilton.KahnLocalBound

public section

/-! # Theorem 4.2 of Kahn, Asymptotics for Shamir's Problem -/
noncomputable section
open scoped BigOperators
namespace Kahn

/-- The finite random-order entropy estimate, with every counting and entropy
premise discharged. -/
theorem entropy_reveal_bound : EntropyRevealBound := by
  intro r hr n hn hdiv H μ
  have hrp : 0 < r := by omega
  have hnr : r ≤ n := by nlinarith
  have hm : 0 < n / r := Nat.div_pos hnr hrp
  have hrm : r - 1 < n / r := by
    have h : r ≤ n / r := (Nat.le_div_iff_mul_le hrp).mpr hn
    omega
  calc
    _ ≤ ∑ v : Fin n, (MatchingLaw.jointRevealLaw μ v).conditionalEntropy Prod.snd :=
      MatchingLaw.entropy_le_jointReveal μ hrp
    _ ≤ ∑ v : Fin n, ((1 / (r : ℝ)) *
        FiniteEntropy.entropy (MatchingLaw.marginal μ v).mass +
        (1 / (n : ℝ)) * ∑ Y ∈ MatchingLaw.candidates (r := r) v,
          (MatchingLaw.marginal μ v).mass Y * ∑ i ∈ Finset.range (n / r),
            Real.log ((((i : ℝ) + 1) / (n / r : ℕ)) ^ (r - 1) +
              MatchingLaw.gamma μ v Y)) := by
      exact Finset.sum_le_sum fun v _ => MatchingLaw.local_entropy_bound μ hrp hm hrm hdiv v
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        MatchingLaw.marginalEntropySum, MatchingLaw.weightedPenalty]

/-- Kahn's Theorem 4.2, with the two asymptotic error terms expressed by
uniform constants and a threshold depending only on the fixed uniformity. -/
theorem theorem42 : Theorem42 := theorem42_of_reveal_bound entropy_reveal_bound

end Kahn
