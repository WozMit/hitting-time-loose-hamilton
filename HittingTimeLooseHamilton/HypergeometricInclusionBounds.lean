module

public import HittingTimeLooseHamilton.HypergeometricAlgebra
public import HittingTimeLooseHamilton.UniformPrefixProbability

public section

/-! Upper bounds for prescribed edges in the actual fixed-time process. -/
noncomputable section
namespace LooseHamilton
namespace Hypergeometric

lemma inclusion_ratio_dual {N m k : ℕ} (hm : m ≤ N) (hk : k ≤ m) :
    ((N - k).choose (m - k) : ℝ) / (N.choose m : ℝ) =
      (m.choose k : ℝ) / (N.choose k : ℝ) := by
  have h := Nat.choose_mul (n := N) hk
  have hm0 : (N.choose m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos hm))
  have hk0 : (N.choose k : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (hk.trans hm)))
  apply (div_eq_div_iff hm0 hk0).mpr
  have hh : (N.choose m : ℝ) * (m.choose k : ℝ) =
      (N.choose k : ℝ) * ((N-k).choose (m-k) : ℝ) := by exact_mod_cast h
  nlinarith

lemma inclusion_ratio_le {N m k : ℕ} (hm : m ≤ N) (hk : k ≤ m) (hN : 0 < N) :
    ((N - k).choose (m - k) : ℝ) / (N.choose m : ℝ) ≤ ((m : ℝ) / N)^k := by
  rw [inclusion_ratio_dual hm hk]
  exact choose_ratio_le_pow hm hN (hk.trans hm)
end Hypergeometric

/-- Sampling without replacement bounds the probability of prescribed edges
by the product of their marginal inclusion probabilities. -/
theorem process_contains_probability_le {V : Type*} [Fintype V] [DecidableEq V]
    {r m : ℕ} (hm : m ≤ (completeEdges V r).card)
    (hN : 0 < (completeEdges V r).card) (K : SimpleHypergraph V)
    (hK : K ⊆ completeEdges V r) (hk : K.card ≤ m) :
    (processLaw V r).event (fun σ => K ⊆ processState σ m) ≤
      ((m : ℝ) / (completeEdges V r).card)^K.card := by
  rw [process_contains_probability m hm K hK hk, completeEdges_card]
  apply Hypergeometric.inclusion_ratio_le
  · simpa only [completeEdges_card] using hm
  · exact hk
  · simpa only [completeEdges_card] using hN
end LooseHamilton
