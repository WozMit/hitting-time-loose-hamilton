module

public import HittingTimeLooseHamilton.IsolatedVertexMoments
public import HittingTimeLooseHamilton.HypergeometricAvoidanceLower

public section

/-! Explicit exponential first- and second-moment estimates for the isolation
stopping time. The two correction exponents retain sampling without replacement. -/
noncomputable section
namespace LooseHamilton
open Finset

private theorem variance_ratio_le {n a b : ℝ} (hn : 0 < n) (ha : 0 < a) (hb : 0 ≤ b) :
    (n*a + n*(n-1)*b - (n*a)^2)/(n*a)^2 ≤ 1/(n*a) + b/a^2 - 1 := by
  have he : (n*a + n*(n-1)*b - (n*a)^2)/(n*a)^2 =
      1/(n*a) + b/a^2 - 1 - b/(n*a^2) := by
    field_simp
    <;> ring
  rw [he]
  have hp : 0 ≤ b/(n*a^2) := div_nonneg hb (mul_nonneg hn.le (sq_nonneg a))
  linarith

private theorem isolation_exponential_comparison {n a b A B : ℝ}
    (hn : 0 < n) (ha : Real.exp (-A) ≤ a) (hb : b ≤ Real.exp (-B)) :
    1/(n*a) + b/a^2 - 1 ≤ Real.exp A/n + Real.exp (2*A-B) - 1 := by
  have hapos : 0 < a := (Real.exp_pos _).trans_le ha
  have hfirst : 1/(n*a) ≤ Real.exp A/n := by
    calc
      _ ≤ 1/(n*Real.exp (-A)) := one_div_le_one_div_of_le
        (mul_pos hn (Real.exp_pos _)) (mul_le_mul_of_nonneg_left ha hn.le)
      _ = _ := by rw [Real.exp_neg]; field_simp
  have hsecond : b/a^2 ≤ Real.exp (2*A-B) := by
    calc
      _ ≤ Real.exp (-B)/a^2 := div_le_div_of_nonneg_right hb (sq_nonneg a)
      _ ≤ Real.exp (-B)/(Real.exp (-A))^2 := by
        apply div_le_div_of_nonneg_left (Real.exp_pos _).le (sq_pos_of_pos (Real.exp_pos _))
        exact pow_le_pow_left₀ (Real.exp_pos _).le ha 2
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_sub]
        congr 1
        ring
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

/-- The exact second-moment bound, with its harmless diagonal correction dropped. -/
theorem tauOne_early_probability_le_ratio (hr : 2 ≤ r) (hn : 1 ≤ Fintype.card V)
    (m : ℕ) (hm : m ≤ (completeEdges V r).card)
    (ha : 0 < isolationProbability V r m) :
    (processLaw V r).event (fun σ => tauOne σ ≤ (m : WithTop ℕ)) ≤
      1/((Fintype.card V : ℝ)*isolationProbability V r m) +
        pairIsolationProbability V r m/(isolationProbability V r m)^2 - 1 := by
  have hnpos : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr (by omega)
  have hb : 0 ≤ pairIsolationProbability V r m := by
    unfold pairIsolationProbability
    positivity
  have h := tauOne_early_probability_le hr m hm (mul_pos hnpos ha)
  rw [Nat.cast_sub hn, Nat.cast_one] at h
  exact h.trans (variance_ratio_le hnpos ha hb)

/-- The lower isolation correction exponent. -/
@[expose] def isolationLowerExponent (V : Type*) [Fintype V] (r m : ℕ) : ℝ :=
  ((Fintype.card V - 1).choose (r-1) : ℝ) * m /
    ((Fintype.card V).choose r - m - (Fintype.card V - 1).choose (r-1) : ℕ)

/-- The upper simultaneous-isolation exponent. -/
@[expose] def isolationPairExponent (V : Type*) [Fintype V] (r m : ℕ) : ℝ :=
  ((2*(Fintype.card V - 1).choose (r-1) - (Fintype.card V - 2).choose (r-2) : ℕ) : ℝ) * m /
    ((Fintype.card V).choose r : ℝ)

/-- Explicit finite early-time estimate. -/
theorem tauOne_early_probability_le_exp (hr : 2 ≤ r) (hn : 2 ≤ Fintype.card V)
    (m : ℕ) (hgap : m + (Fintype.card V - 1).choose (r-1) < (Fintype.card V).choose r) :
    (processLaw V r).event (fun σ => tauOne σ ≤ (m : WithTop ℕ)) ≤
      Real.exp (isolationLowerExponent V r m)/(Fintype.card V : ℝ) +
        Real.exp (2*isolationLowerExponent V r m-isolationPairExponent V r m) - 1 := by
  have hm : m ≤ (completeEdges V r).card := by rw [completeEdges_card]; omega
  have hN : 0 < (Fintype.card V).choose r := by omega
  have ha : Real.exp (-isolationLowerExponent V r m) ≤ isolationProbability V r m :=
    Hypergeometric.avoidance_ratio_ge_exp hgap
  have hb : pairIsolationProbability V r m ≤ Real.exp (-isolationPairExponent V r m) := by
    apply Hypergeometric.avoidance_ratio_le_exp (by omega) hN
    obtain ⟨u,v,huv⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card V)
    rw [← edgeIncidences_union_card hr huv]
    exact (card_le_card (subset_univ _)).trans (by simp [completeEdges_card])
  exact (tauOne_early_probability_le_ratio hr (by omega) m hm ((Real.exp_pos _).trans_le ha)).trans
    (isolation_exponential_comparison (Nat.cast_pos.mpr (by omega)) ha hb)

/-- Explicit finite late-time estimate. -/
theorem tauOne_late_probability_le_exp (hr : 1 ≤ r) (m : ℕ)
    (hm : m ≤ (completeEdges V r).card) (hN : 0 < (Fintype.card V).choose r) :
    (processLaw V r).event (fun σ => (m : WithTop ℕ) < tauOne σ) ≤
      (Fintype.card V : ℝ) * Real.exp (-(((Fintype.card V - 1).choose (r-1) : ℝ) * m /
        ((Fintype.card V).choose r : ℝ))) := by
  apply (tauOne_late_probability_le hr m hm).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Hypergeometric.avoidance_ratio_le_exp (by simpa only [completeEdges_card] using hm) hN
  by_cases hn : Nonempty V
  · letI := hn
    obtain ⟨v⟩ := hn
    rw [← edgeIncidences_card hr v]
    exact (card_le_card (subset_univ _)).trans (by simp [completeEdges_card])
  · haveI : IsEmpty V := not_nonempty_iff.mp hn
    have hcard : Fintype.card V = 0 := Fintype.card_eq_zero
    simp [hcard,Nat.choose_eq_zero_of_lt (by omega : 0 < r)] at hN
end LooseHamilton
