module

public import HittingTimeLooseHamilton.UniformPrefixProbability
public import HittingTimeLooseHamilton.HypergeometricAlgebra
public import HittingTimeLooseHamilton.FiniteAvoidanceTail

public section

noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

/-- Negative dependence for absence from a uniform edge-order prefix. -/
theorem process_avoids_le (m : ℕ) (hm : m ≤ (completeEdges V r).card)
    (hN : 0 < (completeEdges V r).card)
    (D : SimpleHypergraph V) (hD : D ⊆ completeEdges V r) :
    (processLaw V r).event (fun σ => Disjoint (processState σ m) D) ≤
      (1 - (m : ℝ) / (completeEdges V r).card) ^ D.card := by
  rw [process_avoids_probability m hm D hD]
  simpa only [completeEdges_card] using
    Hypergeometric.avoidance_ratio_le hm hN (card_le_card hD)

/-- Finite hypergeometric lower tail in algebraic exponential-Markov form. -/
theorem process_intersection_lower_tail (m : ℕ) (hm : m ≤ (completeEdges V r).card)
    (hN : 0 < (completeEdges V r).card)
    (D : SimpleHypergraph V) (hD : D ⊆ completeEdges V r)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (k : ℕ) :
    (processLaw V r).event (fun σ => (processState σ m ∩ D).card ≤ k) ≤
      (1 - (m : ℝ) / (completeEdges V r).card * (1 - q)) ^ D.card / q ^ k := by
  classical
  have hn : (0 : ℝ) < (completeEdges V r).card := Nat.cast_pos.mpr hN
  have hρ : (m : ℝ) / (completeEdges V r).card ≤ 1 :=
    (div_le_one hn).mpr (by exact_mod_cast hm)
  have hav (T : SimpleHypergraph V) (hT : T ⊆ D) :
      (processLaw V r).event (fun σ => True ∧ Disjoint (processState σ m) T) ≤
        1 * (1 - (m : ℝ) / (completeEdges V r).card) ^ T.card := by
    simpa only [true_and, one_mul] using process_avoids_le m hm hN T (hT.trans hD)
  have h := Hypergeometric.lower_tail_le_of_avoidance (processLaw V r)
    (fun σ => processState σ m) D (fun _ => True) q
    (1 - (m : ℝ) / (completeEdges V r).card) 1 hq0 hq1 (sub_nonneg.mpr hρ) k hav
  have heq : q + (1 - q) * (1 - (m : ℝ) / (completeEdges V r).card) =
      1 - (m : ℝ) / (completeEdges V r).card * (1 - q) := by ring
  simpa only [true_and, one_mul, heq] using h

/-- The hypergeometric Chernoff lower tail, without a tail hypothesis. -/
theorem process_intersection_lower_tail_exp (m : ℕ) (hm : m ≤ (completeEdges V r).card)
    (hN : 0 < (completeEdges V r).card)
    (D : SimpleHypergraph V) (hD : D ⊆ completeEdges V r)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (k : ℕ) :
    (processLaw V r).event (fun σ => (processState σ m ∩ D).card ≤ k) ≤
      Real.exp (-(m : ℝ) / (completeEdges V r).card * D.card * (1 - q) -
        (k : ℝ) * Real.log q) := by
  classical
  have hn : (0 : ℝ) < (completeEdges V r).card := Nat.cast_pos.mpr hN
  have hρ : (m : ℝ) / (completeEdges V r).card ≤ 1 :=
    (div_le_one hn).mpr (by exact_mod_cast hm)
  have hav (T : SimpleHypergraph V) (hT : T ⊆ D) :
      (processLaw V r).event (fun σ => True ∧ Disjoint (processState σ m) T) ≤
        1 * (1 - (m : ℝ) / (completeEdges V r).card) ^ T.card := by
    simpa only [true_and, one_mul] using process_avoids_le m hm hN T (hT.trans hD)
  have h := Hypergeometric.lower_tail_exp_le_of_avoidance (processLaw V r)
    (fun σ => processState σ m) D (fun _ => True) q
    ((m : ℝ) / (completeEdges V r).card) 1 hq0 hq1 (by positivity) hρ (by norm_num) k hav
  simpa only [true_and, one_mul, neg_div] using h

end LooseHamilton
