module

public import HittingTimeLooseHamilton.ExceptionalSetModels
public import HittingTimeLooseHamilton.FiniteMomentBounds
public import HittingTimeLooseHamilton.KahnRandomOrder
public import Mathlib.Topology.Algebra.Order.Field

public section

/-! The exact target statement and the finite union-bound reduction for
Lemma 3.2. The reduction makes its probabilistic inputs explicit. -/
noncomputable section
namespace LooseHamilton
open Finset Filter
open scoped BigOperators Topology
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact target of Lemma 3.2. This definition is a statement, not a proof. -/
@[expose] def Lemma32 : Prop := ∀ r : ℕ, 3 ≤ r → ∃ C : ℝ, 0 < C ∧
  Tendsto (fun n : ℕ => (processLaw (Fin n) r).event (stoppedExceptionalEvent C))
    atTop (𝓝 1)

/-- The five possible failures in an early/late bracketing argument. -/
@[expose] def exceptionalFailure {r : ℕ} (C : ℝ) (lo hi : ℕ) :
    Fin 5 → EdgeOrder V r → Prop
  | 0, σ => ¬ ∃ t : ℕ, tauOne σ = (t : WithTop ℕ) ∧ lo ≤ t ∧ t ≤ hi
  | 1, σ => ¬ ((lowDegreeVertices (processState σ lo)).card : ℝ) ≤
      Real.rpow (Fintype.card V : ℝ) (1 / 12 : ℝ)
  | 2, σ => ¬ ∀ v : V, (vertexDegree (processState σ hi) v : ℝ) ≤
      C * Real.log (Fintype.card V : ℝ)
  | 3, σ => ¬ ∀ u v : V, u ≠ v → pairDegree (processState σ hi) u v ≤ 2
  | 4, σ => ¬ ∀ u ∈ lowDegreeVertices (processState σ lo),
      ∀ v ∈ lowDegreeVertices (processState σ lo),
      u ≠ v → ¬ shortBergeConnected (processState σ hi) u v

/-- No failure among the five estimates implies the complete stopped event. -/
theorem stoppedExceptionalEvent_of_no_failure [Nonempty V] {r : ℕ}
    (C : ℝ) (lo hi : ℕ) (σ : EdgeOrder V r)
    (hbase : 1 ≤ lowerDegreeBase V)
    (h : ∀ i, ¬ exceptionalFailure C lo hi i σ) : stoppedExceptionalEvent C σ := by
  classical
  have h0 := not_not.mp (h 0)
  obtain ⟨t, ht, hlo, hhi⟩ := h0
  exact stoppedExceptionalEvent_of_bracket σ ht hlo hhi hbase
    (not_not.mp (h 1)) (not_not.mp (h 2)) (not_not.mp (h 3)) (not_not.mp (h 4))

/-- Explicit finite error bound; no independence between failures is required. -/
theorem exceptional_failure_bound [Nonempty V] {r : ℕ}
    (C : ℝ) (lo hi : ℕ) (hbase : 1 ≤ lowerDegreeBase V) :
    1 - (processLaw V r).event (stoppedExceptionalEvent C) ≤
      ∑ i : Fin 5, (processLaw V r).event (exceptionalFailure C lo hi i) := by
  classical
  rw [← FiniteEntropy.Law.event_compl]
  apply le_trans ((processLaw V r).event_mono ?_)
    ((processLaw V r).finite_union_bound (exceptionalFailure C lo hi))
  intro σ hbad
  by_contra hn
  push_neg at hn
  exact hbad (stoppedExceptionalEvent_of_no_failure C lo hi σ hbase hn)

/-- Once the five concrete error probabilities tend to zero, the original
stopped-process event has probability tending to one. This theorem does not
assume that the stopped host was sampled from a different probability law. -/
theorem exceptional_probability_tendsto_of_failures {r : ℕ} (C : ℝ)
    (lo hi : ℕ → ℕ)
    (hbase : ∀ᶠ n : ℕ in atTop, 1 ≤ lowerDegreeBase (Fin n))
    (herr : Tendsto (fun n : ℕ => ∑ i : Fin 5,
      (processLaw (Fin n) r).event (exceptionalFailure C (lo n) (hi n) i))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (processLaw (Fin n) r).event (stoppedExceptionalEvent C))
      atTop (𝓝 1) := by
  have hz : Tendsto (fun n : ℕ =>
      1 - (processLaw (Fin n) r).event (stoppedExceptionalEvent C)) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun n =>
      sub_nonneg.mpr ((processLaw (Fin n) r).event_le_one _)) ?_ herr
    filter_upwards [hbase, eventually_gt_atTop 0] with n hb hn
    letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact exceptional_failure_bound C (lo n) (hi n) hb
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hz
  simpa only [sub_zero, sub_sub_cancel] using h
end LooseHamilton
