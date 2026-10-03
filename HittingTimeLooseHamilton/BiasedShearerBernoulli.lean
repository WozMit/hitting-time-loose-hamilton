module

public import HittingTimeLooseHamilton.BiasedShearerPinsker
public import HittingTimeLooseHamilton.BernoulliSubsetLaw

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy

/-- A Bernoulli bit, with `true` having probability a. -/
@[expose] def bernoulliBitLaw (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : Law Bool where
  mass b := if b then a else 1-a
  nonneg b := by cases b <;> simp [ha0, sub_nonneg.mpr ha1]
  total := by simp

lemma bernoulliBitLaw_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (b : Bool) :
    0 < (bernoulliBitLaw a ha0.le ha1.le).mass b := by
  cases b <;> simp [bernoulliBitLaw, ha0, sub_pos.mpr ha1]

/-- Exact probability of a fixed pattern under the Bernoulli product law. -/
lemma bernoulli_pattern_mass {V : Type*} [Fintype V] [DecidableEq V]
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (s : Finset V) :
    (independentCoordinateLaw (fun _ : V => bernoulliBitLaw a ha0 ha1)).mass
      (fun v => decide (v ∈ s)) =
        a ^ s.card * (1-a) ^ (Fintype.card V-s.card) := by
  change (∏ v, if decide (v ∈ s) then a else 1-a) = _
  simpa only [decide_eq_true_eq] using
    (BernoulliSubset.weight_eq_prod (fun _ : V => a) (fun _ => 1-a) s).symm.trans
      (BernoulliSubset.weight_const a (1-a) s)

/-- In particular, a role having precisely two junction vertices has the
reference probability a²(1-a)^(r-2). -/
lemma bernoulli_two_point_pattern_mass {V : Type*} [Fintype V] [DecidableEq V]
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (u v : V) (huv : u ≠ v) :
    (independentCoordinateLaw (fun _ : V => bernoulliBitLaw a ha0 ha1)).mass
      (fun w => decide (w ∈ ({u,v} : Finset V))) =
        a ^ 2 * (1-a) ^ (Fintype.card V-2) := by
  simpa [Finset.card_pair huv] using bernoulli_pattern_mass a ha0 ha1 ({u,v} : Finset V)

end LooseHamilton
