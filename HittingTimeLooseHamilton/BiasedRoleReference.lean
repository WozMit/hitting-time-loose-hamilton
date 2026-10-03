module

public import HittingTimeLooseHamilton.BiasedRoleProjection
public import HittingTimeLooseHamilton.BiasedRoleHostBias
public import HittingTimeLooseHamilton.BiasedCloneMean

public section

/-! Exact normalization and final triangle inequality for the printed role sum. -/
noncomputable section
namespace LooseHamilton
open Finset FiniteEntropy
open scoped BigOperators

lemma privateFraction_pos (r : ℕ) (hr : 3≤r) : 0 < privateFraction r := by
  have h : (3:ℝ)≤r := by exact_mod_cast hr
  unfold privateFraction
  exact div_pos (by linarith) (by linarith)

lemma junctionFraction_pos_lt_one (r : ℕ) (hr : 3≤r) :
    0<junctionFraction r ∧ junctionFraction r<1 := by
  have h : (3:ℝ)≤r := by exact_mod_cast hr
  unfold junctionFraction
  constructor
  · exact div_pos zero_lt_one (by linarith)
  · exact (div_lt_one (by linarith)).mpr (by linarith)

lemma one_sub_junctionFraction (r : ℕ) (hr : 3≤r) :
    1-junctionFraction r=privateFraction r := by
  have h : (3:ℝ)≤r := by exact_mod_cast hr
  unfold junctionFraction privateFraction
  field_simp [show (r:ℝ)-1≠0 by linarith]
  <;> ring

lemma biased_role_reference_identity (r : ℕ) (hr : 3≤r) (μ : ℝ) (hμ : 0<μ) :
    (junctionFraction r)^2*(privateFraction r)^(r-2)/
      ((privateFraction r)^(r-2)*μ) = 1/(((r:ℝ)-1)^2*μ) := by
  have hb : (privateFraction r)^(r-2)≠0 := pow_ne_zero _ (privateFraction_pos r hr).ne'
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  unfold junctionFraction
  field_simp [hb, hμ.ne', show (r:ℝ)-1≠0 by linarith]
  <;> ring

variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def roleCloneDeviation (r : ℕ) (markers G : SimpleHypergraph V)
    (root : ↥markers) (a : ↥root.val) (p : Law (BiasedCycleState r markers G))
    (lam : ℝ) : ℝ :=
  ∑ e ∈ eligibleRoleEdges markers G, ∑ uv ∈ e.offDiag,
    |directedRoleProbability r markers G root a p e uv.1 uv.2-
      ConnectedCloneCycle.junctionRoleProbability root a (p.map biasedConnectedCycle) e uv.1 uv.2/lam|

@[expose] def roleJunctionDeviation (r : ℕ) (markers G : SimpleHypergraph V)
    (root : ↥markers) (a : ↥root.val) (p : Law (BiasedCycleState r markers G)) : ℝ :=
  ∑ e ∈ eligibleRoleEdges markers G, ∑ uv ∈ e.offDiag,
    |ConnectedCloneCycle.junctionRoleProbability root a (p.map biasedConnectedCycle) e uv.1 uv.2-
      (junctionFraction r)^2*(privateFraction r)^(r-2)|

/-- The target is exactly 1/((r-1)^2 mu), with no orientation factor missing. -/
theorem biasedRoleDeviation_triangle (r : ℕ) (hr : 3≤r)
    (markers G : SimpleHypergraph V) (root : ↥markers) (a : ↥root.val)
    (p : Law (BiasedCycleState r markers G))
    (hμ : 0 < meanDegree (V:=V) r G.card) :
    biasedRoleDeviation r markers G root a p ≤
      roleCloneDeviation r markers G root a p
        ((privateFraction r)^(r-2)*meanDegree (V:=V) r G.card) +
      roleJunctionDeviation r markers G root a p /
        ((privateFraction r)^(r-2)*meanDegree (V:=V) r G.card) := by
  let lam := (privateFraction r)^(r-2)*meanDegree (V:=V) r G.card
  have hlam : 0<lam := mul_pos (pow_pos (privateFraction_pos r hr) _) hμ
  have hpoint (e : Finset V) (uv : V×V) :
      |directedRoleProbability r markers G root a p e uv.1 uv.2-
        1/(((r:ℝ)-1)^2*meanDegree (V:=V) r G.card)| ≤
      |directedRoleProbability r markers G root a p e uv.1 uv.2-
        ConnectedCloneCycle.junctionRoleProbability root a (p.map biasedConnectedCycle) e uv.1 uv.2/lam|+
      |ConnectedCloneCycle.junctionRoleProbability root a (p.map biasedConnectedCycle) e uv.1 uv.2-
        (junctionFraction r)^2*(privateFraction r)^(r-2)|/lam := by
    rw [← biased_role_reference_identity r hr _ hμ]
    have h := abs_sub_le (directedRoleProbability r markers G root a p e uv.1 uv.2)
      (ConnectedCloneCycle.junctionRoleProbability root a (p.map biasedConnectedCycle) e uv.1 uv.2/lam)
      ((junctionFraction r)^2*(privateFraction r)^(r-2)/lam)
    simpa only [←sub_div,abs_div,abs_of_pos hlam] using h
  have h := sum_le_sum (fun e (_ : e∈eligibleRoleEdges markers G) =>
    sum_le_sum (fun uv (_ : uv∈e.offDiag) => hpoint e uv))
  simpa only [sum_add_distrib,←sum_div,biasedRoleDeviation,roleCloneDeviation,
    roleJunctionDeviation,eligibleRoleEdges,lam] using h
end LooseHamilton
