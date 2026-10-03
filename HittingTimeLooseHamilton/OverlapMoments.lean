module

public import HittingTimeLooseHamilton.KahnLaw
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

public section

noncomputable section
open scoped BigOperators
namespace FiniteEntropy.Law
variable {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]

/-- Expected intersection size for two independent samples from the same law. -/
@[expose] def independentOverlap (p : Law Ω) (S : Ω → Finset V) : ℝ :=
  ∑ a, ∑ b, p.mass a*p.mass b*((S a∩S b).card:ℝ)

lemma card_inter_eq_indicator_sum (A B : Finset V) :
    ((A∩B).card:ℝ) = ∑ v : V, if v∈A ∧ v∈B then (1:ℝ) else 0 := by
  classical
  simp [←Finset.mem_inter]

/-- Independence turns expected overlap into the sum of squared marginals. -/
theorem independentOverlap_eq_sum_sq (p : Law Ω) (S : Ω → Finset V) :
    p.independentOverlap S = ∑ v : V, (p.event (fun a => v∈S a))^2 := by
  classical
  unfold independentOverlap
  simp_rw [card_inter_eq_indicator_sum, Finset.mul_sum]
  calc
    _ = ∑ v : V, ∑ a : Ω, ∑ b : Ω,
        p.mass a*p.mass b*(if v∈S a ∧ v∈S b then (1:ℝ) else 0) := by
      calc
        _ = ∑ a : Ω, ∑ v : V, ∑ b : Ω,
            p.mass a*p.mass b*(if v∈S a ∧ v∈S b then (1:ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      unfold event
      rw [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp_all

lemma independentOverlap_nonneg (p : Law Ω) (S : Ω → Finset V) :
    0≤p.independentOverlap S := by
  rw [independentOverlap_eq_sum_sq]
  positivity
end FiniteEntropy.Law
