module

public import HittingTimeLooseHamilton.KahnLaw

public section

/-! Elementary finite probability bounds and moment identities.
All sums use the existing finite-law mass function; no measure-theoretic or
independence assumptions are introduced. -/
noncomputable section
open scoped BigOperators
namespace FiniteEntropy.Law
variable {Ω I : Type*} [Fintype Ω] [Fintype I]

/-- Expectation of a real-valued function under a finite law. -/
@[expose] def finiteMean (p : FiniteEntropy.Law Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, p.mass ω * X ω

theorem finiteMean_nonneg (p : FiniteEntropy.Law Ω) {X : Ω → ℝ}
    (hX : ∀ ω, 0 ≤ X ω) : 0 ≤ p.finiteMean X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (p.nonneg ω) (hX ω)

theorem finite_markov (p : FiniteEntropy.Law Ω) {X : Ω → ℝ}
    (hX : ∀ ω, 0 ≤ X ω) {a : ℝ} (ha : 0 < a) :
    p.event (fun ω => a ≤ X ω) ≤ p.finiteMean X / a := by
  classical
  apply (le_div_iff₀ ha).mpr
  unfold event finiteMean
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : a ≤ X ω
  · simp only [h, if_true]
    exact mul_le_mul_of_nonneg_left h (p.nonneg ω)
  · simp only [h, if_false, zero_mul]
    exact mul_nonneg (p.nonneg ω) (hX ω)

theorem finite_union_bound (p : FiniteEntropy.Law Ω) (E : I → Ω → Prop) :
    p.event (fun ω => ∃ i, E i ω) ≤ ∑ i, p.event (E i) := by
  classical
  unfold event
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : ∃ i, E i ω
  · obtain ⟨i,hi⟩ := h
    rw [if_pos ⟨i,hi⟩]
    calc
      p.mass ω = (if E i ω then p.mass ω else 0) := (if_pos hi).symm
      _ ≤ ∑ j, if E j ω then p.mass ω else 0 :=
        Finset.single_le_sum (f := fun j => if E j ω then p.mass ω else 0)
          (fun j _ => ite_nonneg (p.nonneg ω) (le_refl 0)) (Finset.mem_univ i)
  · rw [if_neg h]
    exact Finset.sum_nonneg fun i _ => ite_nonneg (p.nonneg ω) (le_refl 0)

/-- The centered second moment is the second moment minus the squared mean. -/
theorem finiteMean_squared_deviation (p : FiniteEntropy.Law Ω) (X : Ω → ℝ) :
    p.finiteMean (fun ω => (X ω - p.finiteMean X)^2) =
      p.finiteMean (fun ω => (X ω)^2) - (p.finiteMean X)^2 := by
  unfold finiteMean
  have hterm (ω : Ω) :
      p.mass ω * (X ω - ∑ a, p.mass a * X a)^2 =
      p.mass ω * X ω ^ 2 - 2 * (∑ a, p.mass a * X a) * (p.mass ω * X ω) +
        (∑ a, p.mass a * X a)^2 * p.mass ω := by ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [p.total]
  ring

/-- The standard second-moment upper bound for the probability of a zero count.
It actually holds for any real-valued random variable with positive mean. -/
theorem finite_second_moment_zero (p : FiniteEntropy.Law Ω) (X : Ω → ℝ)
    (hmean : 0 < p.finiteMean X) :
    p.event (fun ω => X ω = 0) ≤
      (p.finiteMean (fun ω => (X ω)^2) - (p.finiteMean X)^2) /
        (p.finiteMean X)^2 := by
  have hmono : p.event (fun ω => X ω = 0) ≤
      p.event (fun ω => (p.finiteMean X)^2 ≤ (X ω - p.finiteMean X)^2) := by
    apply p.event_mono
    intro ω hω
    simp [hω]
  have hmarkov := p.finite_markov (fun ω => sq_nonneg (X ω - p.finiteMean X)) (sq_pos_of_pos hmean)
  rw [p.finiteMean_squared_deviation X] at hmarkov
  exact hmono.trans hmarkov

/-- The number of events that occur, regarded as a real random variable. -/
@[expose] def finiteIndicatorCount (E : I → Ω → Prop) (ω : Ω) : ℝ := by
  classical
  exact ∑ i, if E i ω then 1 else 0

theorem finiteIndicatorCount_nonneg (E : I → Ω → Prop) (ω : Ω) :
    0 ≤ finiteIndicatorCount E ω := by
  classical
  exact Finset.sum_nonneg fun i _ => ite_nonneg (by norm_num) (le_refl 0)

/-- The first moment of a count is the sum of the individual probabilities. -/
theorem finiteMean_indicatorCount (p : FiniteEntropy.Law Ω) (E : I → Ω → Prop) :
    p.finiteMean (finiteIndicatorCount E) = ∑ i, p.event (E i) := by
  classical
  simp only [finiteMean, finiteIndicatorCount, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp_all

/-- The second moment of a count is the sum of all ordered pair intersection
probabilities, including the diagonal. -/
theorem finiteMean_indicatorCount_sq (p : FiniteEntropy.Law Ω) (E : I → Ω → Prop) :
    p.finiteMean (fun ω => (finiteIndicatorCount E ω)^2) =
      ∑ i, ∑ j, p.event (fun ω => E i ω ∧ E j ω) := by
  classical
  simp only [finiteMean, finiteIndicatorCount, sq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hi : E i ω <;> by_cases hj : E j ω <;> simp [hi,hj]
end FiniteEntropy.Law
