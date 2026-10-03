module

public import HittingTimeLooseHamilton.FiniteMomentBounds

public section

/-! Averaging and Markov bounds for the fraction of unstable candidates.
The candidate set may be empty, in which case its fraction is defined to be zero.
The events may have arbitrary dependence. -/
noncomputable section
open scoped BigOperators
namespace FiniteEntropy.Law
variable {Ω ι : Type*}
attribute [local instance] Classical.propDecidable

/-- The proportion of candidates whose event occurs. -/
@[expose] def unstableFraction (I : Finset ι) (E : ι → Ω → Prop) (ω : Ω) : ℝ := by
  classical
  exact ((I.filter fun i => E i ω).card : ℝ) / (I.card : ℝ)

lemma unstableFraction_nonneg (I : Finset ι) (E : ι → Ω → Prop) (ω : Ω) :
    0 ≤ unstableFraction I E ω := by
  classical
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma unstableFraction_le_one (I : Finset ι) (E : ι → Ω → Prop) (ω : Ω) :
    unstableFraction I E ω ≤ 1 := by
  classical
  unfold unstableFraction
  by_cases h : I.card = 0
  · simp [h]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)).mpr
    exact_mod_cast Finset.card_filter_le I (fun i => E i ω)

@[simp] lemma unstableFraction_empty (E : ι → Ω → Prop) (ω : Ω) :
    unstableFraction ∅ E ω = 0 := by
  classical
  simp [unstableFraction]

lemma unstableFraction_eq_sum (I : Finset ι) (E : ι → Ω → Prop) (ω : Ω) :
    unstableFraction I E ω = (∑ i ∈ I, if E i ω then (1 : ℝ) else 0) / I.card := by
  classical
  unfold unstableFraction
  congr 1
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter]

variable [Fintype Ω]

/-- Linearity of expectation: the expected fraction is the average event probability. -/
theorem mean_unstableFraction (p : FiniteEntropy.Law Ω)
    (I : Finset ι) (E : ι → Ω → Prop) :
    p.finiteMean (unstableFraction I E) = (∑ i ∈ I, p.event (E i)) / I.card := by
  classical
  simp only [finiteMean, unstableFraction_eq_sum, ← mul_div_assoc, ← Finset.sum_div,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  unfold event
  apply Finset.sum_congr rfl
  intro ω hω
  split_ifs <;> simp

/-- A uniform bound on individual probabilities bounds the expected fraction.
The nonnegativity assumption also covers an empty candidate set. -/
theorem mean_unstableFraction_le (p : FiniteEntropy.Law Ω)
    (I : Finset ι) (E : ι → Ω → Prop) {p₀ : ℝ} (hp₀ : 0 ≤ p₀)
    (hE : ∀ i ∈ I, p.event (E i) ≤ p₀) :
    p.finiteMean (unstableFraction I E) ≤ p₀ := by
  rw [mean_unstableFraction]
  by_cases h : I.card = 0
  · simpa [h] using hp₀
  · apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero h)).mpr
    calc
      ∑ i ∈ I, p.event (E i) ≤ ∑ _i ∈ I, p₀ := Finset.sum_le_sum hE
      _ = p₀ * I.card := by simp [mul_comm]

/-- Markov's inequality with the exact average of the individual probabilities. -/
theorem unstableFraction_tail_average (p : FiniteEntropy.Law Ω)
    (I : Finset ι) (E : ι → Ω → Prop) {δ : ℝ} (hδ : 0 < δ) :
    p.event (fun ω => δ < unstableFraction I E ω) ≤
      ((∑ i ∈ I, p.event (E i)) / I.card) / δ := by
  have hmono : p.event (fun ω => δ < unstableFraction I E ω) ≤
      p.event (fun ω => δ ≤ unstableFraction I E ω) :=
    p.event_mono (fun _ h => le_of_lt h)
  have h := p.finite_markov (unstableFraction_nonneg I E) hδ
  rw [mean_unstableFraction] at h
  exact hmono.trans h

/-- The probability of more than a δ-fraction of unstable candidates is at most p₀/δ. -/
theorem unstableFraction_tail_le (p : FiniteEntropy.Law Ω)
    (I : Finset ι) (E : ι → Ω → Prop) {p₀ δ : ℝ}
    (hδ : 0 < δ) (hp₀ : 0 ≤ p₀) (hE : ∀ i ∈ I, p.event (E i) ≤ p₀) :
    p.event (fun ω => δ < unstableFraction I E ω) ≤ p₀ / δ := by
  calc
    p.event (fun ω => δ < unstableFraction I E ω) ≤
        p.finiteMean (unstableFraction I E) / δ := by
      simpa only [mean_unstableFraction] using p.unstableFraction_tail_average I E hδ
    _ ≤ p₀ / δ := div_le_div_of_nonneg_right (p.mean_unstableFraction_le I E hp₀ hE)
      (le_of_lt hδ)

end FiniteEntropy.Law
