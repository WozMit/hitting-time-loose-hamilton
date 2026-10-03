module

public import HittingTimeLooseHamilton.StoppedExponentialMaximal

public section

noncomputable section
namespace LooseHamilton.StoppedExponential
open Finset
variable {Ω : Type*} [Fintype Ω]

/-- Zero quadratic budget forces every bounded increment to vanish. -/
theorem zero_variance (p : FiniteEntropy.Law Ω) (d : ℕ → Ω → ℝ) (n : ℕ)
    (b : ℕ → ℝ) (hd : ∀ i < n, ∀ ω, |d i ω| ≤ b i)
    (A : ℝ) (hA : 0 ≤ A) (hV : ∑ i ∈ range n, (b i)^2 = 0) :
    p.event (fun ω => ∃ t ≤ n, A < partialSum d t ω) = 0 := by
  classical
  have hb : ∀ i < n, b i = 0 := by
    intro i hi
    have hs : (b i)^2 ≤ ∑ j ∈ range n, (b j)^2 :=
      single_le_sum (fun j _ => sq_nonneg (b j)) (mem_range.mpr hi)
    rw [hV] at hs
    exact sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg _))
  have hz : ∀ i < n, ∀ ω, d i ω = 0 := by
    intro i hi ω
    apply abs_eq_zero.mp
    exact le_antisymm (by simpa [hb i hi] using hd i hi ω) (abs_nonneg _)
  have hf : ∀ ω, ¬ ∃ t ≤ n, A < partialSum d t ω := by
    rintro ω ⟨t,ht,hx⟩
    have hs : partialSum d t ω = 0 := by
      apply sum_eq_zero
      intro i hi
      exact hz i (lt_of_lt_of_le (mem_range.mp hi) ht) ω
    rw [hs] at hx
    exact not_lt_of_ge hA hx
  simp [FiniteEntropy.Law.event, hf]

/-- The maximal bound, including degenerate zero variance (where the event is empty). -/
theorem maximal_total (p : FiniteEntropy.Law Ω) (d : ℕ → Ω → ℝ)
    (R : ℕ → Ω → Ω → Prop) (n : ℕ) (hD : Differences p d R n)
    (b : ℕ → ℝ) (hb : ∀ i < n, 0 ≤ b i) (hd : ∀ i < n, ∀ ω, |d i ω| ≤ b i)
    (A : ℝ) (hA : 0 < A) :
    p.event (fun ω => ∃ t ≤ n, A < partialSum d t ω) ≤
      Real.exp (-A^2 / (2 * ∑ i ∈ range n, (b i)^2)) := by
  classical
  by_cases hV : ∑ i ∈ range n, (b i)^2 = 0
  · rw [zero_variance p d n b hd A hA.le hV]
    exact (Real.exp_pos _).le
  · exact maximal p d R n hD b hb hd A hA
      (lt_of_le_of_ne (sum_nonneg (fun i _ => sq_nonneg (b i))) (Ne.symm hV))

end LooseHamilton.StoppedExponential
