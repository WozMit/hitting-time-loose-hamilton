module

public import HittingTimeLooseHamilton.OneVertexStatement
public import Mathlib.Tactic

public section

/-! Factorial-moment upper tails for the Poisson comparison. -/
noncomputable section
namespace LooseHamilton

/-- A Poisson tail is at most its kth factorial moment divided by k!. -/
theorem poisson_tail_factorial (μ : NNReal) (k : ℕ) :
    1 - ∑ j ∈ Finset.range k, ProbabilityTheory.poissonPMFReal μ j ≤
      (μ : ℝ)^k / (k.factorial : ℝ) := by
  rw [poisson_upper_tail_eq_tsum]
  have hs := ProbabilityTheory.poissonPMFRealSum μ
  have hshift := hs.summable.comp_injective (fun a b h => Nat.add_right_cancel h :
    Function.Injective (fun a : ℕ => a+k))
  have hpoint (j : ℕ) : ProbabilityTheory.poissonPMFReal μ (j+k) ≤
      ((μ : ℝ)^k / (k.factorial : ℝ)) * ProbabilityTheory.poissonPMFReal μ j := by
    have hfac : (j.factorial : ℝ) * k.factorial ≤ (j+k).factorial := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (j+k))
        (Nat.factorial_mul_factorial_dvd_factorial_add j k)
    unfold ProbabilityTheory.poissonPMFReal
    rw [pow_add]
    have hj : (0 : ℝ) < j.factorial := by positivity
    have hk : (0 : ℝ) < k.factorial := by positivity
    have hjk : (0 : ℝ) < (j+k).factorial := by positivity
    apply (div_le_iff₀ hjk).mpr
    have hb := mul_le_mul_of_nonneg_left hfac
      (show 0 ≤ ((μ : ℝ)^k / (k.factorial : ℝ)) *
        (Real.exp (-(μ : ℝ)) * (μ : ℝ)^j / (j.factorial : ℝ)) by positivity)
    convert hb using 1 <;> (field_simp <;> ring)
  calc
    _ ≤ ∑' j, ((μ : ℝ)^k / (k.factorial : ℝ)) *
        ProbabilityTheory.poissonPMFReal μ j :=
      hshift.tsum_le_tsum hpoint (hs.summable.mul_left _)
    _ = _ := by
      simp only [ProbabilityTheory.poissonPMFReal]
      rw [tsum_mul_left,hs.tsum_eq,mul_one]

theorem PoissonDominated.factorial_tail {Ω : Type*} [Fintype Ω]
    {p : FiniteEntropy.Law Ω} {X : Ω → ℕ} {μ : NNReal}
    (h : PoissonDominated p X μ) (k : ℕ) :
    p.event (fun ω => k ≤ X ω) ≤ (μ : ℝ)^k / (k.factorial : ℝ) :=
  (h k).trans (poisson_tail_factorial μ k)
end LooseHamilton
