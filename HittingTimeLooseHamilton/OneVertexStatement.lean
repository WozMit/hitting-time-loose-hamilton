module

public import HittingTimeLooseHamilton.DegreeExcess
public import Mathlib.Probability.Distributions.Poisson.Basic

public section

/-! Exact statement of Lemma 4.1 of the supplied loose-Hamilton manuscript. -/
noncomputable section
namespace LooseHamilton
open Finset

/-- First-order stochastic domination of a natural-valued statistic by the
actual Poisson distribution: every upper tail is bounded by its Poisson tail.
The tail is one minus the finite cumulative sum of mathlib's Poisson masses. -/
@[expose] def PoissonDominated {Ω : Type*} [Fintype Ω] (p : FiniteEntropy.Law Ω)
    (X : Ω → ℕ) (μ : NNReal) : Prop :=
  ∀ k : ℕ, p.event (fun ω => k ≤ X ω) ≤
    1-∑ j ∈ range k, ProbabilityTheory.poissonPMFReal μ j

/-- The finite cumulative complement is the full Poisson upper-tail mass,
not an exponential estimate for that tail. -/
lemma poisson_upper_tail_eq_tsum (μ : NNReal) (k : ℕ) :
    1-∑ j ∈ range k, ProbabilityTheory.poissonPMFReal μ j =
      ∑' j : ℕ, ProbabilityTheory.poissonPMFReal μ (j+k) := by
  have hs := ProbabilityTheory.poissonPMFRealSum μ
  have hsplit := hs.summable.sum_add_tsum_nat_add k
  rw [hs.tsum_eq] at hsplit
  simp only [ProbabilityTheory.poissonPMFReal]
  linarith

/-- Lemma 4.1: in every nonempty uniform m-edge r-graph model with prescribed
vertex-degree lower bounds, the positive excess above max(ell_v,ceil(rm/N))
is stochastically dominated by Poisson(rm/N). No sparse-regime hypothesis
or Hamiltonicity conclusion is part of the switching lemma. -/
@[expose] def Lemma41 : Prop :=
  ∀ (N r m : ℕ), 0 < N → 3 ≤ r → ∀ ell : Fin N → ℕ,
    ∀ [Nonempty (TerminalState (Fin N) r m ell)], ∀ v : Fin N,
    PoissonDominated (terminalLaw r m ell) (fun F => degreeExcess F v)
      ⟨meanDegree (V := Fin N) r m,meanDegree_nonneg r m⟩
end LooseHamilton
