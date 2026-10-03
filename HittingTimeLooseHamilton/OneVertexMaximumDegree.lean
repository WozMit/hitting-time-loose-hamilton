module

public import HittingTimeLooseHamilton.OneVertexPoisson
public import HittingTimeLooseHamilton.PoissonTailParameters

public section

/-! The maximum-degree consequence stated immediately after Lemma 4.1.
The constant is independent of the bounded degree offsets; the sufficiently
large vertex-count threshold may depend on their fixed bound. -/
noncomputable section
namespace LooseHamilton
open Filter

/-- An explicit, uniform version of the maximum-degree consequence. -/
theorem core_maximum_degree_tail_eventually (A B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] [DecidableEq V],
      Fintype.card V = n → ∀ (r M : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
      ∀ hadm : CoreAdmissible r M ell markers B,
      letI : Nonempty (TerminalState V r M ell) := hadm.feasible
      (terminalLaw r M ell).event (fun F => ∃ v,
        poissonMaximumConstant A * Real.log (n : ℝ) < (vertexDegree F.val v : ℝ)) ≤
        Real.rpow (n : ℝ) (-A) := by
  filter_upwards [eventually_core_poisson_parameters B] with n hn
  intro V _ _ hcard r M ell markers hadm
  letI : Nonempty (TerminalState V r M ell) := hadm.feasible
  obtain ⟨hlog,hmean,hthreshold⟩ := hn V hcard r M ell markers hadm
  have ht := maximum_tail_of_poisson_domination
    (terminalLaw r M ell) (fun F v => vertexDegree F.val v)
    (degreeThreshold r M ell) (meanDegree (V := V) r M) A
    (meanDegree_nonneg r M) hlog hmean hthreshold
    (fun v k => one_vertex_poisson_domination v k)
  simpa only [hcard] using ht

/-- The stated polynomial tail: for every fixed exponent and uniformity,
there is a logarithmic degree constant, uniform in the bounded lower-degree
offsets and in all admissible terminal cores of sufficiently large order. -/
theorem lemma41_maximum_degree (r : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ,
      ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] [DecidableEq V],
        Fintype.card V = n → ∀ (M : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
        ∀ hadm : CoreAdmissible r M ell markers B,
        letI : Nonempty (TerminalState V r M ell) := hadm.feasible
        (terminalLaw r M ell).event (fun F => ∃ v,
          C * Real.log (n : ℝ) < (vertexDegree F.val v : ℝ)) ≤
          Real.rpow (n : ℝ) (-A) := by
  refine ⟨poissonMaximumConstant A, ?_, ?_⟩
  · unfold poissonMaximumConstant
    positivity
  · intro B
    filter_upwards [core_maximum_degree_tail_eventually A B] with n hn
    intro V _ _ hcard M ell markers hadm
    exact hn V hcard r M ell markers hadm

end LooseHamilton
