module

public import HittingTimeLooseHamilton.OneVertexStatement
public import HittingTimeLooseHamilton.DegreeExcessRecurrence
public import HittingTimeLooseHamilton.PoissonComparison

public section

/-! The one-vertex switching lemma, proved from actual graph counts. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r m : ℕ} {ell : V → ℕ} [Nonempty (TerminalState V r m ell)]

/-- A numerical upper-tail form of the exact one-vertex Poisson domination. -/
theorem one_vertex_poisson_domination (v : V) (k : ℕ) :
    (terminalLaw r m ell).event (fun F => k ≤ degreeExcess F v) ≤
      1-Real.exp (-meanDegree (V := V) r m)*
        ∑ j ∈ range k, (meanDegree (V := V) r m)^j/(j.factorial : ℝ) := by
  have h := finite_poisson_cdf_le
    (natLawAtom (terminalLaw r m ell) (fun F => degreeExcess F v))
    (meanDegree (V := V) r m) m k (meanDegree_nonneg r m)
    (natLawAtom_nonneg _ _) (fun q hq => natLawAtom_eq_zero _ _ m (fun F => degreeExcess_le F v) hq)
    (sum_natLawAtom_total _ _ m (fun F => degreeExcess_le F v))
    (degreeExcess_atom_recurrence v)
  rw [event_ge_eq_one_sub_atoms]
  linarith

/-- Stochastic domination expressed using mathlib's Poisson distribution. The
stronger auxiliary theorem works for every uniformity, including empty graphs
of mean zero, whenever the terminal family is nonempty. -/
theorem one_vertex_stochastic_domination (v : V) :
    PoissonDominated (terminalLaw r m ell) (fun F => degreeExcess F v)
      ⟨meanDegree (V := V) r m,meanDegree_nonneg r m⟩ := by
  intro k
  exact (one_vertex_poisson_domination v k).trans_eq
    (congrArg (fun x : ℝ => 1-x) (poisson_cdf_eq
      ⟨meanDegree (V := V) r m, meanDegree_nonneg r m⟩ k).symm)

/-- The same domination with its full infinite Poisson tail displayed. -/
theorem one_vertex_poisson_tsum (v : V) (k : ℕ) :
    (terminalLaw r m ell).event (fun F => k ≤ degreeExcess F v) ≤
      ∑' j : ℕ, ProbabilityTheory.poissonPMFReal
        ⟨meanDegree (V := V) r m,meanDegree_nonneg r m⟩ (j+k) := by
  have h := one_vertex_stochastic_domination (r := r) (m := m) (ell := ell) v k
  exact h.trans_eq (poisson_upper_tail_eq_tsum _ _)

/-- Lemma 4.1 (One-vertex switching). -/
theorem lemma41 : Lemma41 := by
  intro N r m hN hr ell _ v
  exact one_vertex_stochastic_domination v
end LooseHamilton
