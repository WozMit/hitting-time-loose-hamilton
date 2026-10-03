module

public import HittingTimeLooseHamilton.TerminalFeasibilityFinite
public import HittingTimeLooseHamilton.TerminalFeasibilityScales

public section

/-! # Equation (eq:beta), Section 4

For fixed uniformity and a fixed bound on the degree offsets, every sufficiently
large admissible uniform M-edge hypergraph satisfies all terminal degree lower
bounds with probability at least exp(-N^(1/10)). The cutoff is uniform in M,
ell, the vertex type, and any marked matching. The stronger statement below
needs no nonemptiness assumption on the degree-constrained family.
-/
noncomputable section
namespace LooseHamilton
open Filter

/-- Exact asymptotic quantifiers of the terminal-feasibility bound.
The size condition only makes the unconditioned uniform M-edge model meaningful. -/
@[expose] def TerminalFeasibilityBound : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ B : ℝ, 0 ≤ B → ∃ N₀ : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V], N₀ ≤ Fintype.card V →
      ∀ (M : ℕ) (ell : V → ℕ), M ≤ (completeEdges V r).card →
        |meanDegree (V:=V) r M - Real.log (Fintype.card V:ℝ)| ≤
          3*Real.log (Real.log (Fintype.card V:ℝ)) →
        (∀ v, |(ell v:ℝ) - lowerDegreeBase V| ≤ B) →
        Real.exp (-(Fintype.card V:ℝ)^(1/10:ℝ)) ≤
          terminalFeasibilityProbability r M ell

/-- The terminal-feasibility estimate (eq:beta), with no probability estimate assumed. -/
theorem terminal_feasibility_probability : TerminalFeasibilityBound := by
  intro r hr B _hB
  have hev := (eventually_feasibility_parameters B).and
    ((eventually_feasibility_scales (by omega : 1 ≤ r)).and (eventually_ge_atTop r))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hev
  refine ⟨N₀,?_⟩
  intro V _ _ hn M ell hM hd ho
  obtain ⟨⟨hl,hμ,hell⟩,⟨hn1,hu,hscale⟩,hrn⟩ := hN₀ (Fintype.card V) hn
  have hm := hμ (meanDegree (V:=V) r M) hd
  have hthreshold (v : V) : (ell v:ℝ) ≤ (11/1000:ℝ)*Real.log (Fintype.card V:ℝ) :=
    hell (ell v) (ho v)
  exact (hscale M hl hm).trans
    (terminal_feasibility_finite r M ell (by omega) hrn hM hm hthreshold hu)

/-- The manuscript's existing conditioned-core setup is an immediate specialization. -/
theorem terminal_feasibility_core (r : ℕ) (hr : 3 ≤ r) (B : ℝ) (hB : 0 ≤ B) :
    ∃ N₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N₀ ≤ Fintype.card V →
      ∀ (M : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
        CoreAdmissible r M ell markers B →
        Real.exp (-(Fintype.card V:ℝ)^(1/10:ℝ)) ≤
          terminalFeasibilityProbability r M ell := by
  obtain ⟨N₀,hN₀⟩ := terminal_feasibility_probability r hr B hB
  refine ⟨N₀,?_⟩
  intro V _ _ hn M ell markers hadm
  obtain ⟨F⟩ := hadm.feasible
  exact hN₀ V hn M ell (terminal_size_le F) hadm.density_window hadm.offsets
end LooseHamilton
