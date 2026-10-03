module

public import HittingTimeLooseHamilton.KahnMatching
public import HittingTimeLooseHamilton.KahnLaw
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

/-!
# Specification of Kahn's Theorem 4.2

Source: Jeff Kahn, *Asymptotics for Shamir's Problem*, arXiv:1909.06834v1,
Theorem 4.2, equation (28). Natural logarithms, fixed `r ≥ 3`.

`Theorem42` below specifies the statement proved by `Kahn.theorem42`
in `Kahn/Main.lean`. The constants are quantified before `n`, the hypergraph,
and the probability law. No uniform-distribution hypothesis is imposed.
-/
open scoped BigOperators
noncomputable section
namespace Kahn

/-- A finite simple `r`-uniform hypergraph on `Fin n`. -/
structure Hypergraph (n r : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ B ∈ edges, B.card = r

/-- Perfect matchings whose every edge belongs to the specified hypergraph. -/
@[expose] def MatchingIn {n r : ℕ} (H : Hypergraph n r) :=
  {M : PerfectMatching n r // M.val ⊆ H.edges}

@[expose] noncomputable instance {n r : ℕ} (H : Hypergraph n r) : Fintype (MatchingIn H) := by
  classical
  unfold MatchingIn
  infer_instance

namespace MatchingLaw
variable {n r : ℕ} {H : Hypergraph n r}

/-- The distribution of Kahn's `f(v) = f_v \ {v}`. -/
@[expose] noncomputable def marginal (μ : FiniteEntropy.Law (MatchingIn H)) (v : Fin n) :
    FiniteEntropy.Law (Finset (Fin n)) :=
  μ.map (fun M => M.val.companion v)

/-- The unconditional bad-event probability `γ_v(Y)` of equation (27). -/
@[expose] noncomputable def gamma (μ : FiniteEntropy.Law (MatchingIn H)) (v : Fin n)
    (Y : Finset (Fin n)) : ℝ :=
  μ.event (fun M => M.val.Bad v Y)

/-- Exactly the `(r-1)`-sets `Y` not containing the distinguished vertex. -/
@[expose] noncomputable def candidates (v : Fin n) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter (fun Y => Y.card = r - 1 ∧ v ∉ Y)

/-- The error sum in equation (28); the exponent is a real reciprocal. -/
@[expose] noncomputable def errorSum (μ : FiniteEntropy.Law (MatchingIn H)) : ℝ :=
  ∑ v : Fin n, ∑ Y ∈ candidates (r := r) v,
    (marginal μ v).mass Y * Real.rpow (gamma μ v Y) (1 / ((r : ℝ) - 1))

@[expose] noncomputable def marginalEntropySum (μ : FiniteEntropy.Law (MatchingIn H)) : ℝ :=
  ∑ v : Fin n, FiniteEntropy.entropy (marginal μ v).mass

lemma gamma_nonneg (μ : FiniteEntropy.Law (MatchingIn H)) (v : Fin n)
    (Y : Finset (Fin n)) : 0 ≤ gamma μ v Y := μ.event_nonneg _

lemma gamma_le_one (μ : FiniteEntropy.Law (MatchingIn H)) (v : Fin n)
    (Y : Finset (Fin n)) : gamma μ v Y ≤ 1 := μ.event_le_one _

lemma marginal_le_gamma (μ : FiniteEntropy.Law (MatchingIn H)) (hr : 2 ≤ r)
    (v : Fin n) (Y : Finset (Fin n)) : (marginal μ v).mass Y ≤ gamma μ v Y := by
  apply μ.event_mono
  intro M hM
  exact M.val.bad_of_companion_eq hr v Y hM

lemma marginal_zero_outside (μ : FiniteEntropy.Law (MatchingIn H))
    (v : Fin n) (Y : Finset (Fin n))
    (hY : Y.card ≠ r - 1 ∨ v ∈ Y) : (marginal μ v).mass Y = 0 := by
  apply μ.event_eq_zero_of_false
  intro M hM
  change M.val.companion v = Y at hM
  rcases hY with hcard | hv
  · apply hcard
    rw [← hM]
    exact M.val.companion_card v
  · apply M.val.not_mem_companion v
    rwa [hM]

/-- Summing the marginal over precisely the paper's candidate sets gives one. -/
lemma candidates_mass_total (μ : FiniteEntropy.Law (MatchingIn H)) (v : Fin n) :
    (∑ Y ∈ candidates (r := r) v, (marginal μ v).mass Y) = 1 := by
  classical
  rw [← (marginal μ v).total]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro Y _ hY
  apply marginal_zero_outside μ v Y
  by_cases hc : Y.card = r - 1
  · right
    by_contra hv
    exact hY (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hv⟩)
  · exact Or.inl hc

lemma errorSum_nonneg (μ : FiniteEntropy.Law (MatchingIn H)) : 0 ≤ errorSum μ := by
  classical
  apply Finset.sum_nonneg
  intro v _
  apply Finset.sum_nonneg
  intro Y _
  exact mul_nonneg ((marginal μ v).nonneg Y) (Real.rpow_nonneg (gamma_nonneg μ v Y) _)

end MatchingLaw

/-- The quantity `Λ` in equation (7). All arithmetic here is real arithmetic. -/
@[expose] def correction (n r : ℕ) : ℝ := ((r : ℝ) - 1) * n / r

/-- The exact uniform asymptotic upper-bound interpretation of equation (28).

The paper fixes `r ≥ 3` and takes sufficiently large `n` divisible by `r`.
The positive constants and the threshold may depend on `r` only. Strict `<`
is retained, as printed. The proof is `Kahn.theorem42` in `Kahn/Main.lean`.
-/
@[expose] def Theorem42 : Prop :=
  ∀ r : ℕ, 3 ≤ r →
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → r ∣ n →
      ∀ (H : Hypergraph n r) (μ : FiniteEntropy.Law (MatchingIn H)),
        FiniteEntropy.entropy μ.mass <
          (1 / (r : ℝ)) * MatchingLaw.marginalEntropySum μ - correction n r +
          C₁ * MatchingLaw.errorSum μ + C₂ * Real.log (n : ℝ)

end Kahn
