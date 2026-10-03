module

public import HittingTimeLooseHamilton.BiasedMatchingCollisionBound
public import HittingTimeLooseHamilton.BiasedCollisionCounting

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy

/-- Equation (collision) for an actual matching law on an actual host, with
only degree and pair-degree bounds as inputs. The finite nondegenerate range
`0 < ζ < 1` is precisely the range in which the logarithmic estimate is used. -/
theorem kahn_matching_collision_bound {n r D : ℕ}
    (H : Kahn.Hypergraph n r) (μ : Law (Kahn.MatchingIn H))
    (hn : 0 < n) (hDpos : 0 < D) (hr : 2 ≤ r)
    (hD : ∀ v, Fintype.card (KahnIncident H v) ≤ D)
    (κ : ℕ)
    (hκ : ∀ q : Finset (Fin n), q.card = 2 → (H.edges.filter (q ⊆ ·)).card ≤ κ)
    (hζ : 0 < (r.choose 2 : ℝ)*κ/D) (hζ1 : (r.choose 2 : ℝ)*κ/D < 1) :
    Kahn.MatchingLaw.errorSum μ ≤
      (n:ℝ)*((r.choose 2 : ℝ)*κ/D)^(1/(2*((r:ℝ)-1))) +
      2*((n:ℝ)*Real.log D - Kahn.MatchingLaw.marginalEntropySum μ +
        (n:ℝ)*Real.log 2) / Real.log (1/((r.choose 2 : ℝ)*κ/D)) := by
  apply kahn_collision_bound_of_incidence_sum H μ hn hDpos hr hD hζ hζ1
  have h := kahn_gamma_incidence_sum_le H μ κ hκ
  have hDne : (D:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hDpos.ne'
  have heq : (n:ℝ)*D*((r.choose 2 : ℝ)*κ/D) = (n:ℝ)*(r.choose 2)*κ := by
    field_simp
    <;> ring
  rw [heq]
  exact h

end LooseHamilton
