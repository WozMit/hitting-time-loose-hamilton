module

public import HittingTimeLooseHamilton.BiasedMatchingCollision
public import HittingTimeLooseHamilton.BiasedMatchingCoarseEntropy

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy

/-- The common padded deficit averaged over the actual role distribution. -/
@[expose] def averageKahnPaddedDeficit {R : Type*} [Fintype R] {n r : ℕ}
    (ν : Law R) (H : R → Kahn.Hypergraph n r)
    (μ : (i : R) → Law (Kahn.MatchingIn (H i))) (D : ℝ) : ℝ :=
  ∑ i, ν.mass i * ((n:ℝ)*Real.log D - Kahn.MatchingLaw.marginalEntropySum (μ i))

lemma averageKahnPaddedDeficit_eq {R : Type*} [Fintype R] {n r : ℕ}
    (ν : Law R) (H : R → Kahn.Hypergraph n r)
    (μ : (i : R) → Law (Kahn.MatchingIn (H i))) (D : ℝ) :
    averageKahnPaddedDeficit ν H μ D = (n:ℝ)*Real.log D -
      ∑ i, ν.mass i*Kahn.MatchingLaw.marginalEntropySum (μ i) := by
  simp only [averageKahnPaddedDeficit, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ν.total, one_mul]

/-- Coarse deficit control needs only the average matching entropy. -/
lemma average_kahn_padded_deficit_coarse {R : Type*} [Fintype R] {n r : ℕ}
    (ν : Law R) (H : R → Kahn.Hypergraph n r)
    (μ : (i : R) → Law (Kahn.MatchingIn (H i)))
    (hr : 2 ≤ r) {C₁ C₂ D : ℝ} (hC₁ : 0 ≤ C₁)
    (hK : ∀ i, entropy (μ i).mass <
      (1/(r:ℝ))*Kahn.MatchingLaw.marginalEntropySum (μ i) - Kahn.correction n r +
        C₁*Kahn.MatchingLaw.errorSum (μ i) + C₂*Real.log n) :
    averageKahnPaddedDeficit ν H μ D ≤
      (n:ℝ)*Real.log D - (r:ℝ)*(∑ i, ν.mass i*entropy (μ i).mass) -
        (r:ℝ)*Kahn.correction n r + (r:ℝ)*C₁*n + (r:ℝ)*C₂*Real.log n := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset R)) =>
    mul_le_mul_of_nonneg_left (kahn_padded_deficit_coarse (μ i) hr (D := D) hC₁ (hK i)).le (ν.nonneg i))
  change averageKahnPaddedDeficit ν H μ D ≤ _ at h
  have heq : (∑ i, ν.mass i *
      ((n:ℝ)*Real.log D - (r:ℝ)*entropy (μ i).mass - (r:ℝ)*Kahn.correction n r +
        (r:ℝ)*C₁*n + (r:ℝ)*C₂*Real.log n)) =
      (n:ℝ)*Real.log D - (r:ℝ)*(∑ i, ν.mass i*entropy (μ i).mass) -
        (r:ℝ)*Kahn.correction n r + (r:ℝ)*C₁*n + (r:ℝ)*C₂*Real.log n := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp_rw [mul_left_comm (ν.mass _) (r:ℝ)]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, ν.total, one_mul]
  rwa [heq] at h

/-- Averaged equation (collision), with no entropy lower bound on individual
role configurations. Only the averaged padded deficit appears. -/
lemma average_kahn_collision_bound {R : Type*} [Fintype R] {n r D : ℕ}
    (ν : Law R) (H : R → Kahn.Hypergraph n r)
    (μ : (i : R) → Law (Kahn.MatchingIn (H i)))
    (hn : 0 < n) (hDpos : 0 < D) (hr : 2 ≤ r)
    (hD : ∀ i v, Fintype.card (KahnIncident (H i) v) ≤ D)
    (κ : ℕ)
    (hκ : ∀ i (q : Finset (Fin n)), q.card = 2 → ((H i).edges.filter (q ⊆ ·)).card ≤ κ)
    (hζ : 0 < (r.choose 2 : ℝ)*κ/D) (hζ1 : (r.choose 2 : ℝ)*κ/D < 1) :
    (∑ i, ν.mass i*Kahn.MatchingLaw.errorSum (μ i)) ≤
      (n:ℝ)*((r.choose 2 : ℝ)*κ/D)^(1/(2*((r:ℝ)-1))) +
      2*(averageKahnPaddedDeficit ν H μ D + (n:ℝ)*Real.log 2) /
        Real.log (1/((r.choose 2 : ℝ)*κ/D)) := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset R)) =>
    mul_le_mul_of_nonneg_left
      (kahn_matching_collision_bound (H i) (μ i) hn hDpos hr (hD i) κ (hκ i) hζ hζ1)
      (ν.nonneg i))
  have heq : (∑ i, ν.mass i *
      ((n:ℝ)*((r.choose 2 : ℝ)*κ/D)^(1/(2*((r:ℝ)-1))) +
      2*((n:ℝ)*Real.log D - Kahn.MatchingLaw.marginalEntropySum (μ i) +
        (n:ℝ)*Real.log 2) / Real.log (1/((r.choose 2 : ℝ)*κ/D)))) =
      (n:ℝ)*((r.choose 2 : ℝ)*κ/D)^(1/(2*((r:ℝ)-1))) +
      2*(averageKahnPaddedDeficit ν H μ D + (n:ℝ)*Real.log 2) /
        Real.log (1/((r.choose 2 : ℝ)*κ/D)) := by
    let z := (r.choose 2 : ℝ)*κ/D
    let t := (n:ℝ)*z^(1/(2*((r:ℝ)-1)))
    let l := Real.log (1/z)
    change (∑ i, ν.mass i*(t + 2*((n:ℝ)*Real.log D -
      Kahn.MatchingLaw.marginalEntropySum (μ i)+(n:ℝ)*Real.log 2)/l)) =
      t + 2*(averageKahnPaddedDeficit ν H μ D+(n:ℝ)*Real.log 2)/l
    have hpt (i : R) : ν.mass i*(t + 2*((n:ℝ)*Real.log D -
        Kahn.MatchingLaw.marginalEntropySum (μ i)+(n:ℝ)*Real.log 2)/l) =
        ν.mass i*(t+2*((n:ℝ)*Real.log 2)/l) +
        (2/l)*(ν.mass i*((n:ℝ)*Real.log D-Kahn.MatchingLaw.marginalEntropySum (μ i))) := by ring
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ν.total, one_mul, ← Finset.mul_sum]
    change t + 2*((n:ℝ)*Real.log 2)/l + (2/l)*averageKahnPaddedDeficit ν H μ D = _
    ring
  rwa [heq] at h

end LooseHamilton
