module

public import HittingTimeLooseHamilton.BiasedMatchingCollisionBound
public import HittingTimeLooseHamilton.KahnMain

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy

/-- The trivial Kahn error bound suffices for the first, coarse entropy estimate. -/
lemma kahn_errorSum_le_vertices {n r : ℕ} {H : Kahn.Hypergraph n r}
    (μ : Law (Kahn.MatchingIn H)) (hr : 2 ≤ r) :
    Kahn.MatchingLaw.errorSum μ ≤ n := by
  classical
  have ha : 0 ≤ 1/((r:ℝ)-1) := by
    have : (2:ℝ) ≤ r := by exact_mod_cast hr
    exact div_nonneg zero_le_one (by linarith)
  have hv (v : Fin n) :
      (∑ Y ∈ Kahn.MatchingLaw.candidates (r := r) v,
        (Kahn.MatchingLaw.marginal μ v).mass Y *
          (Kahn.MatchingLaw.gamma μ v Y)^(1/((r:ℝ)-1))) ≤ 1 := by
    conv_rhs => rw [← Kahn.MatchingLaw.candidates_mass_total μ v]
    apply Finset.sum_le_sum
    intro Y hY
    have hp : (Kahn.MatchingLaw.gamma μ v Y)^(1/((r:ℝ)-1)) ≤ 1 := by
      simpa using Real.rpow_le_rpow (Kahn.MatchingLaw.gamma_nonneg μ v Y)
        (Kahn.MatchingLaw.gamma_le_one μ v Y) ha
    exact (mul_le_mul_of_nonneg_left hp ((Kahn.MatchingLaw.marginal μ v).nonneg Y)).trans_eq
      (mul_one _)
  have h := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (Fin n))) => hv v)
  simpa [Kahn.MatchingLaw.errorSum] using h

/-- Coarse Kahn entropy control, retaining its negative correction. -/
lemma kahn_coarse_entropy_of_bound {n r : ℕ} {H : Kahn.Hypergraph n r}
    (μ : Law (Kahn.MatchingIn H)) (hr : 2 ≤ r) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁)
    (hK : entropy μ.mass < (1/(r:ℝ))*Kahn.MatchingLaw.marginalEntropySum μ -
      Kahn.correction n r + C₁*Kahn.MatchingLaw.errorSum μ + C₂*Real.log n) :
    entropy μ.mass < (1/(r:ℝ))*Kahn.MatchingLaw.marginalEntropySum μ -
      Kahn.correction n r + C₁*n + C₂*Real.log n := by
  have h := mul_le_mul_of_nonneg_left (kahn_errorSum_le_vertices μ hr) hC₁
  linarith

/-- Exact coarse bound on the padded entropy deficit; averaging this inequality
requires only an averaged matching entropy lower bound. -/
lemma kahn_padded_deficit_coarse {n r : ℕ} {H : Kahn.Hypergraph n r}
    (μ : Law (Kahn.MatchingIn H)) (hr : 2 ≤ r) {C₁ C₂ D : ℝ} (hC₁ : 0 ≤ C₁)
    (hK : entropy μ.mass < (1/(r:ℝ))*Kahn.MatchingLaw.marginalEntropySum μ -
      Kahn.correction n r + C₁*Kahn.MatchingLaw.errorSum μ + C₂*Real.log n) :
    (n:ℝ)*Real.log D - Kahn.MatchingLaw.marginalEntropySum μ <
      (n:ℝ)*Real.log D - (r:ℝ)*entropy μ.mass - (r:ℝ)*Kahn.correction n r +
        (r:ℝ)*C₁*n + (r:ℝ)*C₂*Real.log n := by
  have h := kahn_coarse_entropy_of_bound μ hr hC₁ hK
  have hrpos : 0 < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hh := mul_lt_mul_of_pos_left h hrpos
  have heq : (r:ℝ)*((1/(r:ℝ))*Kahn.MatchingLaw.marginalEntropySum μ) =
      Kahn.MatchingLaw.marginalEntropySum μ := by field_simp
  rw [mul_add, mul_add, mul_sub, heq] at hh
  linarith

/-- A coarse version of Kahn's actual theorem, with constants uniform in the
host and its arbitrary matching law. -/
theorem kahn_coarse_entropy (r : ℕ) (hr : 3 ≤ r) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → r ∣ n → ∀ (H : Kahn.Hypergraph n r)
      (μ : Law (Kahn.MatchingIn H)),
      entropy μ.mass < (1/(r:ℝ))*Kahn.MatchingLaw.marginalEntropySum μ -
        Kahn.correction n r + C₁*n + C₂*Real.log n := by
  obtain ⟨C₁,C₂,hC₁,hC₂,N,hN⟩ := Kahn.theorem42 r hr
  refine ⟨C₁,C₂,hC₁,hC₂,N,?_⟩
  intro n hn hdiv H μ
  exact kahn_coarse_entropy_of_bound μ (by omega) hC₁.le (hN n hn hdiv H μ)

end LooseHamilton
