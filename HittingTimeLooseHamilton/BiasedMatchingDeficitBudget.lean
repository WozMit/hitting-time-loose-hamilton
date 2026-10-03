module

public import HittingTimeLooseHamilton.BiasedMatchingCollisionAverage
public import HittingTimeLooseHamilton.BiasedEntropyDeficits

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy

/-- Coarse averaged padded deficit budget from the actual entropy chain and
one lower bound for total cycle entropy. No conditional entropy lower bounds
are required. `B` is the full cycle entropy benchmark. -/
lemma kahn_role_padded_budget {R : Type*} [Fintype R] {n r : ℕ}
    (ν : Law R) (H : R → Kahn.Hypergraph n r)
    (μ : (i : R) → Law (Kahn.MatchingIn (H i))) (hr : 2 ≤ r)
    {C₁ C₂ D Htot Hrole S B loss : ℝ} (hC₁ : 0 ≤ C₁)
    (hK : ∀ i, entropy (μ i).mass <
      (1/(r:ℝ))*Kahn.MatchingLaw.marginalEntropySum (μ i) - Kahn.correction n r +
        C₁*Kahn.MatchingLaw.errorSum (μ i) + C₂*Real.log n)
    (hchain : Htot = Hrole + ∑ i, ν.mass i*entropy (μ i).mass)
    (hrole : Hrole ≤ S) (hlower : B-loss ≤ Htot) :
    averageKahnPaddedDeficit ν H μ D ≤
      (n:ℝ)*Real.log D - (r:ℝ)*(B-loss-S) - (r:ℝ)*Kahn.correction n r +
        (r:ℝ)*C₁*n + (r:ℝ)*C₂*Real.log n := by
  have h := average_kahn_padded_deficit_coarse ν H μ hr (D := D) hC₁ hK
  have hmean : B-loss-S ≤ ∑ i, ν.mass i*entropy (μ i).mass := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg r : (0:ℝ) ≤ r)
  linarith

/-- Propagate any proved averaged padded-deficit budget to the averaged
collision correction of actual random perfect matchings. -/
lemma kahn_role_collision_budget {R : Type*} [Fintype R] {n r D : ℕ}
    (ν : Law R) (H : R → Kahn.Hypergraph n r)
    (μ : (i : R) → Law (Kahn.MatchingIn (H i)))
    (hn : 0 < n) (hDpos : 0 < D) (hr : 2 ≤ r)
    (hD : ∀ i v, Fintype.card (KahnIncident (H i) v) ≤ D)
    (κ : ℕ)
    (hκ : ∀ i (q : Finset (Fin n)), q.card = 2 → ((H i).edges.filter (q ⊆ ·)).card ≤ κ)
    (hζ : 0 < (r.choose 2 : ℝ)*κ/D) (hζ1 : (r.choose 2 : ℝ)*κ/D < 1)
    {budget : ℝ} (hbudget : averageKahnPaddedDeficit ν H μ D ≤ budget) :
    (∑ i, ν.mass i*Kahn.MatchingLaw.errorSum (μ i)) ≤
      (n:ℝ)*((r.choose 2 : ℝ)*κ/D)^(1/(2*((r:ℝ)-1))) +
      2*(budget + (n:ℝ)*Real.log 2) / Real.log (1/((r.choose 2 : ℝ)*κ/D)) := by
  have h := average_kahn_collision_bound ν H μ hn hDpos hr hD κ hκ hζ hζ1
  have hl : 0 < Real.log (1/((r.choose 2 : ℝ)*κ/D)) :=
    Real.log_pos ((lt_div_iff₀ hζ).mpr (by simpa using hζ1))
  apply h.trans
  apply add_le_add_right
  apply div_le_div_of_nonneg_right _ hl.le
  nlinarith

lemma kahn_correction_eq {n r k : ℕ} (hr : 0 < r) (hn : n = r*k) :
    Kahn.correction n r = ((r:ℝ)-1)*k := by
  have hrne : (r:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  unfold Kahn.correction
  rw [hn, Nat.cast_mul]
  field_simp
  <;> ring

/-- The actual Kahn theorem and the cycle entropy chain imply the three-deficit
budget. The local and degree deficits enter through their defining identity;
positivity and host-average-degree estimates are independent inputs downstream. -/
lemma kahn_three_deficits_budget {R : Type*} [Fintype R] {n r k : ℕ}
    (ν : Law R) (H : R → Kahn.Hypergraph n r)
    (μ : (i : R) → Law (Kahn.MatchingIn (H i)))
    (hr : 2 ≤ r) (hn : n = r*k)
    (Dloc Q lam : R → ℝ) (Htot Hrole S muRef loss C₁ C₂ : ℝ)
    (hchain : Htot = Hrole + ∑ i, ν.mass i*entropy (μ i).mass)
    (hdef : ∀ i, Dloc i = (n:ℝ)*Real.log (lam i)-Q i-
      Kahn.MatchingLaw.marginalEntropySum (μ i))
    (hK : ∀ i, entropy (μ i).mass <
      (1/(r:ℝ))*Kahn.MatchingLaw.marginalEntropySum (μ i) - Kahn.correction n r +
        C₁*Kahn.MatchingLaw.errorSum (μ i) + C₂*Real.log n)
    (hlower : (k:ℝ)*Real.log (((r:ℝ)-1)*muRef)-((r:ℝ)-1)*k-loss ≤ Htot) :
    (S-Hrole) + (∑ i, ν.mass i*(Dloc i+Q i))/(r:ℝ) ≤
      S+(k:ℝ)*(∑ i, ν.mass i*Real.log (lam i))-
        (k:ℝ)*Real.log (((r:ℝ)-1)*muRef)+loss +
        C₁*(∑ i, ν.mass i*Kahn.MatchingLaw.errorSum (μ i))+C₂*Real.log n := by
  have hrpos : 0 < r := by omega
  have hrreal : 0 < (r:ℝ) := Nat.cast_pos.mpr hrpos
  have hcond (i : R) : entropy (μ i).mass ≤
      Kahn.MatchingLaw.marginalEntropySum (μ i)/(r:ℝ)-((r:ℝ)-1)*k+
        (C₁*Kahn.MatchingLaw.errorSum (μ i)+C₂*Real.log n) := by
    have hi := (hK i).le
    rw [kahn_correction_eq hrpos hn] at hi
    simpa only [one_div_mul_eq_div, add_assoc] using hi
  have h := FiniteEntropy.three_entropy_deficits ν
    (fun i => entropy (μ i).mass) (fun i => Kahn.MatchingLaw.marginalEntropySum (μ i))
    Dloc Q (fun i => C₁*Kahn.MatchingLaw.errorSum (μ i)+C₂*Real.log n) lam
    Htot Hrole S r k n muRef loss hrreal (by exact_mod_cast hn) hchain hdef hcond hlower
  have herr : (∑ i, ν.mass i*(C₁*Kahn.MatchingLaw.errorSum (μ i)+C₂*Real.log n)) =
      C₁*(∑ i, ν.mass i*Kahn.MatchingLaw.errorSum (μ i))+C₂*Real.log n := by
    simp_rw [mul_add, mul_left_comm (ν.mass _) C₁]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ν.total, one_mul]
  rw [herr] at h
  linarith

end LooseHamilton
