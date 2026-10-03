module

public import HittingTimeLooseHamilton.BiasedCloneAverage

public section

noncomputable section
open scoped BigOperators
namespace FiniteEntropy

/-- The averaged form of the conditional Kahn entropy upper bound. -/
lemma average_conditional_entropy_bound {R : Type*} [Fintype R]
    (q : Law R) (H L err : R → ℝ) (r k : ℝ)
    (hKahn : ∀ a, H a ≤ L a / r - (r - 1) * k + err a) :
    (∑ a, q.mass a * H a) ≤
      (∑ a, q.mass a * L a) / r - (r - 1) * k + ∑ a, q.mass a * err a := by
  have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset R)) =>
    mul_le_mul_of_nonneg_left (hKahn a) (q.nonneg a))
  have heq : (∑ a, q.mass a * (L a / r - (r - 1) * k + err a)) =
      (∑ a, q.mass a * L a) / r - (r - 1) * k + ∑ a, q.mass a * err a := by
    simp_rw [mul_add, mul_sub, ← mul_div_assoc]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
      ← Finset.sum_mul, q.total, one_mul]
  rwa [heq] at h

/-- The sum of local entropy deficit and logarithmic degree deficit is exactly
the gap between the regular-degree entropy benchmark and the local entropy sum. -/
lemma average_local_degree_deficit {R : Type*} [Fintype R]
    (q : Law R) (D Q L lam : R → ℝ) (v : ℝ)
    (hD : ∀ a, D a = v * Real.log (lam a) - Q a - L a) :
    (∑ a, q.mass a * (D a + Q a)) =
      v * (∑ a, q.mass a * Real.log (lam a)) - ∑ a, q.mass a * L a := by
  simp_rw [hD]
  have heq (a : R) : q.mass a * (v * Real.log (lam a) - Q a - L a + Q a) =
      v * (q.mass a * Real.log (lam a)) - q.mass a * L a := by ring
  simp_rw [heq]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- Entropy-chain and conditional Kahn bounds control all three deficits
simultaneously. This is an algebraic consequence of the actual chain identity,
local-deficit identity, conditional entropy bounds, and total entropy lower bound. -/
theorem three_entropy_deficits {R : Type*} [Fintype R]
    (q : Law R) (Hcond L D Q err lam : R → ℝ)
    (Htot Hrole S r k v mu loss : ℝ) (hr : 0 < r)
    (hv : v = r * k)
    (hchain : Htot = Hrole + ∑ a, q.mass a * Hcond a)
    (hD : ∀ a, D a = v * Real.log (lam a) - Q a - L a)
    (hKahn : ∀ a, Hcond a ≤ L a / r - (r - 1) * k + err a)
    (hlower : k * Real.log ((r - 1) * mu) - (r - 1) * k - loss ≤ Htot) :
    (S - Hrole) + (∑ a, q.mass a * (D a + Q a)) / r ≤
      S + k * (∑ a, q.mass a * Real.log (lam a)) -
        k * Real.log ((r - 1) * mu) + loss + ∑ a, q.mass a * err a := by
  have hcond := average_conditional_entropy_bound q Hcond L err r k hKahn
  have hdef := average_local_degree_deficit q D Q L lam v hD
  rw [hv] at hdef
  have hquot : (∑ a, q.mass a * (D a + Q a)) / r =
      k * (∑ a, q.mass a * Real.log (lam a)) - (∑ a, q.mass a * L a) / r := by
    rw [hdef, sub_div]
    congr 1
    field_simp <;> ring
  rw [hquot]
  linarith

/-- If the local and role deficits are nonnegative, the factor on the local
term can be removed at a cost depending only on uniformity. -/
lemma three_deficit_absorption {r role loc rhs : ℝ} (hr : 0 < r)
    (hrole : 0 ≤ role) (hlocal : 0 ≤ loc)
    (hbound : role + loc / r ≤ rhs) :
    role + loc ≤ max 1 r * rhs := by
  have hdiv : 0 ≤ loc / r := div_nonneg hlocal hr.le
  have hrhs : 0 ≤ rhs := by linarith
  have hscaled : r * role + loc ≤ r * rhs := by
    have h := mul_le_mul_of_nonneg_left hbound hr.le
    have heq : r * (role + loc / r) = r * role + loc := by
      rw [mul_add, mul_div_cancel₀ _ hr.ne']
    rwa [heq] at h
  by_cases hsmall : r ≤ 1
  · rw [max_eq_left hsmall, one_mul]
    have hlocaldiv : loc ≤ loc / r := by
      apply (le_div_iff₀ hr).2
      nlinarith
    linarith
  · have hlarge : 1 ≤ r := le_of_not_ge hsmall
    rw [max_eq_right hlarge]
    nlinarith

end FiniteEntropy
