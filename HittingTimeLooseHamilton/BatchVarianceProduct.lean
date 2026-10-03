module

public import HittingTimeLooseHamilton.HypergeometricAvoidanceLower

public section

noncomputable section
open scoped BigOperators
namespace LooseHamilton

/-- Exact falling-factorial expression for the normalized joint avoidance ratio. -/
lemma batch_joint_choose_eq_product (m k τ I : ℕ)
    (hk4 : 4*k ≤ m) (ht4 : 4*τ ≤ m) :
    ((m-2*k+I).choose τ : ℝ)*(m.choose τ : ℝ)/((m-k).choose τ : ℝ)^2 =
      ∏ i ∈ Finset.range τ,
        (((m:ℝ)-2*k+I-i)*((m:ℝ)-i))/((m:ℝ)-k-i)^2 := by
  calc
    _ = (((m-2*k+I).choose τ : ℝ)/((m-k).choose τ : ℝ)) *
        ((m.choose τ : ℝ)/((m-k).choose τ : ℝ)) := by ring
    _ = (∏ i ∈ Finset.range τ, ((m-2*k+I-i:ℕ):ℝ)/((m-k-i:ℕ):ℝ)) *
        (∏ i ∈ Finset.range τ, ((m-i:ℕ):ℝ)/((m-k-i:ℕ):ℝ)) := by
      rw [Hypergeometric.choose_ratio_eq_prod, Hypergeometric.choose_ratio_eq_prod]
    _ = _ := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have h1 : ((m-2*k+I-i:ℕ):ℝ) = (m:ℝ)-2*k+I-i := by
        rw [Nat.cast_sub (by omega : i ≤ m-2*k+I), Nat.cast_add,
          Nat.cast_sub (by omega : 2*k ≤ m), Nat.cast_mul, Nat.cast_ofNat]
      have h2 : ((m-i:ℕ):ℝ) = (m:ℝ)-i := Nat.cast_sub (by omega)
      have h3 : ((m-k-i:ℕ):ℝ) = (m:ℝ)-k-i := by
        rw [Nat.cast_sub (by omega : i ≤ m-k), Nat.cast_sub (by omega : k ≤ m)]
      rw [h1,h2,h3, div_mul_div_comm, pow_two]

end LooseHamilton
