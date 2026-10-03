module

public import HittingTimeLooseHamilton.BiasedCloneAverage
public import HittingTimeLooseHamilton.ForwardReverseKernel

public section

noncomputable section
open scoped BigOperators
namespace FiniteEntropy

/-- Averaging over a role law cannot increase the L1 distance between two
families of coordinates. -/
theorem role_average_l1_le {R I : Type*} [Fintype R] [Fintype I]
    (nu : Law R) (f g : R → I → ℝ) :
    (∑ i, |(∑ a, nu.mass a * f a i) - (∑ a, nu.mass a * g a i)|) ≤
      ∑ a, nu.mass a * (∑ i, |f a i - g a i|) := by
  have hpoint (i : I) : |(∑ a, nu.mass a * f a i) - (∑ a, nu.mass a * g a i)| ≤
      ∑ a, nu.mass a * |f a i - g a i| := by
    calc
      _ = |∑ a, nu.mass a * (f a i - g a i)| := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
      _ ≤ ∑ a, |nu.mass a * (f a i - g a i)| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp_rw [abs_mul, abs_of_nonneg (nu.nonneg _)]
  calc
    _ ≤ ∑ i, ∑ a, nu.mass a * |f a i - g a i| := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = _ := by rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]

/-- Probability form of the role-averaging estimate for a finite conditional
kernel. The reference event depends only on the source role. -/
theorem kernel_role_average_l1_le {R B I : Type*} [Fintype R] [Fintype B] [Fintype I]
    (nu : Law R) (k : R → Law B)
    (W : I → R × B → Prop) (A : I → R → Prop)
    [∀ i a, Decidable (A i a)] (lam : ℝ) :
    (∑ i, |(nu.kernel k).event (W i) - nu.event (A i) / lam|) ≤
      ∑ a, nu.mass a * (∑ i,
        |(k a).event (fun b => W i (a, b)) - (if A i a then 1 / lam else 0)|) := by
  classical
  have href (i : I) : (∑ a, nu.mass a * (if A i a then 1 / lam else 0)) =
      nu.event (A i) / lam := by
    unfold Law.event
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp [div_eq_mul_inv]
  simpa only [href, ← LooseHamilton.forward_kernel_event] using
    role_average_l1_le nu (fun a i => (k a).event (fun b => W i (a, b)))
      (fun a i => if A i a then 1 / lam else 0)

/-- Projection is a triangle inequality: a clone-to-role error plus the role
marginal error from its deterministic target. -/
theorem projection_l1_triangle {I : Type*} [Fintype I]
    (p role : I → ℝ) (c lam : ℝ) (hlam : 0 < lam) :
    (∑ i, |p i - c / lam|) ≤
      (∑ i, |p i - role i / lam|) + (∑ i, |role i - c|) / lam := by
  calc
    _ ≤ ∑ i, (|p i - role i / lam| + |role i / lam - c / lam|) :=
      Finset.sum_le_sum (fun i _ => abs_sub_le _ _ _)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp_rw [← sub_div, abs_div, abs_of_pos hlam]
      rw [Finset.sum_div]

end FiniteEntropy
