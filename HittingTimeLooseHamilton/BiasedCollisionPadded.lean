module

public import HittingTimeLooseHamilton.BiasedCollisionMoment

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy

/-- The normalized law on padded incidence positions. Every vertex carries its
own probability law on the same finite set of slots. -/
@[expose] def paddedIncidenceLaw {U A : Type*} [Fintype U] [Fintype A] [Nonempty U]
    (p : U → Law A) : Law (U × A) := (uniform : Law U).kernel p

lemma paddedIncidence_entropy_deficit {U A : Type*}
    [Fintype U] [Fintype A] [Nonempty U] [Nonempty A] (p : U → Law A) :
    (Fintype.card U : ℝ) * finiteRelativeEntropy (paddedIncidenceLaw p) uniform =
      (Fintype.card U : ℝ) * Real.log (Fintype.card A) - ∑ u, entropy (p u).mass := by
  have hv : (Fintype.card U : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hD : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [finiteRelativeEntropy_uniform]
  have hk := entropy_kernel (uniform : Law U) p
  change entropy (paddedIncidenceLaw p).mass = _ at hk
  rw [hk, entropy_uniform, Fintype.card_prod, Nat.cast_mul, Real.log_mul hv hD]
  simp only [uniform, ← Finset.mul_sum]
  field_simp
  ring

lemma paddedIncidence_moment {U A : Type*}
    [Fintype U] [Fintype A] [Nonempty U] (p : U → Law A) (f : U × A → ℝ) :
    (Fintype.card U : ℝ) * (∑ z, (paddedIncidenceLaw p).mass z * f z) =
      ∑ u, ∑ a, (p u).mass a * f (u,a) := by
  have hv : (Fintype.card U : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [paddedIncidenceLaw, Law.kernel, uniform, Fintype.sum_prod_type,
    mul_assoc, ← Finset.mul_sum]
  rw [← mul_assoc, mul_inv_cancel₀ hv, one_mul]

/-- The paper's collision inequality for a padded family of local marginal laws.
The combinatorial sum bound is a separate hypothesis, keeping this entropy
argument independent of the matching or clone representation. -/
lemma padded_collision_bound {U A : Type*}
    [Fintype U] [Fintype A] [Nonempty U] [Nonempty A]
    (p : U → Law A) (γ : U × A → ℝ)
    (hγ : ∀ z, 0 ≤ γ z) (hγ1 : ∀ z, γ z ≤ 1)
    {ζ α : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) (hα : 0 ≤ α)
    (hmean : (∑ z, γ z) ≤
      (Fintype.card U : ℝ) * (Fintype.card A : ℝ) * ζ) :
    (∑ u, ∑ a, (p u).mass a * (γ (u,a))^α) ≤
      (Fintype.card U : ℝ) * ζ^(α/2) +
      2*((Fintype.card U : ℝ)*Real.log (Fintype.card A) -
        (∑ u, entropy (p u).mass) + (Fintype.card U : ℝ)*Real.log 2) /
        Real.log (1/ζ) := by
  have hv : 0 < (Fintype.card U : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hD : 0 < (Fintype.card A : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hq : ∀ z : U × A, 0 < (uniform : Law (U × A)).mass z := by
    intro z
    exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  have hm : (∑ z, (uniform : Law (U × A)).mass z * γ z) ≤ ζ := by
    simp only [uniform, ← Finset.mul_sum, Fintype.card_prod, Nat.cast_mul]
    calc
      ((Fintype.card U : ℝ) * (Fintype.card A : ℝ))⁻¹ * ∑ z, γ z ≤
          ((Fintype.card U : ℝ) * (Fintype.card A : ℝ))⁻¹ *
            ((Fintype.card U : ℝ) * (Fintype.card A : ℝ) * ζ) :=
        mul_le_mul_of_nonneg_left hmean (inv_nonneg.mpr (mul_nonneg hv.le hD.le))
      _ = ζ := by rw [← mul_assoc, inv_mul_cancel₀ (mul_pos hv hD).ne', one_mul]
  have h := biased_collision_moment_scaled (paddedIncidenceLaw p) uniform hq
    γ hγ hγ1 hζ hζ1 hα hv.le hm
  rw [paddedIncidence_moment, paddedIncidence_entropy_deficit] at h
  exact h

end LooseHamilton
