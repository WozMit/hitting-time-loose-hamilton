module

public import HittingTimeLooseHamilton.BiasedCollisionEntropy

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy

/-- Markov's inequality for the exceptional collision incidences. -/
lemma collision_large_event_bound {A : Type*} [Fintype A]
    (q : Law A) (γ : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) {ζ : ℝ}
    (hζ : 0 < ζ) (hmean : (∑ a, q.mass a * γ a) ≤ ζ) :
    q.event (fun a => Real.sqrt ζ < γ a) ≤ Real.sqrt ζ := by
  classical
  have hpt (a : A) :
      Real.sqrt ζ * (if Real.sqrt ζ < γ a then q.mass a else 0) ≤
        q.mass a * γ a := by
    split_ifs with ha
    · nlinarith [q.nonneg a]
    · simpa using mul_nonneg (q.nonneg a) (hγ a)
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) => hpt a)
  rw [← Finset.mul_sum] at hs
  change Real.sqrt ζ * q.event (fun a => Real.sqrt ζ < γ a) ≤ _ at hs
  have hsqrt := Real.mul_self_sqrt hζ.le
  have hp := Real.sqrt_pos.2 hζ
  nlinarith

/-- The fractional collision moment is controlled by the exceptional probability. -/
lemma collision_moment_split {A : Type*} [Fintype A]
    (p : Law A) (γ : A → ℝ) (hγ : ∀ a, 0 ≤ γ a)
    (hγ1 : ∀ a, γ a ≤ 1) {t α : ℝ} (ht : 0 ≤ t) (hα : 0 ≤ α) :
    (∑ a, p.mass a * (γ a)^α) ≤ t^α + p.event (fun a => t < γ a) := by
  classical
  have hpt (a : A) : p.mass a * (γ a)^α ≤
      p.mass a * t^α + (if t < γ a then p.mass a else 0) := by
    by_cases ha : t < γ a
    · simp only [ha, ↓reduceIte]
      have hr : (γ a)^α ≤ 1 := by
        simpa using Real.rpow_le_rpow (hγ a) (hγ1 a) hα
      have := mul_le_mul_of_nonneg_left hr (p.nonneg a)
      have := mul_nonneg (p.nonneg a) (Real.rpow_nonneg ht α)
      nlinarith
    · simp only [ha, ↓reduceIte, add_zero]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hγ a) (le_of_not_gt ha) hα) (p.nonneg a)
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) => hpt a)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, p.total, one_mul] at hs
  exact hs

/-- The normalized form of equation (collision). The reference law can be any
strictly positive finite law, so uniform padded incidence positions are included. -/
lemma biased_collision_moment {A : Type*} [Fintype A]
    (p q : Law A) (hq : ∀ a, 0 < q.mass a)
    (γ : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγ1 : ∀ a, γ a ≤ 1)
    {ζ α : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) (hα : 0 ≤ α)
    (hmean : (∑ a, q.mass a * γ a) ≤ ζ) :
    (∑ a, p.mass a * (γ a)^α) ≤
      ζ^(α/2) + 2*(finiteRelativeEntropy p q + Real.log 2) / Real.log (1/ζ) := by
  have htail := collision_large_event_bound q γ hγ hζ hmean
  have hsqrt : 0 < Real.sqrt ζ := Real.sqrt_pos.2 hζ
  have hsqrt1 : Real.sqrt ζ < 1 := by
    have := Real.mul_self_sqrt hζ.le
    nlinarith
  have hrare := rare_event_entropy_bound p q hq _ hsqrt hsqrt1 htail
  have hsplit := collision_moment_split p γ hγ hγ1 hsqrt.le hα
  have hlog : Real.log (1 / Real.sqrt ζ) = Real.log (1/ζ) / 2 := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_sqrt hζ.le]
    ring
  rw [hlog] at hrare
  have hdiv : (finiteRelativeEntropy p q + Real.log 2) / (Real.log (1/ζ) / 2) =
      2*(finiteRelativeEntropy p q + Real.log 2) / Real.log (1/ζ) := by ring
  rw [hdiv] at hrare
  rw [← Real.rpow_div_two_eq_sqrt α hζ.le] at hsplit
  linarith

/-- Equation (collision), multiplied by the number of vertices. -/
lemma biased_collision_moment_scaled {A : Type*} [Fintype A]
    (p q : Law A) (hq : ∀ a, 0 < q.mass a)
    (γ : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγ1 : ∀ a, γ a ≤ 1)
    {ζ α v : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) (hα : 0 ≤ α) (hv : 0 ≤ v)
    (hmean : (∑ a, q.mass a * γ a) ≤ ζ) :
    v * (∑ a, p.mass a * (γ a)^α) ≤
      v * ζ^(α/2) + 2*(v*finiteRelativeEntropy p q + v*Real.log 2) / Real.log (1/ζ) := by
  have h := mul_le_mul_of_nonneg_left
    (biased_collision_moment p q hq γ hγ hγ1 hζ hζ1 hα hmean) hv
  convert h using 1 <;> ring

end LooseHamilton
