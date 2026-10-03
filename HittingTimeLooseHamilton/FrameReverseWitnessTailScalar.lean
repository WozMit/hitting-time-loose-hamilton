module

public import HittingTimeLooseHamilton.CandidateReverseWitnessTail
public import Mathlib.Analysis.Complex.ExponentialBounds

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [DecidableEq A]

/-- The reverse hypergeometric tail at the real threshold alpha² tau, with
exact exponent 1/64. Rounding the threshold introduces no error. -/
theorem frame_reverse_uniform_tail (U E : Finset A) (hE : E⊆U)
    (τ : ℕ) (hτ : τ≤U.card) (hU : 0<U.card)
    [Nonempty ↥(U.powersetCard τ)] {α : ℝ} (hα : 0≤α) (hsmall : α≤1/16)
    (hdensity : α/8*(U.card:ℝ)≤E.card) :
    (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard τ)).event
      (fun T => ((T.val∩E).card:ℝ)≤α^2*τ) ≤ Real.exp (-α*τ/64) := by
  have hx : 0≤α^2*(τ:ℝ) := by positivity
  have hk : (⌊α^2*(τ:ℝ)⌋₊:ℝ)≤(α/8)*τ/2 := by
    have hf := Nat.floor_le hx
    have ha : α^2≤α/16 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg τ : (0:ℝ)≤τ)
    nlinarith
  have ht := candidate_uniform_lower_tail U E hE τ ⌊α^2*(τ:ℝ)⌋₊ hτ hU
    (α/8) (by positivity) hdensity hk
  have he : (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard τ)).event
      (fun T => ((T.val∩E).card:ℝ)≤α^2*τ) ≤
      (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard τ)).event
        (fun T => (T.val∩E).card≤⌊α^2*(τ:ℝ)⌋₊) := by
    apply FiniteEntropy.Law.event_mono
    intro T hT
    exact (Nat.le_floor_iff hx).mpr hT
  apply (he.trans ht).trans
  apply Real.exp_le_exp.mpr
  have hlog : Real.log 2≤3/4 := by linarith [Real.log_two_lt_d9]
  have hm := mul_nonneg (show 0≤(1-Real.log 2)/16-1/64 by linarith)
    (mul_nonneg hα (Nat.cast_nonneg τ))
  nlinarith
end LooseHamilton
