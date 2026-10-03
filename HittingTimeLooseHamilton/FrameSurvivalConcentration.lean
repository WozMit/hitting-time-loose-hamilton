module

public import HittingTimeLooseHamilton.IndexedSurvivalVariance
public import HittingTimeLooseHamilton.CompletionChebyshev

public section

/-! Relative concentration for labelled families with variable support sizes.
The deterministic center is the full-size hypergeometric survival factor;
the support deficit is retained as an explicit bias. -/
noncomputable section
namespace LooseHamilton.IndexedSurvival
open Finset FrameSurvival CandidateLogSurvival
variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

/-- A mean lying between `A` and `L*A` transfers centered deviations to
`A`, with the deterministic relative bias `L-1`. -/
theorem deviation_transfer {x A μ L h : ℝ} (hA : 0 < A)
    (hlo : A ≤ μ) (hhi : μ ≤ L*A) (hh : 0 ≤ h)
    (hx : ((L-1)+h*L)*A < |x-A|) : h*μ < |x-μ| := by
  have hm : 0 ≤ μ-A := sub_nonneg.mpr hlo
  have ht : |x-A| ≤ |x-μ| + (μ-A) := by
    simpa only [sub_add_sub_cancel, abs_of_nonneg hm] using
      (abs_add_le (x-μ) (μ-A))
  have hmul := mul_le_mul_of_nonneg_left hhi hh
  nlinarith

/-- Chebyshev with the exact deterministic support-deficit bias, for arbitrary
labelled supports in `[k-d,k]`. Identical supports keep their multiplicity. -/
theorem interval_relative_concentration {H : Finset α} {k d τ : ℕ}
    (hm : 0 < H.card) (hk : 0 < k) (hk4 : 4*k ≤ H.card) (ht4 : 4*τ ≤ H.card)
    (F : Finset ι) (support : ι → Finset α) (hne : F.Nonempty)
    (hsub : ∀ i ∈ F, support i ⊆ H)
    (hsize : ∀ i ∈ F, k-d ≤ (support i).card ∧ (support i).card ≤ k)
    {h : ℝ} (hh : 0 < h) :
    (hostBatchLaw (by omega : τ ≤ H.card)).event (fun T =>
      ((Real.exp (2*(d:ℝ)*τ/H.card)-1) + h*Real.exp (2*(d:ℝ)*τ/H.card)) *
          (zeta H.card k τ * F.card) <
        |(count F support T.val : ℝ) - zeta H.card k τ * F.card|) ≤
      (Real.exp (4*(d:ℝ)*τ/H.card) * (Real.exp (4*(τ:ℝ)*k/H.card)-1) *
        uniformOverlap F support / k) / h^2 := by
  classical
  have hτ : τ ≤ H.card := by omega
  have hp := mean_pos hτ F support hsub hne (fun i hi => by
    have := (hsize i hi).2; omega)
  have hc := (hostBatchLaw hτ).finite_relative_chebyshev
    (fun T => (count F support T.val : ℝ)) hh hp
  change (hostBatchLaw hτ).event _ ≤ variance hτ F support /
    (h^2*(mean hτ F support)^2) at hc
  have hb := interval_mean_bounds hm hk4 ht4 F support hsub hsize
  have hA : 0 < zeta H.card k τ * (F.card:ℝ) :=
    mul_pos (zeta_pos (by omega)) (by exact_mod_cast hne.card_pos)
  have he : (hostBatchLaw hτ).event (fun T =>
      ((Real.exp (2*(d:ℝ)*τ/H.card)-1) + h*Real.exp (2*(d:ℝ)*τ/H.card)) *
          (zeta H.card k τ * F.card) <
        |(count F support T.val : ℝ) - zeta H.card k τ * F.card|) ≤
      (hostBatchLaw hτ).event (fun T => h*mean hτ F support <
        |(count F support T.val:ℝ)-mean hτ F support|) := by
    apply FiniteEntropy.Law.event_mono
    intro T hT
    apply deviation_transfer hA (by simpa only [mul_comm] using hb.1)
      (by simpa only [mul_assoc] using hb.2) hh.le hT
  have hv := div_le_div_of_nonneg_right
    (normalized_variance_bound hm hk hk4 ht4 F support hne hsub hsize) (sq_nonneg h)
  have hid : variance hτ F support / (h^2*(mean hτ F support)^2) =
      (variance hτ F support / (mean hτ F support)^2) / h^2 := by ring
  exact he.trans (hc.trans (hid ▸ hv))

end LooseHamilton.IndexedSurvival
