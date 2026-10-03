module

public import HittingTimeLooseHamilton.EndpointCutCardinality
public import Mathlib.Analysis.SpecificLimits.Basic

public section

/-! Explicit finite replacement for Section 9's polynomial small-cut loss.
The cutoff is `W / N^(2*r+2)`, and the relative loss is at most
`((r-1)+(r-1)^2) / N^4`. All powers here are ordinary natural powers. -/
noncomputable section
namespace LooseHamilton.Migration
open Filter Topology

@[expose] def cutLossCoefficient (r : ℕ) : ℝ := ((r - 1) + (r - 1)^2 : ℕ)

@[expose] def cutLoss (r N : ℕ) : ℝ := cutLossCoefficient r / (N : ℝ)^4

lemma cutLoss_nonneg (r N : ℕ) : 0 ≤ cutLoss r N := by
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)

lemma polynomial_cut_loss_eq {r N : ℕ} (hr : 1 ≤ r) (hN : 0 < N) :
    cutLossCoefficient r * (N : ℝ)^(2*r-2) / (N : ℝ)^(2*r+2) =
      cutLoss r N := by
  have he : 2*r+2 = (2*r-2)+4 := by omega
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  unfold cutLoss
  rw [he, pow_add]
  field_simp <;> ring

/-- The exact loss tends to zero for each fixed uniformity. -/
theorem cutLoss_tendsto (r : ℕ) :
    Tendsto (cutLoss r) atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop
    ((tendsto_pow_atTop (by decide : (4 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop)

/-- In particular, a single uniform size threshold makes the discarded mass
at most one quarter of the source, independently of the host and cut counts. -/
theorem eventually_cutLoss_le_quarter (r : ℕ) :
    ∀ᶠ N in atTop, cutLoss r N ≤ 1/4 :=
  ((cutLoss_tendsto r).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4))).mono
    (fun _ h => h.le)

end LooseHamilton.Migration
