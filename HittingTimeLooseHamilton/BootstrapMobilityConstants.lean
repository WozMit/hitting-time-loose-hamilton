module

public import HittingTimeLooseHamilton.MigrationCandidateLower
public import HittingTimeLooseHamilton.BootstrapSourceMeanRatios
public import HittingTimeLooseHamilton.BootstrapSourceCutoffs

public section

/-! Constants are fixed from uniformity and the common lower regularity
constant before constructing any sampling event. -/
noncomputable section
namespace LooseHamilton.BootstrapConstants
open Filter

@[expose] def rootThreshold (r : ℕ) : ℝ := 1 / (2*((r : ℝ)-1)^2)
@[expose] def privateFactor (r : ℕ) (c : ℝ) : ℝ := c / (12*((r : ℝ)-1)^2)
@[expose] def endpointFactor (r : ℕ) (c : ℝ) : ℝ := privateFactor r c / 4
@[expose] def portThreshold (r : ℕ) (c : ℝ) : ℝ :=
  (privateFactor r c)^(r-2) * endpointFactor r c / 2

theorem rootThreshold_pos {r : ℕ} (hr : 3 ≤ r) : 0 < rootThreshold r := by
  have hr' : (3 : ℝ) ≤ r := by exact_mod_cast hr
  unfold rootThreshold
  have : (r : ℝ)-1 ≠ 0 := by linarith
  positivity

theorem privateFactor_pos {r : ℕ} (hr : 3 ≤ r) {c : ℝ} (hc : 0 < c) :
    0 < privateFactor r c := by
  have hr' : (3 : ℝ) ≤ r := by exact_mod_cast hr
  unfold privateFactor
  have : (r : ℝ)-1 ≠ 0 := by linarith
  positivity

theorem endpointFactor_pos {r : ℕ} (hr : 3 ≤ r) {c : ℝ} (hc : 0 < c) :
    0 < endpointFactor r c := div_pos (privateFactor_pos hr hc) (by norm_num)

theorem portThreshold_pos {r : ℕ} (hr : 3 ≤ r) {c : ℝ} (hc : 0 < c) :
    0 < portThreshold r c := by
  unfold portThreshold
  exact div_pos (mul_pos (pow_pos (privateFactor_pos hr hc) _) (endpointFactor_pos hr hc))
    (by norm_num)

/-- The port threshold is strictly below the full migration product. -/
theorem portThreshold_lt {r : ℕ} (hr : 3 ≤ r) {c : ℝ} (hc : 0 < c) :
    portThreshold r c < (privateFactor r c)^(r-2) * endpointFactor r c := by
  have h := mul_pos (pow_pos (privateFactor_pos hr hc) (r-2)) (endpointFactor_pos hr hc)
  unfold portThreshold
  linarith

theorem rootThreshold_le_balance {r : ℕ} (hr : 3 ≤ r) {α : ℝ} (hα : α ≤ 1/2) :
    rootThreshold r ≤ (1-α)/((r : ℝ)-1)^2 := by
  have hr' : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hd : 0 < ((r : ℝ)-1)^2 := sq_pos_of_pos (by linarith)
  unfold rootThreshold
  rw [show 1/(2*((r : ℝ)-1)^2) = (1/2)/((r : ℝ)-1)^2 by rw [div_mul_eq_div_div]]
  apply div_le_div_of_nonneg_right _ hd.le
  linarith

/-- Exact private mobility coefficient after occupancy and mean comparisons. -/
theorem privateFactor_eq (r : ℕ) (c : ℝ) :
    privateFactor r c = (rootThreshold r / 3) * (c/2) := by
  unfold privateFactor rootThreshold
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- A quarter of the source mass with the private per-cut coefficient
already suffices for the conservative endpoint coefficient. -/
theorem endpointFactor_eq (r : ℕ) (c : ℝ) :
    endpointFactor r c = (rootThreshold r / 3) * (c/2) * (1/4) := by
  rw [endpointFactor, privateFactor_eq]
  ring

theorem privateFactor_le_root_ratio {r : ℕ} (hr : 3 ≤ r) {c d : ℝ}
    (h : c/2 ≤ d) : privateFactor r c ≤ rootThreshold r / 3 * d := by
  rw [privateFactor_eq]
  exact mul_le_mul_of_nonneg_left h (div_nonneg (rootThreshold_pos hr).le (by norm_num))

/-- One positive lower factor works for either kind of migration. -/
@[expose] def mobilityFloor (r : ℕ) (c : ℝ) : ℝ :=
  min 1 (min (privateFactor r c) (endpointFactor r c))

theorem mobilityFloor_pos {r : ℕ} (hr : 3 ≤ r) {c : ℝ} (hc : 0 < c) :
    0 < mobilityFloor r c := by
  exact lt_min (by norm_num) (lt_min (privateFactor_pos hr hc) (endpointFactor_pos hr hc))

theorem mobilityFloor_bounds (r : ℕ) (c : ℝ) :
    mobilityFloor r c ≤ 1 ∧ mobilityFloor r c ≤ privateFactor r c ∧
      mobilityFloor r c ≤ endpointFactor r c := by
  exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩

/-- The prescribed constants, with a budget of r moves, preserve every
source and retained-cut cutoff required by the bootstrap. -/
theorem eventually_fixed_cutoffs {r : ℕ} (hr : 3 ≤ r) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in Filter.atTop, 0 < N ∧ ∀ j : ℕ, j ≤ r → ∀ X W : ℝ, 0 ≤ X →
      X / (N : ℝ)^(2*r) ≤ W →
      X / (N : ℝ)^(3*r) ≤ (mobilityFloor r c)^j * W ∧
      X / (N : ℝ)^(5*r+2) ≤ ((mobilityFloor r c)^j * W) / (N : ℝ)^(2*r+2) ∧
      X * (N : ℝ)^(-(100*r : ℝ)) ≤
        ((mobilityFloor r c)^j * W) / (N : ℝ)^(2*r+2) :=
  BootstrapSourceCutoffs.eventually_bounded_move_cutoffs (by omega)
    (mobilityFloor_pos hr hc) r

end LooseHamilton.BootstrapConstants
