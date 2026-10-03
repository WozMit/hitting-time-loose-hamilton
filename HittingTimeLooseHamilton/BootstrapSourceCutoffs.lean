module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

public section

/-! Uniform polynomial cutoffs after a bounded number of fixed positive losses.
The thresholds depend only on the fixed parameters, never on a source count. -/
noncomputable section
namespace LooseHamilton.BootstrapSourceCutoffs
open Filter Topology

theorem retained_lower_bound {r N m : ℕ} {c X W : ℝ}
    (hN : 0 < N) (hc : 0 < c) (hX : 0 ≤ X)
    (hfactor : 1 ≤ c^m * (N : ℝ)^r)
    (hW : X / (N : ℝ)^(2*r) ≤ W) :
    X / (N : ℝ)^(3*r) ≤ c^m * W := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hh : 2*r+r=3*r := by omega
  calc
    X / (N : ℝ)^(3*r) ≤ c^m * (X / (N : ℝ)^(2*r)) := by
      apply (div_le_iff₀ (pow_pos hn _)).mpr
      rw [← hh, pow_add]
      have he : c^m * (X / (N : ℝ)^(2*r)) *
          ((N : ℝ)^(2*r) * (N : ℝ)^r) = X * (c^m * (N : ℝ)^r) := by
        field_simp <;> ring
      rw [he]
      simpa using mul_le_mul_of_nonneg_left hfactor hX
    _ ≤ c^m * W := mul_le_mul_of_nonneg_left hW (pow_nonneg hc.le _)

theorem eventually_retained_lower_bound {r : ℕ} (hr : 0 < r)
    {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ X W : ℝ, 0 ≤ X →
      X / (N : ℝ)^(2*r) ≤ W →
      X / (N : ℝ)^(3*r) ≤ c^m * W := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^r) atTop atTop :=
    (tendsto_pow_atTop (Nat.ne_of_gt hr)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop (0 : ℕ), ht.eventually (eventually_ge_atTop (1 / c^m))]
    with N hN hfactor
  refine ⟨hN, fun X W hX hW => retained_lower_bound hN hc hX ?_ hW⟩
  have hp : 0 < c^m := pow_pos hc _
  have hh := (div_le_iff₀ hp).mp hfactor
  simpa [mul_comm] using hh

theorem polynomial_cut_lower_bound {r N : ℕ} {X W : ℝ}
    (hN : 0 < N) (hW : X / (N : ℝ)^(3*r) ≤ W) :
    X / (N : ℝ)^(5*r+2) ≤ W / (N : ℝ)^(2*r+2) := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have he : 5*r+2 = 3*r+(2*r+2) := by omega
  rw [he, pow_add, ← div_div]
  exact div_le_div_of_nonneg_right hW (pow_nonneg hn.le _)

theorem generous_cut_lower_bound {r N : ℕ} (hr : 1 ≤ r)
    (hN : 1 ≤ N) {X W : ℝ} (hX : 0 ≤ X)
    (hW : X / (N : ℝ)^(5*r+2) ≤ W) :
    X * (N : ℝ)^(-(100*r : ℝ)) ≤ W := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (N : ℝ)^(5*r+2) ≤ (N : ℝ)^(100*r) :=
    pow_le_pow_right₀ hn (by omega)
  have he : (100*r : ℝ) = ((100*r : ℕ) : ℝ) := by norm_cast
  rw [he, Real.rpow_neg (le_trans (by norm_num) hn), Real.rpow_natCast, ← div_eq_mul_inv]
  exact (div_le_div_of_nonneg_left hX (pow_pos (lt_of_lt_of_le zero_lt_one hn) _) hp).trans hW

/-- One size threshold works for all source values and every number of losses
up to the fixed move budget. The small-cut threshold stays above the generous
polynomial cutoff used by the registered tests. -/
theorem eventually_bounded_move_cutoffs {r : ℕ} (hr : 0 < r)
    {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ j : ℕ, j ≤ m → ∀ X W : ℝ, 0 ≤ X →
      X / (N : ℝ)^(2*r) ≤ W →
      X / (N : ℝ)^(3*r) ≤ c^j * W ∧
      X / (N : ℝ)^(5*r+2) ≤ (c^j * W) / (N : ℝ)^(2*r+2) ∧
      X * (N : ℝ)^(-(100*r : ℝ)) ≤ (c^j * W) / (N : ℝ)^(2*r+2) := by
  have hall : ∀ᶠ N : ℕ in atTop, ∀ j : Fin (m+1),
      0 < N ∧ ∀ X W : ℝ, 0 ≤ X → X / (N : ℝ)^(2*r) ≤ W →
      X / (N : ℝ)^(3*r) ≤ c^j.val * W :=
    Filter.eventually_all.mpr (fun j => eventually_retained_lower_bound hr hc j.val)
  filter_upwards [hall] with N hN
  refine ⟨(hN ⟨0, by omega⟩).1, ?_⟩
  intro j hj X W hX hW
  have h := hN ⟨j, by omega⟩
  have hret := h.2 X W hX hW
  have hcut := polynomial_cut_lower_bound h.1 hret
  exact ⟨hret, hcut, generous_cut_lower_bound hr h.1 hX hcut⟩

end LooseHamilton.BootstrapSourceCutoffs
