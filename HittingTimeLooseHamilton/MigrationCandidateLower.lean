module

public import HittingTimeLooseHamilton.CandidateBalanceSpecification
public import HittingTimeLooseHamilton.DirectedCompletions

public section

/-! Numerical bridge from the paper's relative candidate balance to the
explicit pointwise count hypothesis of the deterministic migration lemmas. -/
noncomputable section
namespace LooseHamilton.Migration

/-- A balanced candidate has the required lower count, with its normalization
retained exactly. This lemma makes no assertion about how balance is obtained. -/
theorem balanced_count_lower {X Y μ scale α : ℝ}
    (hX : 0 < X) (hμ : 0 < μ) (hscale : 0 < scale)
    (hbalance : |Y / (X / (scale * μ)) - 1| ≤ α) :
    ((1 - α) / scale) * X / μ ≤ Y := by
  have hd : 0 < X / (scale * μ) := div_pos hX (mul_pos hscale hμ)
  have h : 1 - α ≤ Y / (X / (scale * μ)) := by
    linarith [(abs_le.mp hbalance).1]
  have h' := (le_div_iff₀ hd).mp h
  convert h' using 1 <;> ring

/-- In uniformity `r`, the exact directed normalization is
`X / (((r:ℝ)-1)^2 * μ)`, so `λ=(1-α)/((r:ℝ)-1)^2`. -/
theorem balanced_directed_count_lower {r : ℕ} (hr : 3 ≤ r)
    {X Y μ α : ℝ} (hX : 0 < X) (hμ : 0 < μ)
    (hbalance : |Y / (X / (((r : ℝ) - 1)^2 * μ)) - 1| ≤ α) :
    ((1 - α) / ((r : ℝ) - 1)^2) * X / μ ≤ Y := by
  apply balanced_count_lower hX hμ _ hbalance
  have hr' : (3 : ℝ) ≤ r := by exact_mod_cast hr
  exact pow_pos (by linarith) _

theorem candidate_lower_coefficient_nonneg {r : ℕ} {α : ℝ} (hα : α ≤ 1) :
    0 ≤ (1 - α) / ((r : ℝ) - 1)^2 :=
  div_nonneg (sub_nonneg.mpr hα) (sq_nonneg _)

/-- Forgetting a prescribed relative direction can only increase the count.
This also applies on the surviving-vertex subtype of a private candidate. -/
theorem directed_count_le_unrestricted {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (hr : 3 ≤ r) (markers host : Finset (Finset V)) (ports : Finset V)
    (root distinguished : ↥markers) (a : ↥root.val) (y : V) :
    directedCycleCount r markers host ports root distinguished a y ≤
      unrestrictedCycleCount r markers host := by
  apply Finset.card_le_card
  intro F hF
  apply (mem_unrestrictedCycleFamily r markers host F hr).mpr
  have h := (mem_directedCycleFamily r markers host ports root distinguished a y F).mp hF
  have hc := (mem_cycleFamily r markers host ports F).mp h.1
  exact ⟨hc.1, hc.2.1⟩

/-- The directed candidate lower bound remains valid for the unrestricted
`X` summand used by the private-coordinate injection. -/
theorem balanced_directed_count_lower_unrestricted
    {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} (hr : 3 ≤ r)
    (markers host : Finset (Finset V)) (ports : Finset V)
    (root distinguished : ↥markers) (a : ↥root.val) (y : V)
    {X μ α : ℝ} (hX : 0 < X) (hμ : 0 < μ)
    (hbalance : |(directedCycleCount r markers host ports root distinguished a y : ℝ) /
      (X / (((r : ℝ) - 1)^2 * μ)) - 1| ≤ α) :
    ((1 - α) / ((r : ℝ) - 1)^2) * X / μ ≤
      (unrestrictedCycleCount r markers host : ℝ) :=
  (balanced_directed_count_lower hr hX hμ hbalance).trans
    (Nat.cast_le.mpr (directed_count_le_unrestricted hr markers host ports root distinguished a y))

end LooseHamilton.Migration
