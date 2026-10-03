module

public import Mathlib

public section

/-! Finite weighted averaging used by the deterministic migration maps.
Exceptional cuts are combined by their weights, without a union bound. -/
noncomputable section
open Finset
namespace LooseHamilton.Migration
variable {B T : Type*} [DecidableEq B] [DecidableEq T]

/-- A finite nonnegative mass bound controls the number of large entries. -/
theorem exceptional_card_mul_le (s : Finset T) (f : T → ℝ) (a K : ℝ)
    (hf : ∀ t ∈ s, 0 ≤ f t) (hs : ∑ t ∈ s, f t ≤ K) :
    ((s.filter (fun t => a < f t)).card : ℝ) * a ≤ K := by
  calc
    _ = ∑ t ∈ s.filter (fun t => a < f t), a := by simp
    _ ≤ ∑ t ∈ s.filter (fun t => a < f t), f t := by
      apply sum_le_sum
      intro t ht
      exact (mem_filter.mp ht).2.le
    _ ≤ ∑ t ∈ s, f t := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by
      intro t ht _; exact hf t ht)
    _ ≤ K := hs

/-- The total discarded weight is at most the number of cuts times the cutoff. -/
theorem small_cut_mass_le (s : Finset B) (w : B → ℝ) (q : ℝ) (hq : 0 ≤ q) :
    (∑ b ∈ s.filter (fun b => w b < q), w b) ≤ (s.card : ℝ) * q := by
  calc
    _ ≤ ∑ b ∈ s.filter (fun b => w b < q), q := sum_le_sum (fun b hb =>
      (mem_filter.mp hb).2.le)
    _ = ((s.filter (fun b => w b < q)).card : ℝ) * q := by simp
    _ ≤ (s.card : ℝ) * q := mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (card_le_card (filter_subset _ _))) hq

/-- Total exceptional mass, obtained by interchanging the two finite sums. -/
theorem weighted_bad_mass_sum_le (cuts : Finset B) (targets : Finset T)
    (w : B → ℝ) (bad : B → T → Prop) [DecidableRel bad] (η N W : ℝ)
    (hw : ∀ b ∈ cuts, 0 ≤ w b)
    (hbad : ∀ b ∈ cuts, ((targets.filter (bad b)).card : ℝ) ≤ η * N)
    (hmass : ∑ b ∈ cuts, w b ≤ W) (hηN : 0 ≤ η * N) :
    (∑ t ∈ targets, ∑ b ∈ cuts.filter (fun b => bad b t), w b) ≤ η * N * W := by
  simp_rw [sum_filter]
  rw [sum_comm]
  calc
    _ = ∑ b ∈ cuts, ((targets.filter (bad b)).card : ℝ) * w b := by
      apply sum_congr rfl
      intro b hb
      rw [← sum_filter]
      simp
    _ ≤ ∑ b ∈ cuts, (η * N) * w b := sum_le_sum (fun b hb =>
      mul_le_mul_of_nonneg_right (hbad b hb) (hw b hb))
    _ = η * N * ∑ b ∈ cuts, w b := by rw [mul_sum]
    _ ≤ η * N * W := mul_le_mul_of_nonneg_left hmass hηN

/-- For all but `ε N` targets, the exceptional cut mass is at most `ε W`.
The per-cut exceptional target allowance is `ε² N`. -/
theorem weighted_exceptional_targets (cuts : Finset B) (targets : Finset T)
    (w : B → ℝ) (bad : B → T → Prop) [DecidableRel bad] (ε N W : ℝ)
    (hw : ∀ b ∈ cuts, 0 ≤ w b) (hε : 0 < ε) (hN : 0 ≤ N) (hW : 0 < W)
    (hbad : ∀ b ∈ cuts, ((targets.filter (bad b)).card : ℝ) ≤ ε ^ 2 * N)
    (hmass : ∑ b ∈ cuts, w b ≤ W) :
    ((targets.filter (fun t => ε * W <
      ∑ b ∈ cuts.filter (fun b => bad b t), w b)).card : ℝ) ≤ ε * N := by
  have hsum := weighted_bad_mass_sum_le cuts targets w bad (ε^2) N W hw hbad hmass
    (mul_nonneg (sq_nonneg ε) hN)
  have hmark := exceptional_card_mul_le targets
    (fun t => ∑ b ∈ cuts.filter (fun b => bad b t), w b) (ε*W) (ε^2*N*W)
    (fun t ht => sum_nonneg (fun b hb => hw b (mem_filter.mp hb).1)) hsum
  have hp : 0 < ε * W := mul_pos hε hW
  have heq : ε^2*N*W = (ε*N)*(ε*W) := by ring
  rw [heq] at hmark
  exact (mul_le_mul_iff_left₀ hp).mp hmark

/-- Removing at most `ε W` exceptional mass from retained cuts leaves the
claimed source mass. -/
theorem good_retained_mass_ge (cuts : Finset B) (w : B → ℝ) (bad : B → Prop)
    [DecidablePred bad] (δ ε W : ℝ)
    (hretained : (1-δ)*W ≤ ∑ b ∈ cuts, w b)
    (hbad : (∑ b ∈ cuts.filter bad, w b) ≤ ε*W) :
    (1-δ-ε)*W ≤ ∑ b ∈ cuts.filter (fun b => ¬ bad b), w b := by
  have heq := sum_filter_add_sum_filter_not cuts bad w
  nlinarith

/-- Retaining every cut at least as large as `W δ` loses at most
`card cuts * δ` of the original mass. -/
theorem retained_mass_ge (cuts : Finset B) (w : B → ℝ) (W δ : ℝ)
    (hW : 0 ≤ W) (hδ : 0 ≤ δ) (hpartition : ∑ b ∈ cuts, w b = W) :
    (1-(cuts.card:ℝ)*δ)*W ≤ ∑ b ∈ cuts.filter (fun b => W*δ ≤ w b), w b := by
  have hsmall := small_cut_mass_le cuts w (W*δ) (mul_nonneg hW hδ)
  have hsplit := sum_filter_add_sum_filter_not cuts (fun b => w b < W*δ) w
  simp only [not_lt] at hsplit
  rw [hpartition] at hsplit
  nlinarith

/-- Averaging exceptional directed labels over their target coordinate. -/
theorem coordinate_exceptional_targets (targets : Finset T) (f : T → ℝ)
    (ε N : ℝ) (k : ℕ) (hf : ∀ t ∈ targets, 0 ≤ f t)
    (hε : 0 < ε) (hN : 0 < N)
    (hsum : ∑ t ∈ targets, f t ≤ ε^2*N^(k+1)) :
    ((targets.filter (fun t => ε*N^k < f t)).card : ℝ) ≤ ε*N := by
  have hm := exceptional_card_mul_le targets f (ε*N^k) (ε^2*N^(k+1)) hf hsum
  have he : ε^2*N^(k+1) = (ε*N)*(ε*N^k) := by rw [pow_succ]; ring
  rw [he] at hm
  exact (mul_le_mul_iff_left₀ (mul_pos hε (pow_pos hN k))).mp hm

/-- General finite weighted Markov bound, before choosing the square-root scale. -/
theorem weighted_exceptional_targets_div (cuts : Finset B) (targets : Finset T)
    (w : B → ℝ) (bad : B → T → Prop) [DecidableRel bad] (η ε N W : ℝ)
    (hw : ∀ b ∈ cuts, 0 ≤ w b) (hε : 0 < ε) (hηN : 0 ≤ η*N) (hW : 0 < W)
    (hbad : ∀ b ∈ cuts, ((targets.filter (bad b)).card : ℝ) ≤ η*N)
    (hmass : ∑ b ∈ cuts, w b ≤ W) :
    ((targets.filter (fun t => ε*W <
      ∑ b ∈ cuts.filter (fun b => bad b t), w b)).card : ℝ) ≤ η*N/ε := by
  have hs := weighted_bad_mass_sum_le cuts targets w bad η N W hw hbad hmass hηN
  have hm := exceptional_card_mul_le targets
    (fun t => ∑ b ∈ cuts.filter (fun b => bad b t), w b) (ε*W) (η*N*W)
    (fun t ht => sum_nonneg (fun b hb => hw b (mem_filter.mp hb).1)) hs
  apply (le_div_iff₀ hε).mpr
  rw [← mul_assoc] at hm
  exact (mul_le_mul_iff_left₀ hW).mp hm

/-- A label can contribute exceptional incidences to at most `d` coordinates.
This accounts for every private coordinate, rather than selecting only one. -/
theorem coordinate_incidence_sum_le [Fintype T] (labels : Finset B)
    (coords : B → Finset T) (d : ℕ)
    (hcoords : ∀ b ∈ labels, (coords b).card ≤ d) :
    (∑ t : T, (labels.filter (fun b => t ∈ coords b)).card) ≤ d*labels.card := by
  simp_rw [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  calc
    _ = ∑ b ∈ labels, (coords b).card := by
      apply sum_congr rfl
      intro b hb
      simp
    _ ≤ ∑ b ∈ labels, d := sum_le_sum (fun b hb => hcoords b hb)
    _ = d*labels.card := by simp [Nat.mul_comm]
  simp
end LooseHamilton.Migration


