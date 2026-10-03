module

public import HittingTimeLooseHamilton.SequentialMobilityCounting

public section

/-! Forgetting private-coordinate order after sequential mobility. -/
noncomputable section
namespace LooseHamilton.Migration
open Finset
attribute [local instance] Classical.propDecidable

/-- A private-then-endpoint schedule has exactly the advertised multiplicative
factor, including the one-endpoint original-port branch. -/
theorem mobility_schedule_product (d e : ℕ) (cp ce : ℝ) :
    (∏ i ∈ range (d+e), if i<d then cp else ce) = cp^d*ce^e := by
  rw [prod_range_add]
  congr 1
  · calc
      _ = ∏ _i ∈ range d, cp := by
        apply prod_congr rfl
        intro i hi
        simp [mem_range.mp hi]
      _ = cp^d := by simp
  · calc
      _ = ∏ _i ∈ range e, ce := by
        apply prod_congr rfl
        intro i hi
        simp
      _ = ce^e := by simp

/-- A final completion label may have several ordered private-coordinate
representatives. Surjectivity suffices to preserve the exceptional count. -/
theorem sequential_failed_labels_card_le {V L : Type*} [Fintype V] [DecidableEq L]
    (step : (k : ℕ) → ChoicePath V k → V → Prop)
    (value : (k : ℕ) → ChoicePath V k → ℝ) (factor : ℕ → ℝ) (base ε : ℝ)
    (hε : 0 ≤ ε) (hfactor : ∀ k, 0 ≤ factor k)
    (hbase : ∀ p, base ≤ value 0 p)
    (hmove : ∀ k p v, Successful step k p → step k p v →
      factor k * value k p ≤ value (k+1) (p,v))
    (hstep : ∀ k p, Successful step k p →
      ((univ.filter (fun v => ¬step k p v)).card:ℝ) ≤ ε*(Fintype.card V:ℝ))
    (k : ℕ) (labels : Finset L) (forget : ChoicePath V k → L) (weight : L → ℝ)
    (hsurj : ∀ l ∈ labels, ∃ p, forget p=l)
    (hweight : ∀ p, value k p=weight (forget p)) :
    ((labels.filter (fun l => weight l < (∏ i ∈ range k, factor i)*base)).card:ℝ) ≤
      (k:ℝ)*ε*(Fintype.card V:ℝ)^k := by
  have hf := failed_labels_card_le labels forget
    (fun l => (∏ i ∈ range k, factor i)*base ≤ weight l) hsurj
  simp only [not_le] at hf
  have hc := sequential_low_value_card_le step value factor base ε hε hfactor hbase hmove hstep k
  have he : univ.filter (fun p => weight (forget p) < (∏ i ∈ range k, factor i)*base) =
      univ.filter (fun p => value k p < (∏ i ∈ range k, factor i)*base) := by
    ext p
    simp only [mem_filter, mem_univ, true_and, hweight]
  rw [he] at hf
  exact (Nat.cast_le.mpr hf).trans hc
end LooseHamilton.Migration
