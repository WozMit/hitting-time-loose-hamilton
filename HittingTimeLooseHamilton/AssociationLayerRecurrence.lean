module

public import HittingTimeLooseHamilton.AssociationLayerCardinalities
public import HittingTimeLooseHamilton.AssociationLayerInjection

public section

/-! The exact association-layer recurrence, from forward bounds and the
proved injective reverse encoding. -/
noncomputable section
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {d : V → ℕ} {y : V} {B : Finset V}

theorem association_layer_count_recurrence (hr : 3 ≤ r) (hyB : y ∉ B) (t : ℕ) :
    degreeSum d*t*associationLayerCount r d y B t ≤
      associationBadBudget r d B*t*associationLayerCount r d y B t +
        associationNumerator r d y B*associationLayerCount r d y B (t-1) := by
  have hf := associationForwardIncidence_card_lower hr d y B t
  have hi := Fintype.card_le_of_injective _
    (associationEncodeSwitch_injective (r := r) (t := t) (d := d) hyB)
  rw [associationReverseIncidence_card] at hi
  exact hf.trans (by nlinarith only [hi])

/-- The manuscript's t*A_B*A_t ≤ (r-1)*d_y*d(B)*A_(t-1), with A_B the exact
real difference. This statement requires no positivity assumption on A_B. -/
theorem association_layer_recurrence (hr : 3 ≤ r) (hyB : y ∉ B) (t : ℕ) :
    (t : ℝ)*associationSlack r d B*(associationLayerCount r d y B t : ℝ) ≤
      (associationNumerator r d y B : ℝ)*associationLayerCount r d y B (t-1) := by
  have hnat := association_layer_count_recurrence (d := d) hr hyB t
  have h : (degreeSum d : ℝ)*t*(associationLayerCount r d y B t : ℝ) ≤
      (associationBadBudget r d B : ℝ)*t*(associationLayerCount r d y B t : ℝ) +
        (associationNumerator r d y B : ℝ)*associationLayerCount r d y B (t-1) := by
    exact_mod_cast hnat
  rw [associationSlack_eq_sub_budget]
  calc
    _ = (degreeSum d : ℝ)*t*(associationLayerCount r d y B t : ℝ) -
        (associationBadBudget r d B : ℝ)*t*associationLayerCount r d y B t := by ring
    _ ≤ ((associationBadBudget r d B : ℝ)*t*(associationLayerCount r d y B t : ℝ) +
        (associationNumerator r d y B : ℝ)*associationLayerCount r d y B (t-1)) -
        (associationBadBudget r d B : ℝ)*t*associationLayerCount r d y B t := sub_le_sub_right h _
    _ = _ := by ring
end LooseHamilton
