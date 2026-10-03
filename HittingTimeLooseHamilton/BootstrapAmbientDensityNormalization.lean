module

public import HittingTimeLooseHamilton.DeletedRootCollision
public import Mathlib.Data.Nat.Choose.Bounds

public section

/-! Explicit normalization of ambient root-link counts. No residual-population
normalization or asymptotic absorption is used. -/
noncomputable section
namespace LooseHamilton.BootstrapAmbientDensityNormalization
open Finset

/-- The full ambient link universe absorbs a power of the ambient size with
an explicit constant depending only on the uniformity. -/
theorem ambient_power_le_choose {r N : ℕ} (hr : 3 ≤ r) (hN : 2*r ≤ N) :
    (N : ℝ)^(r-1) ≤
      ((2 : ℝ)^(r-1) * ((r-1).factorial : ℝ)) *
        ((N-1).choose (r-1) : ℝ) := by
  have hsub : N-1+1-(r-1) = N-(r-1) := by omega
  have hd : (N-(r-1))^(r-1) ≤ (r-1).factorial * (N-1).choose (r-1) := by
    simpa only [hsub, Nat.descFactorial_eq_factorial_mul_choose] using
      Nat.pow_sub_le_descFactorial (N-1) (r-1)
  have hp := Nat.pow_le_pow_left (show N ≤ 2*(N-(r-1)) by omega) (r-1)
  rw [Nat.mul_pow] at hp
  have h := hp.trans (Nat.mul_le_mul_left (2^(r-1)) hd)
  have h' : N^(r-1) ≤ (2^(r-1) * (r-1).factorial) * (N-1).choose (r-1) := by
    simpa only [Nat.mul_assoc] using h
  exact_mod_cast h'

/-- Exact adjacent-binomial normalization of the collision term. -/
theorem collision_ratio {r N : ℕ} (hr : 3 ≤ r) (hN : 2*r ≤ N) :
    ((N-2).choose (r-2) : ℝ) / ((N-1).choose (r-1) : ℝ) =
      (r-1 : ℕ) / (N-1 : ℕ) := by
  have hb : (0 : ℝ) < ((N-1).choose (r-1) : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hn : (0 : ℝ) < (N-1 : ℕ) := Nat.cast_pos.mpr (by omega)
  apply (div_eq_div_iff hb.ne' hn.ne').mpr
  have h := Nat.add_one_mul_choose_eq (N-2) (r-2)
  rw [show (N-2)+1=N-1 by omega, show (r-2)+1=r-1 by omega] at h
  have h' : (N-1 : ℕ) * ((N-2).choose (r-2) : ℝ) =
      ((N-1).choose (r-1) : ℝ) * (r-1 : ℕ) := by exact_mod_cast h
  nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Convert a finite bad-edge count to the explicit ambient density estimate.
The counted family need not be assumed to lie in the root universe. -/
theorem density_le {r : ℕ} (hr : 3 ≤ r) (hN : 2*r ≤ Fintype.card V)
    (x : V) (bad : SimpleHypergraph V) (β L : ℝ) (hβ : 0 ≤ β)
    (hcount : (bad.card : ℝ) ≤ β*(Fintype.card V : ℝ)^(r-1) +
      L*((Fintype.card V-2).choose (r-2) : ℝ)) :
    rootLinkDensity r x bad ≤
      ((2 : ℝ)^(r-1) * ((r-1).factorial : ℝ))*β +
      L*(r-1 : ℕ)/(Fintype.card V-1 : ℕ) := by
  have hb : (0 : ℝ) < ((Fintype.card V-1).choose (r-1) : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hp := mul_le_mul_of_nonneg_left (ambient_power_le_choose hr hN) hβ
  rw [rootLinkDensity, rootEdgeUniverse_card r (by omega)]
  calc
    _ ≤ (β*(Fintype.card V : ℝ)^(r-1) +
        L*((Fintype.card V-2).choose (r-2) : ℝ)) /
          ((Fintype.card V-1).choose (r-1) : ℝ) :=
      div_le_div_of_nonneg_right hcount hb.le
    _ = β*(Fintype.card V : ℝ)^(r-1) /
          ((Fintype.card V-1).choose (r-1) : ℝ) +
        L*((Fintype.card V-2).choose (r-2) : ℝ) /
          ((Fintype.card V-1).choose (r-1) : ℝ) := add_div _ _ _
    _ ≤ ((2 : ℝ)^(r-1) * ((r-1).factorial : ℝ))*β +
        L*((Fintype.card V-2).choose (r-2) : ℝ) /
          ((Fintype.card V-1).choose (r-1) : ℝ) := by
      apply add_le_add_left
      apply (div_le_iff₀ hb).mpr
      nlinarith [hp]
    _ = _ := by rw [mul_div_assoc, collision_ratio hr hN, ← mul_div_assoc]

/-- A separate static exclusion contributes additively to the averaged
exceptional-target bound. -/
theorem excluded_union_card_le (E Z : Finset V) (β L : ℝ)
    (hE : (E.card : ℝ) ≤ β*(Fintype.card V : ℝ))
    (hZ : (Z.card : ℝ) ≤ L) :
    ((E ∪ Z).card : ℝ) ≤ β*(Fintype.card V : ℝ)+L := by
  have h : ((E ∪ Z).card : ℝ) ≤ (E.card : ℝ)+(Z.card : ℝ) := by
    exact_mod_cast card_union_le E Z
  exact h.trans (add_le_add hE hZ)

end LooseHamilton.BootstrapAmbientDensityNormalization
