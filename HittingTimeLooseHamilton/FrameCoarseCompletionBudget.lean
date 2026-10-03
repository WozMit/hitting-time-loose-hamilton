module

public import HittingTimeLooseHamilton.AuxiliaryFrameEntropy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

/-! Coarse entropy of the actual simultaneous-direction completion family.
No direction class is enlarged or replaced in these estimates. -/
noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- The polynomial cutoff implies nonemptiness of the actual completion family. -/
theorem completion_nonempty_of_cutoff (F : Frame r original)
    (H : Finset (Finset V)) (c : Finset V × V × V)
    (hN : 0 < Fintype.card V) (hX : (F.cycleFamily H).Nonempty)
    (hY : (F.cycleCount H:ℝ) * (Fintype.card V:ℝ) ^ (-(100*(r:ℝ))) ≤
      F.completionCount H c) :
    (F.completionFamily H c).Nonempty := by
  apply card_pos.mp
  have hp : (0:ℝ)<F.completionCount H c := lt_of_lt_of_le
    (mul_pos (Nat.cast_pos.mpr (card_pos.mpr hX))
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _)) hY
  exact_mod_cast hp

/-- Taking logarithms of the cutoff loses exactly `100*r*log N`. -/
theorem completion_log_cutoff (F : Frame r original)
    (H : Finset (Finset V)) (c : Finset V × V × V)
    (hN : 0 < Fintype.card V) (hX : (F.cycleFamily H).Nonempty)
    (hY : (F.cycleCount H:ℝ) * (Fintype.card V:ℝ) ^ (-(100*(r:ℝ))) ≤
      F.completionCount H c) :
    Real.log (F.cycleCount H) - 100*(r:ℝ)*Real.log (Fintype.card V) ≤
      Real.log (F.completionCount H c) := by
  have hXpos : (0:ℝ)<F.cycleCount H := Nat.cast_pos.mpr (card_pos.mpr hX)
  have hNpos : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hN
  have hp := Real.rpow_pos_of_pos hNpos (-(100*(r:ℝ)))
  have hl := Real.log_le_log (mul_pos hXpos hp) hY
  rw [Real.log_mul hXpos.ne' hp.ne', Real.log_rpow hNpos] at hl
  linarith

/-- Uniform coarse count bound with the original frame mean degree. -/
theorem completion_coarse_log_original (F : Frame r original) (hr : 3≤r)
    (H : Finset (Finset V)) (c : Finset V × V × V)
    {B : ℝ} (hB : 0≤B) (hN : 0<Fintype.card V)
    (hscale : 1≤Real.sqrt (FrameScales.L1 (Fintype.card V)))
    (hbudget : F.entropyBudget H B) (hmu : 1≤F.mu H)
    (hY : (F.cycleCount H:ℝ) * (Fintype.card V:ℝ) ^ (-(100*(r:ℝ))) ≤
      F.completionCount H c) :
    ((F.k-1:ℕ):ℝ)*Real.log (F.mu H) -
      (((r:ℝ)-1)+B+100*r)*(Fintype.card V:ℝ) ≤
        Real.log (F.completionCount H c) := by
  have hcoarse := F.entropyBudget_coarse hr H hB hscale hbudget
  have hl := F.completion_log_cutoff H c hN hbudget.1 hY
  have hlog := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr hN : (0:ℝ)<Fintype.card V)
  have hk : ((F.k-1:ℕ):ℝ)≤F.k := Nat.cast_le.mpr (Nat.sub_le _ _)
  have hterm := mul_le_mul_of_nonneg_right hk (Real.log_nonneg hmu)
  have hloss := mul_le_mul_of_nonneg_left hlog (show (0:ℝ)≤100*r by positivity)
  nlinarith

/-- Replacing the mean degree by a contracted value at most twice as large
costs at most one additional original vertex count. -/
theorem completion_coarse_log_contracted (F : Frame r original) (hr : 3≤r)
    (H : Finset (Finset V)) (c : Finset V × V × V)
    {B muc : ℝ} (hB : 0≤B) (hN : 0<Fintype.card V)
    (hscale : 1≤Real.sqrt (FrameScales.L1 (Fintype.card V)))
    (hbudget : F.entropyBudget H B) (hmu : 1≤F.mu H)
    (hmc : 0<muc) (hmc_upper : muc≤2*F.mu H)
    (hY : (F.cycleCount H:ℝ) * (Fintype.card V:ℝ) ^ (-(100*(r:ℝ))) ≤
      F.completionCount H c) :
    ((F.k-1:ℕ):ℝ)*Real.log muc -
      ((r:ℝ)+B+100*r)*(Fintype.card V:ℝ) ≤
        Real.log (F.completionCount H c) := by
  have hh := F.completion_coarse_log_original hr H c hB hN hscale hbudget hmu hY
  have hlog := Real.log_le_log hmc hmc_upper
  have hmupos : 0<F.mu H := lt_of_lt_of_le zero_lt_one hmu
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hmupos.ne'] at hlog
  have hlog2 : Real.log (2:ℝ)≤1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hkn : ((F.k-1:ℕ):ℝ)≤Fintype.card V := by
    exact_mod_cast (Nat.sub_le F.k 1).trans (F.k_le_n.trans (by
      have := F.n_add_deleted; omega))
  have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (F.k-1) : (0:ℝ)≤(F.k-1:ℕ))
  have hlogmul := mul_le_mul_of_nonneg_left hlog2
    (Nat.cast_nonneg (F.k-1) : (0:ℝ)≤(F.k-1:ℕ))
  nlinarith
end LooseHamilton.AuxiliaryFrame.Frame
