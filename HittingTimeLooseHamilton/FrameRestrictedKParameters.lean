module

public import HittingTimeLooseHamilton.FrameRestrictedParameters

public section

/-! A frame's cycle-size parameter is uniformly comparable with original N,
even before any cycle or entropy-budget hypothesis is imposed. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- Integer division loses less than one cycle edge. No witness is assumed. -/
theorem frame_k_comparison_unconditional (f : Frame r original) (hr : 3 ≤ r)
    (hN : 16*r ≤ Fintype.card V) :
    (Fintype.card V:ℝ) ≤ (8*((r:ℝ)-1))*f.k ∧
      (f.k:ℝ) ≤ Fintype.card V ∧ 0 < f.k := by
  have hs := f.twice_s_le_n
  have hn := f.n_add_deleted
  have hd := f.val.deleted_card_le
  have hrem := Nat.mod_lt (f.n-f.s) (by omega : 0<r-1)
  have hdiv := Nat.mod_add_div (f.n-f.s) (r-1)
  change (f.n-f.s) % (r-1)+(r-1)*f.k = f.n-f.s at hdiv
  have hsub : f.n-f.s+f.s=f.n := by omega
  have ha : Fintype.card V ≤ 2*f.n := by omega
  have hrsub : r-1+1=r := by omega
  have hactive : 12*r ≤ f.n := by omega
  have hb : f.n ≤ 4*(r-1)*f.k := by nlinarith
  have hh : Fintype.card V ≤ 8*(r-1)*f.k := by nlinarith
  refine ⟨?_,?_,?_⟩
  · have hhR : (Fintype.card V:ℝ) ≤ (8:ℝ)*(r-1:ℕ)*f.k := by exact_mod_cast hh
    simpa only [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] using hhR
  · exact_mod_cast (f.k_le_n.trans (by omega : f.n ≤ Fintype.card V))
  · nlinarith
end LooseHamilton.CandidateBalance
