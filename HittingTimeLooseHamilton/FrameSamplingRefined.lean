module

public import HittingTimeLooseHamilton.FrameSamplingParameters

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open AuxiliaryFrame Finset

/-- Removing a distinguished sampled edge reduces the sampling density. -/
lemma erased_batch_ratio_le (m t : ℕ) (hm : 1 < m) (ht : 1 ≤ t) (htm : t ≤ m) :
    ((t-1:ℕ):ℝ)/(m-1:ℕ) ≤ (t:ℝ)/m := by
  have hmR : (1:ℝ)< m := by exact_mod_cast hm
  have htR : (1:ℝ)≤t := by exact_mod_cast ht
  have htmR : (t:ℝ)≤ m := by exact_mod_cast htm
  rw [Nat.cast_sub ht,Nat.cast_sub (by omega : 1≤ m),Nat.cast_one]
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

/-- The actual floor-defined batch obeys both density bounds. -/
lemma actual_batch_ratio_bounds {V : Type} [Fintype V] [DecidableEq V]
    {r : ℕ} {original : Finset (Finset V)} (f : Frame r original)
    (D : Finset V) (H : SimpleHypergraph V) (hk : 0<f.k)
    (hm : 0<(unexposed f D H).card) (hnu : 0≤FrameScales.nu (Fintype.card V)) :
    (batchSize f D H:ℝ)/(unexposed f D H).card ≤
      FrameScales.nu (Fintype.card V)/f.k ∧
    (batchSize f D H:ℝ)*f.k/(unexposed f D H).card ≤
      FrameScales.nu (Fintype.card V) := by
  have hkR : (0:ℝ)<f.k := by exact_mod_cast hk
  have hmR : (0:ℝ)<(unexposed f D H).card := by exact_mod_cast hm
  have hf : (batchSize f D H:ℝ) ≤
      FrameScales.nu (Fintype.card V)*(unexposed f D H).card/f.k :=
    Nat.floor_le (by positivity)
  have hp := (le_div_iff₀ hkR).mp hf
  constructor
  · apply (div_le_div_iff₀ hmR hkR).mpr
    nlinarith
  · exact (div_le_iff₀ hmR).mpr hp

/-- The completion size k-1 remains comparable to original N, before any
candidate is chosen. -/
lemma completion_k_comparison {V : Type} [Fintype V] [DecidableEq V]
    {r : ℕ} {original : Finset (Finset V)} (f : Frame r original)
    (hr : 3≤r) (hN : 32*r≤Fintype.card V) :
    0<f.k-1 ∧ (Fintype.card V:ℝ) ≤ (16*((r:ℝ)-1))*(f.k-1:ℕ) := by
  have hk := frame_k_comparison_unconditional f hr (by omega)
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hNR : (32:ℝ)*r≤Fintype.card V := by exact_mod_cast hN
  have hk2 : 2≤f.k := by
    by_contra h
    have hh : (f.k:ℝ)≤1 := by exact_mod_cast (show f.k≤1 by omega)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0≤8*((r:ℝ)-1) by linarith)
    nlinarith [hk.1]
  refine ⟨by omega,?_⟩
  have hc : (f.k:ℝ)≤2*(f.k-1:ℕ) := by exact_mod_cast (show f.k≤2*(f.k-1) by omega)
  have hh := mul_le_mul_of_nonneg_left hc (show 0≤8*((r:ℝ)-1) by linarith)
  nlinarith [hk.1]
end LooseHamilton.CandidateBalance
