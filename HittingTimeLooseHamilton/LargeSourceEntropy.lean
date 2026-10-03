module

public import HittingTimeLooseHamilton.LargeSourceBudget
public import HittingTimeLooseHamilton.LargeSourceBudgetScales

public section

noncomputable section
namespace LooseHamilton
open Filter Topology AuxiliaryFrame

/-- Every actual auxiliary frame retaining a fixed polynomial fraction of an
A_j source satisfies the entropy budget. No budget assumption is an input.
The budget constant is 2; its cutoff depends on the fixed polynomial loss. -/
theorem eventually_large_source_entropy (r : ℕ) (hr : 3≤r)
    (c A : ℝ) (hc : 0<c) (hA : 0≤A) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, ∀ original : Finset (Finset (Fin N)),
      N=(r-1)*k+original.card → IsPairMatching original → 1≤original.card →
      (original.card:ℝ)≤(N:ℝ)^(1/10:ℝ) →
      ∀ H : SimpleHypergraph (Fin N), c*N*Real.log N≤H.card → H.card≤N.choose r →
      ∀ X : ℕ, 0<X → logarithmicBaseline r k H.card original-
        (N:ℝ)/Real.sqrt (Real.log N)≤Real.log (X:ℝ) →
      ∀ F : Frame r original, (X:ℝ)*(N:ℝ)^(-A)≤F.cycleCount H →
        F.entropyBudget H 2 := by
  obtain ⟨K,hK,hbench⟩ := lemma23 r hr
  obtain ⟨N₀,hN₀⟩ := hbench c hc
  let D : ℝ := 2*((r:ℝ)+2)+4*r+((r:ℝ)-1)*(4*r+2)
  have hD : 0≤D := by
    have hrR : (3:ℝ)≤r := Nat.cast_le.mpr hr
    have hr1 : 0≤(r:ℝ)-1 := by linarith
    dsimp [D]; positivity
  filter_upwards [eventually_ge_atTop N₀,eventually_ge_atTop r,
    FrameScales.L1_tendsto.eventually (eventually_ge_atTop 1),
    (FrameScales.L1_tendsto.const_mul_atTop hc).eventually (eventually_ge_atTop 1),
    eventually_large_source_error K (D+A) hK.le (add_nonneg hD hA)] with N hN₀' hrN hlog hcLog herr
  intro k original hsize hmatching hs hsbound H hlow hhigh X hX hAX F hfrac
  change 1≤Real.log (N:ℝ) at hlog
  change 1≤c*Real.log (N:ℝ) at hcLog
  have hNp : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hXp : 0<(X:ℝ) := Nat.cast_pos.mpr hX
  have hFpos : (0:ℝ)<F.cycleCount H :=
    (mul_pos hXp (Real.rpow_pos_of_pos hNp _)).trans_le hfrac
  have hFN : 0<F.cycleCount H := Nat.cast_pos.mp hFpos
  have hHN : N≤H.card := by
    apply Nat.cast_le.mp (show (N:ℝ)≤H.card from ?_)
    have hh := mul_le_mul_of_nonneg_left hcLog hNp.le
    nlinarith only [hh,hlow]
  have hb := hN₀ N hN₀' k original.card H.card hsize hs hsbound hlow hhigh
    original hmatching rfl
  have hf := frame_benchmark_upper hr hrN hlog original hsize F H hFN hHN
    (hhigh.trans (Nat.choose_le_pow _ _))
  have hlogfrac := Real.log_le_log (mul_pos hXp (Real.rpow_pos_of_pos hNp (-A))) hfrac
  rw [Real.log_mul hXp.ne' (Real.rpow_pos_of_pos hNp (-A)).ne',Real.log_rpow hNp] at hlogfrac
  have hbudgetgap := (abs_le.mp hb).1
  have hmarker : K*((original.card:ℝ)*Real.log N+Real.log N) ≤
      K*((N:ℝ)^(1/10:ℝ)+1)*Real.log N := by
    have hh := mul_le_mul_of_nonneg_right hsbound (by linarith : 0≤Real.log (N:ℝ))
    nlinarith [mul_le_mul_of_nonneg_left hh hK.le]
  apply (F.entropyBudget_iff H 2).mpr
  refine ⟨hFN,?_⟩
  simp only [Fintype.card_fin,FrameScales.L1]
  change FrameEntropy.benchmark r F.k (F.mu H)≤logarithmicBenchmark r N k H.card+D*Real.log N at hf
  unfold FrameEntropy.benchmark at hf
  rw [mul_div_assoc]
  linear_combination hf + hbudgetgap + hmarker + hAX + hlogfrac + herr

end LooseHamilton
