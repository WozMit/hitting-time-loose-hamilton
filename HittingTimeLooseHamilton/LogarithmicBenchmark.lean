module

public import HittingTimeLooseHamilton.BenchmarkAlgebra
public import HittingTimeLooseHamilton.Normalization
public import HittingTimeLooseHamilton.CompleteCountLog
public import HittingTimeLooseHamilton.CompleteDegreeLog
public import HittingTimeLooseHamilton.BenchmarkRange

public section

set_option maxHeartbeats 1000000
noncomputable section
namespace LooseHamilton

/-- A finite estimate, before the manuscript's asymptotic range is imposed. -/
theorem logarithmicBenchmark_finite :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r N k s j : ℕ,
      3 ≤ r → 2*r ≤ N → 3 ≤ k → 1 ≤ s → 2*s ≤ k →
      N = (r-1)*k+s → 1 ≤ j → j ≤ N.choose r →
      ∀ markers : Finset (Finset (Fin N)), IsPairMatching markers → markers.card = s →
      |logarithmicBaseline r k j markers - logarithmicBenchmark r N k j| ≤
        C*((s:ℝ)+1)*(Real.log N+1) + 2*(r:ℝ)^2 + (k:ℝ)/j := by
  obtain ⟨C, hC, hcount⟩ := log_allowedCompleteFormula_bound
  refine ⟨C, hC, ?_⟩
  intro r N k s j hr hN hk hs hsk hsize hj hjK markers hM hcard
  have hkN : k ≤ N := by
    have : 1 ≤ r-1 := by omega
    nlinarith
  have hN1 : 1 ≤ N := by omega
  have hK1 : 1 ≤ N.choose r := le_trans hj hjK
  have hsize' : Fintype.card (Fin N) = (r-1)*k+markers.card := by
    simpa [hcard] using hsize
  obtain ⟨root, hroot⟩ := Finset.card_pos.mp (show 0 < markers.card by omega)
  have hc := allowedHost_count hr hM hroot hk (by omega) hsize'
  rw [completeHost_count hr hM hroot hk (by omega) hsize'] at hc
  simp only [Fintype.card_fin, hcard] at hc
  have h₁ := hcount r N k s hr (by omega) hs hsk hsize
  rw [← hc] at h₁
  have h₂ := completeMeanDegree_log_error hr hN hkN
  have h₃ := scaled_deletionHarmonic_log_bound k hj hjK
  have htransport := benchmark_log_transport hr hN1 hj hK1
  rw [← completeMeanDegree_eq_mean (by omega : 1 ≤ r) hN1] at htransport
  have hsizeR : (N:ℝ)-(s:ℝ) = ((r:ℝ)-1)*k := by
    have he : (N:ℝ) = ((r-1:ℕ):ℝ)*k+s := by exact_mod_cast hsize
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] at he
    linarith
  rw [hsizeR] at h₁
  have h₂' : |(k:ℝ) * (Real.log (((r:ℝ)-1)*completeMeanDegree r N) -
      (((r:ℝ)-1)*Real.log N - Real.log ((r-2).factorial:ℝ)))| ≤ 2*(r:ℝ)^2 := by
    simpa only [abs_mul, abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k)] using h₂
  obtain ⟨h₁l,h₁u⟩ := abs_le.mp h₁
  obtain ⟨h₂l,h₂u⟩ := abs_le.mp h₂'
  obtain ⟨h₃l,h₃u⟩ := abs_le.mp h₃
  dsimp [logarithmicBaseline, logarithmicBenchmark]
  rw [← htransport]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Lemma 2.3, with the uniform `O_r` quantifiers written explicitly.
The error constant is chosen before `c`; only the threshold may depend on `c`.
`N.choose r` is the complete process length, and the baseline counts actual
mixed cycles obeying the fixed original-port prohibition. -/
@[expose] def Lemma23 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ C : ℝ, 0 < C ∧
    ∀ c : ℝ, 0 < c → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k s j : ℕ,
      N = (r-1)*k+s → 1 ≤ s → (s:ℝ) ≤ (N:ℝ)^(1/10:ℝ) →
      c*N*Real.log N ≤ j → j ≤ N.choose r →
      ∀ markers : Finset (Finset (Fin N)), IsPairMatching markers → markers.card = s →
      |logarithmicBaseline r k j markers - logarithmicBenchmark r N k j| ≤
        C*((s:ℝ)*Real.log N + Real.log N)

/-- The logarithmic benchmark of the manuscript (Lemma 2.3). -/
theorem lemma23 : Lemma23 := by
  obtain ⟨A, hA, hfinite⟩ := logarithmicBenchmark_finite
  intro r hr
  refine ⟨2*A+2*(r:ℝ)^2+1, by positivity, ?_⟩
  intro c hc
  obtain ⟨N₀, hN₀⟩ := benchmark_range_eventually r hr c hc
  refine ⟨N₀, ?_⟩
  intro N hN k s j hsize hs hsbound hj hjK markers hM hcard
  obtain ⟨hNr, hk, hsk, hj1, hlog, hkj⟩ := hN₀ N hN k s j hsize hs hsbound hj
  have hb := hfinite r N k s j hr hNr hk hs hsk hsize hj1 hjK markers hM hcard
  have hs0 : (0:ℝ) ≤ s := by positivity
  have hL0 : 0 ≤ Real.log (N:ℝ) := by linarith
  have hAL : 0 ≤ A*((s:ℝ)+1) := mul_nonneg hA (by positivity)
  have hAL' := mul_le_mul_of_nonneg_left (show Real.log (N:ℝ)+1 ≤ 2*Real.log N by linarith) hAL
  have hbase : 1 ≤ (s:ℝ)*Real.log N+Real.log N := by nlinarith
  have hrerr : 0 ≤ 2*(r:ℝ)^2+1 := by positivity
  have herr := mul_le_mul_of_nonneg_left hbase hrerr
  apply hb.trans
  nlinarith

end LooseHamilton
