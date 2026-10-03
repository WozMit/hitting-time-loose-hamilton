module

public import HittingTimeLooseHamilton.Counting
public import HittingTimeLooseHamilton.HarmonicDeletion

public section

noncomputable section
namespace LooseHamilton

/-- The baseline in equation (baseline), with the original-port prohibition. -/
@[expose] def logarithmicBaseline {N : ℕ} (r k j : ℕ)
    (markers : Finset (Finset (Fin N))) : ℝ :=
  Real.log (cycleCount r markers (completeEdges (Fin N) r)
    (originalPorts markers) : ℝ) - (k : ℝ) * deletionHarmonic j (N.choose r)

/-- The benchmark at mean degree `r*j/N`. -/
@[expose] def logarithmicBenchmark (r N k j : ℕ) : ℝ :=
  (k : ℝ) * Real.log (((r : ℝ)-1) * ((r : ℝ)*j/N)) - ((r : ℝ)-1)*k

lemma benchmark_log_transport {r N j K : ℕ}
    (hr : 3 ≤ r) (hN : 1 ≤ N) (hj : 1 ≤ j) (hK : 1 ≤ K) :
    Real.log (((r : ℝ)-1)*((r : ℝ)*K/N)) - Real.log ((K : ℝ)/j) =
      Real.log (((r : ℝ)-1)*((r : ℝ)*j/N)) := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have hr0 : (r : ℝ) ≠ 0 := by linarith
  have hr1 : (r : ℝ)-1 ≠ 0 := by linarith
  simp only [Real.log_mul hr1 (div_ne_zero (mul_ne_zero hr0 hK0) hN0),
    Real.log_mul hr1 (div_ne_zero (mul_ne_zero hr0 hj0) hN0),
    Real.log_div (mul_ne_zero hr0 hK0) hN0,
    Real.log_div (mul_ne_zero hr0 hj0) hN0,
    Real.log_div hK0 hj0, Real.log_mul hr0 hK0, Real.log_mul hr0 hj0]
  ring

end LooseHamilton
