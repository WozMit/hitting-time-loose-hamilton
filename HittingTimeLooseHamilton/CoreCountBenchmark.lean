module

public import HittingTimeLooseHamilton.CoreCountBenchmarkRates
public import HittingTimeLooseHamilton.LogarithmicBenchmark
public import HittingTimeLooseHamilton.TerminalFeasibilityScales

public section

noncomputable section
namespace LooseHamilton.CoreCountBenchmark
open Filter

/-- Lemma 2.3 specialized uniformly to the core density window. The error has
coefficient one on the N/log N scale; only the threshold depends on r. -/
theorem eventually_core_benchmark (r : ℕ) (hr : 3 ≤ r) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (ell : Fin N → ℕ)
      (markers : Finset (Finset (Fin N))) (offset : ℝ),
      CoreAdmissible r m ell markers offset →
      |logarithmicBaseline r (ordinaryEdgeCount r markers) m markers -
        logarithmicBenchmark r N (ordinaryEdgeCount r markers) m| ≤
        (N:ℝ)/Real.log N := by
  have hr0 : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  obtain ⟨C,hC,hbenchmark⟩ := lemma23 r hr
  obtain ⟨N₀,hN₀⟩ := hbenchmark (1/(2*r)) (by positivity)
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop (1:ℕ),
    eventually_feasibility_parameters 0, eventually_marker_error_le C hC.le]
    with N hN hN1 hparam herr
  intro m ell markers offset hadm
  have hN0 : (0:ℝ)<N := by exact_mod_cast hN1
  have hd := hparam.2.1 (meanDegree (V:=Fin N) r m)
    (by simpa using hadm.density_window)
  simp only [meanDegree, Fintype.card_fin] at hd
  have hd' := (le_div_iff₀ hN0).mp hd
  have hl : 0 ≤ Real.log (N:ℝ) := le_trans (by norm_num) hparam.1
  have hden : (1/(2*(r:ℝ)))*(N:ℝ)*Real.log N ≤ m := by
    apply (mul_le_mul_iff_right₀ (show (0:ℝ)<2*r by positivity)).mp
    have he : 2*(r:ℝ)*((1/(2*r))*(N:ℝ)*Real.log N) = (N:ℝ)*Real.log N := by
      field_simp
    rw [he]
    nlinarith
  have hsize : N = (r-1)*ordinaryEdgeCount r markers+markers.card := by
    simpa only [Fintype.card_fin] using hadm.vertex_bookkeeping
  obtain ⟨F⟩ := hadm.feasible
  have hmK : m ≤ N.choose r := by simpa [completeEdges_card] using terminal_size_le F
  have hs : (markers.card:ℝ) ≤ (N:ℝ)^(1/10:ℝ) := by
    convert hadm.markers_small using 1 <;> simp only [Fintype.card_fin] <;> rfl
  have hb := hN₀ N hN (ordinaryEdgeCount r markers) markers.card m hsize
    hadm.markers_nonempty hs hden hmK markers hadm.marker_matching rfl
  exact hb.trans (herr markers.card hs)
end LooseHamilton.CoreCountBenchmark
