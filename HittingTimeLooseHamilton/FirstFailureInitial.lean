module

public import HittingTimeLooseHamilton.Enumeration
public import HittingTimeLooseHamilton.NormalizationFactorials
public import HittingTimeLooseHamilton.ProhibitionBound
public import HittingTimeLooseHamilton.BenchmarkRange

public section

noncomputable section
namespace LooseHamilton.FirstFailure
open Filter

theorem complete_count_pos {N r k : ℕ} (hr : 3 ≤ r)
    (M : Finset (Finset (Fin N))) (hM : IsPairMatching M)
    (hs : 1 ≤ M.card) (hk : 3 ≤ k) (hsk : 2*M.card ≤ k)
    (hN : N = (r-1)*k+M.card) :
    0 < cycleCount r M (completeEdges (Fin N) r) (originalPorts M) := by
  obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0 < M.card by omega)
  have hn : Fintype.card (Fin N) = (r-1)*k+M.card := by simpa using hN
  have hc := allowedHost_count hr hM he hk hsk hn
  rw [completeHost_count hr hM he hk (by omega) hn] at hc
  have hpos : (0 : ℝ) < cycleCount r M (completeEdges (Fin N) r) (originalPorts M) := by
    rw [hc]
    exact mul_pos (Nat.cast_pos.mpr (completeHostFormula_pos hr (by omega) hn))
      (prohibitionRatio_pos _ _)
  exact_mod_cast hpos

theorem eventually_complete_count_pos (r : ℕ) (hr : 3 ≤ r) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (ell : Fin N → ℕ)
      (M : Finset (Finset (Fin N))) (offset : ℝ),
      CoreAdmissible r m ell M offset →
        0 < cycleCount r M (completeEdges (Fin N) r) (originalPorts M) := by
  obtain ⟨N₀,hN₀⟩ := benchmark_range_eventually r hr 1 (by norm_num)
  filter_upwards [eventually_ge_atTop N₀] with N hN
  intro m ell M offset hadm
  have hn : N = (r-1)*ordinaryEdgeCount r M+M.card := by
    simpa using hadm.vertex_bookkeeping
  have hceil : (1 : ℝ)*N*Real.log N ≤ Nat.ceil ((N:ℝ)*Real.log N) := by
    simpa using (Nat.le_ceil ((N:ℝ)*Real.log N))
  have hh := hN₀ N hN (ordinaryEdgeCount r M) M.card
    (Nat.ceil ((N:ℝ)*Real.log N)) hn hadm.markers_nonempty
    (by simpa using hadm.markers_small) hceil
  exact complete_count_pos hr M hadm.marker_matching hadm.markers_nonempty hh.2.1 hh.2.2.1 hn

end LooseHamilton.FirstFailure
