module

public import HittingTimeLooseHamilton.RootTestRegistry
public import HittingTimeLooseHamilton.RootFreeTestIndexing

public section

/-! Simultaneous root tests on the concrete polynomial label universe.
Each registry is fixed before observing the random path. The threshold is
uniform over every such registry; it is not a union over all registries. -/
noncomputable section
namespace LooseHamilton
open Filter Finset RootFreeTestIndexing

theorem uniform_common_root_whp (r : ℕ) (hr : 3 ≤ r)
    (c : ℝ) (hc : 0 < c) (h : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, ∀ ell : Fin N → ℕ,
      [Nonempty (TerminalState (Fin N) r M ell)] →
      ∀ original : Finset (Finset (Fin N)),
      ∀ tests : RootTestIndex r original → RegisteredRootTest (Fin N) r h,
      (extensionLaw r M ell).event (fun ω => ¬ CommonRootTests tests M ell c ω) ≤ ε := by
  have he := (FrameScales.root_tail_tendsto_zero (16*r+42)
    (by positivity : 0 < c/6400)).eventually (gt_mem_nhds hε)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    ((registered_root_union_eventually hr hc h).and (he.and (eventually_ge_atTop 2)))
  refine ⟨N₀,?_⟩
  intro N hN M ell _ original tests
  obtain ⟨hbound,herror,hlarge⟩ := hN₀ N hN
  have hb := hbound (Fin N) (Fintype.card_fin N) M ell (RootTestIndex r original) tests
  have hcard : (Fintype.card (RootTestIndex r original) : ℝ) ≤ (N : ℝ)^(16*r+42) := by
    have hn : Fintype.card (RootTestIndex r original) ≤ N^(16*r+42) := by
      simpa only [Fintype.card_fin] using
        root_test_index_card_le r original (by simpa using hlarge)
    exact_mod_cast hn
  exact (hb.trans (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le)).trans herror.le

end LooseHamilton
