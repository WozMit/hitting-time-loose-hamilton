module

public import HittingTimeLooseHamilton.BootstrapActualTests
public import HittingTimeLooseHamilton.RegistryAdaptive
public import HittingTimeLooseHamilton.CommonRootEvent
public import HittingTimeLooseHamilton.RootEventGoodLinks

public section

/-! # Probability and adaptive selection for the concrete bootstrap catalogue
Only the fixed geometric labels are union-bounded. Threshold constants are
fixed before sampling; degree, deficit and density remain application gates.
-/
noncomputable section
namespace LooseHamilton.BootstrapCatalogue
open Finset Filter

/-- Uniform high-probability success of the actual fixed catalogue, using its
sharp N^(4r+5) size bound. This does not assert the density gate itself. -/
theorem common_tests_whp (r : ℕ) (hr : 3 ≤ r) (cRoot : ℝ) (hc : 0 < cRoot)
    (h : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, ∀ ell : Fin N → ℕ,
      [Nonempty (TerminalState (Fin N) r M ell)] →
      ∀ original : Finset (Finset (Fin N)), ∀ hM : IsPairMatching original,
      ∀ cP cE cPort : ℝ,
      (extensionLaw r M ell).event (fun ω =>
        ¬ CommonRootTests (tests (h := h) hM cP cE cPort) M ell cRoot ω) ≤ ε := by
  have he := (FrameScales.root_tail_tendsto_zero (4*r+5)
    (by positivity : 0 < cRoot/6400)).eventually (gt_mem_nhds hε)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    ((registered_root_union_eventually hr hc h).and (he.and (eventually_ge_atTop 2)))
  refine ⟨N₀,?_⟩
  intro N hN M ell _ original hM cP cE cPort
  obtain ⟨hbound,herror,hlarge⟩ := hN₀ N hN
  have hb := hbound (Fin N) (Fintype.card_fin N) M ell (Index r original)
    (tests hM cP cE cPort)
  have hcard : (Fintype.card (Index r original) : ℝ) ≤ (N : ℝ)^(4*r+5) := by
    have hn : Fintype.card (Index r original) ≤ N^(4*r+5) := by
      simpa only [Fintype.card_fin] using index_card_le hr hM (by simpa using hlarge)
    exact_mod_cast hn
  exact (hb.trans (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le)).trans herror.le

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A label may be selected from the entire observed outcome. Prescriptions
are empty; the ambient time/deficit/degree/density gates remain explicit. -/
theorem selected_not_bad {r h M : ℕ} {ell : V → ℕ}
    {original : Finset (Finset V)} (hM : IsPairMatching original)
    (cP cE cPort cRoot : ℝ)
    (select : (TerminalState V r M ell × MissingOrder V r M) → Index r original)
    (ω : TerminalState V r M ell × MissingOrder V r M)
    (hω : CommonRootTests (tests (h := h) hM cP cE cPort) M ell cRoot ω)
    (ht : M ≤ (select ω).2.val ∧ (select ω).2.val ≤ (completeEdges V r).card)
    (hdef : (∑ v, rootAdjustedDeficit (root (select ω).1) ell
      (rootFreePairObservation r M ell (select ω).2.val (root (select ω).1) ω).1 v) ≤ 1)
    (hdeg : cRoot * FrameScales.L1 (Fintype.card V) ≤
      (((select ω).2.val - (rootFreePairObservation r M ell (select ω).2.val
        (root (select ω).1) ω).2.card : ℕ) : ℝ))
    (hdens : rootLinkDensity r (root (select ω).1)
      ((tests (h := h) hM cP cE cPort (select ω)).badSet
        (rootFreePairObservation r M ell (select ω).2.val (root (select ω).1) ω)) ≤
      FrameScales.rho (Fintype.card V)) :
    ¬ RootLinkBad ((tests (h := h) hM cP cE cPort (select ω)).badSet
      (rootFreePairObservation r M ell (select ω).2.val (root (select ω).1) ω))
      ((select ω).2.val - (rootFreePairObservation r M ell (select ω).2.val
        (root (select ω).1) ω).2.card)
      (rootSamplingPair r M ell (select ω).2.val ω) := by
  have hn := hω (select ω)
  have hp := (tests (h := h) hM cP cE cPort (select ω)).not_bad_on_gates
    cRoot ω hn
  simpa only [tests_time, tests_root, tests_prescribed, empty_subset] using
    hp (by simpa using ht) (by simp) (by simpa using hdef)
      (by simpa using hdeg) (by simpa using hdens)

end LooseHamilton.BootstrapCatalogue
