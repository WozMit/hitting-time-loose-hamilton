module

public import HittingTimeLooseHamilton.Cycles
public import HittingTimeLooseHamilton.Models
public import HittingTimeLooseHamilton.HittingTime
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

/-! # Section 1 setup for the loose-Hamilton manuscript

`CoreAdmissible` records the finite parameter conditions, with an explicit bound
on the degree offsets. In an asymptotic application this bound and `r` are fixed
while the vertex count tends to infinity. No high-probability claim is made here.
-/
noncomputable section
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A simple matching of prescribed unordered pairs. -/
@[expose] def IsPairMatching (markers : Finset (Finset V)) : Prop :=
  (∀ e ∈ markers, e.card = 2) ∧ (markers : Set (Finset V)).PairwiseDisjoint id

/-- The original port set contains exactly two vertices per marked pair. -/
theorem IsPairMatching.ports_card {markers : Finset (Finset V)}
    (h : IsPairMatching markers) : (originalPorts markers).card = 2 * markers.card := by
  classical
  unfold originalPorts
  rw [Finset.card_biUnion h.2]
  calc
    ∑ e ∈ markers, e.card = ∑ _e ∈ markers, 2 := Finset.sum_congr rfl h.1
    _ = 2 * markers.card := by simp [Nat.mul_comm]

/-- Disjoint marked pairs cannot use more vertices than the host has. -/
theorem IsPairMatching.twice_card_le {markers : Finset (Finset V)}
    (h : IsPairMatching markers) : 2 * markers.card ≤ Fintype.card V := by
  rw [← h.ports_card]
  exact Finset.card_le_card (Finset.subset_univ _)

/-- The small degree-threshold constant fixed by the manuscript. -/
@[expose] def epsilon : ℝ := 1 / 100

/-- Mean vertex degree of an r-uniform host with M edges on V. -/
@[expose] def meanDegree (r M : ℕ) : ℝ := (r : ℝ) * M / Fintype.card V

/-- Baseline for the terminal degree lower bounds. -/
@[expose] def lowerDegreeBase (V : Type*) [Fintype V] : ℕ :=
  Nat.floor (epsilon * Real.log (Fintype.card V : ℝ))

/-- The number k of ordinary edges in a spanning mixed cycle. -/
@[expose] def ordinaryEdgeCount (r : ℕ) (markers : Finset (Finset V)) : ℕ :=
  (Fintype.card V - markers.card) / (r - 1)

/-- Explicit finite form of the conditioned-core parameter assumptions.
`offsetBound` encodes the bounded offsets in ell_v; it must be fixed in a
subsequent asymptotic statement, not chosen anew without a uniform bound. -/
structure CoreAdmissible (r M : ℕ) (ell : V → ℕ)
    (markers : Finset (Finset V)) (offsetBound : ℝ) : Prop where
  uniformity : 3 ≤ r
  marker_matching : IsPairMatching markers
  markers_nonempty : 1 ≤ markers.card
  markers_small : (markers.card : ℝ) ≤ Real.rpow (Fintype.card V : ℝ) (1 / 10)
  divisibility : r - 1 ∣ Fintype.card V - markers.card
  density_window : |meanDegree (V := V) r M - Real.log (Fintype.card V : ℝ)| ≤
    3 * Real.log (Real.log (Fintype.card V : ℝ))
  offset_nonneg : 0 ≤ offsetBound
  offsets : ∀ v, |(ell v : ℝ) - lowerDegreeBase V| ≤ offsetBound
  feasible : Nonempty (TerminalState V r M ell)

/-- The admissible divisibility condition gives the manuscript's exact vertex
bookkeeping even before a cycle is chosen. -/
theorem CoreAdmissible.vertex_bookkeeping {r M : ℕ} {ell : V → ℕ}
    {markers : Finset (Finset V)} {offsetBound : ℝ}
    (h : CoreAdmissible r M ell markers offsetBound) :
    Fintype.card V = (r - 1) * ordinaryEdgeCount r markers + markers.card := by
  have hs : markers.card ≤ Fintype.card V := by
    have := h.marker_matching.twice_card_le
    omega
  unfold ordinaryEdgeCount
  rw [Nat.mul_div_cancel' h.divisibility, Nat.sub_add_cancel hs]

/-- No isolated vertex: the necessary minimum-degree-one condition. -/
@[expose] def NoIsolated (host : SimpleHypergraph V) : Prop :=
  ∀ v : V, 1 ≤ vertexDegree host v

/-- A loose Hamilton cycle is a spanning mixed cycle with no marked pairs. -/
@[expose] def HasLooseHamiltonCycle (r : ℕ) (host : SimpleHypergraph V) : Prop :=
  ∃ edges : Finset (Finset V), edges ⊆ host ∧ IsMixedCycle r ∅ edges

/-- Adding host edges preserves the existence of a loose Hamilton cycle. -/
theorem hasLooseHamiltonCycle_mono {r : ℕ} {G H : SimpleHypergraph V}
    (hGH : G ⊆ H) (h : HasLooseHamiltonCycle r G) : HasLooseHamiltonCycle r H := by
  obtain ⟨C, hC, hc⟩ := h
  exact ⟨C, hC.trans hGH, hc⟩

/-- Spanning loose cycles have no isolated vertices, directly from their cover. -/
theorem HasLooseHamiltonCycle.noIsolated {r : ℕ} {host : SimpleHypergraph V}
    (h : HasLooseHamiltonCycle r host) : NoIsolated host := by
  obtain ⟨C, hsub, hC⟩ := h
  intro v
  obtain ⟨e, he, hv⟩ := hC.covers v
  have heC : e ∈ C := by simpa using he
  exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨hsub heC, hv⟩⟩

/-- The time at which the last isolated vertex disappears, infinity if absent. -/
@[expose] def tauOne {r : ℕ} (σ : EdgeOrder V r) : WithTop ℕ :=
  firstTime (completeEdges V r).card (processState σ) NoIsolated

/-- The first loose-Hamilton time, infinity if the process never has a cycle. -/
@[expose] def tauLooseHamilton {r : ℕ} (σ : EdgeOrder V r) : WithTop ℕ :=
  firstTime (completeEdges V r).card (processState σ) (HasLooseHamiltonCycle r)

/-- The deterministic necessary hitting-time inequality from Section 1. -/
theorem tauOne_le_tauLooseHamilton {r : ℕ} (σ : EdgeOrder V r) :
    tauOne σ ≤ tauLooseHamilton σ := by
  apply firstTime_le_of_imp
  intro t _ ht
  exact ht.noIsolated

/-- The event whose asymptotic probability is the target of Theorem 1.1.
This definition does not assert the hitting-time theorem. -/
@[expose] def hittingTimeEvent {r : ℕ} (σ : EdgeOrder V r) : Prop :=
  tauLooseHamilton σ = tauOne σ

/-- Probability of the hitting-time event in the ordinary random process. -/
@[expose] def hittingTimeProbability (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) : ℝ :=
  (processLaw V r).event hittingTimeEvent

theorem hittingTimeProbability_nonneg (r : ℕ) :
    0 ≤ hittingTimeProbability V r := (processLaw V r).event_nonneg _

theorem hittingTimeProbability_le_one (r : ℕ) :
    hittingTimeProbability V r ≤ 1 := (processLaw V r).event_le_one _

end LooseHamilton
