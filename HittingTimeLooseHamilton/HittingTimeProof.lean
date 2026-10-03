module

public import HittingTimeLooseHamilton.HittingTimeFinite
public import HittingTimeLooseHamilton.HittingTimeLimit

public section

/-! Theorem 1.1: the loose-Hamilton hitting-time assertion for every fixed r>=3.
All stopping, exposure, conditional core and expansion inputs are discharged. -/
noncomputable section
namespace LooseHamilton.HittingTimeConclusion
open Filter

theorem hitting_time_epsilon (r : ℕ) (hr : 3 ≤ r) : Statement r := by
  intro ε hε
  obtain ⟨Ncore,hcore⟩ := HittingTimeCore.terminal_zero_count_probability r hr
    ((2*(r-2) : ℕ)+2) (by positivity) (ε/2) (by positivity)
  obtain ⟨Nbase,hNbase⟩ := eventually_atTop.mp lowerDegreeBase_eventually_pos
  obtain ⟨Nprob,hNprob⟩ := Metric.tendsto_atTop.mp
    (good_event_probability_tendsto_one r hr) (ε/2) (by positivity)
  refine ⟨max 1 (max (r*Ncore) (max Nbase Nprob)),?_⟩
  intro n hn hdiv
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnrest := (le_max_right _ _).trans hn
  have hsize : r*Ncore ≤ n := (le_max_left _ _).trans hnrest
  have hnrest' := (le_max_right _ _).trans hnrest
  have hb : Nbase ≤ n := (le_max_left _ _).trans hnrest'
  have hp : Nprob ≤ n := (le_max_right _ _).trans hnrest'
  have hdist := hNprob n hp
  rw [Real.dist_eq] at hdist
  have hgood := (abs_lt.mp hdist).1
  have hfail := finite_probability_bound r n Ncore hr (by omega) hdiv
    (hNbase n hb) hsize (ε/2) (by positivity) hcore
  rw [FiniteEntropy.Law.event_compl,FiniteEntropy.Law.event_compl] at hfail
  change 1-ε ≤ (processLaw (Fin n) r).event hittingTimeEvent
  linarith

end LooseHamilton.HittingTimeConclusion

namespace LooseHamilton

/-- Theorem 1.1: in the ordinary random r-graph process, with probability
tending to one the first loose Hamilton cycle appears when the last isolated
vertex disappears, as n tends to infinity through multiples of r-1. -/
theorem theorem11 : Theorem11 := by
  intro r hr
  exact HittingTimeConclusion.limit_of_statement hr
    (HittingTimeConclusion.hitting_time_epsilon r hr)

end LooseHamilton
