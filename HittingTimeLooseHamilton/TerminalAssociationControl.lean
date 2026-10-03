module

public import HittingTimeLooseHamilton.TerminalAssociationScales
public import HittingTimeLooseHamilton.TerminalAssociationTails
public import HittingTimeLooseHamilton.TerminalDegreeMixture
public import HittingTimeLooseHamilton.TerminalRegularityModels
public import HittingTimeLooseHamilton.TerminalFeasibilityScales

public section

/-! Uniform association control in the terminal law, by exact degree-sequence conditioning. -/
noncomputable section
namespace LooseHamilton
open Filter Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def terminalPairError (r n : ℕ) (C : ℝ) : ℝ :=
  (n:ℝ)^2*(4*(r:ℝ)*C^2*Real.log n/(n:ℝ))^3/6

@[expose] def terminalStarError (r n : ℕ) (C : ℝ) : ℝ :=
  (n:ℝ)*(4*(r:ℝ)*C^2*Real.log n*(n:ℝ)^(1/4:ℝ)/(n:ℝ))^2/2

lemma terminal_association_error_limits (r : ℕ) (C : ℝ) :
    Tendsto (fun n => terminalPairError r n C) atTop (nhds 0) ∧
    Tendsto (fun n => terminalStarError r n C) atTop (nhds 0) := by
  exact terminal_association_errors_tendsto_zero (4*(r:ℝ)*C^2)

lemma degreeMaximum_real_le {d : V → ℕ} {L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ v, (d v:ℝ) ≤ L) : (degreeMaximum d:ℝ) ≤ L := by
  classical
  by_cases h : Nonempty V
  · letI := h
    obtain ⟨v,_,hv⟩ := Finset.exists_mem_eq_sup (s := (univ : Finset V))
      (f := d) univ_nonempty
    simpa [degreeMaximum,hv] using hd v
  · haveI : IsEmpty V := not_nonempty_iff.mp h
    simp [degreeMaximum,hL]

/-- Explicit bounds on bad pairs and bad low-degree stars jointly with the established
maximum-degree and low-set controls. Both error terms converge to zero. -/
theorem terminal_association_control_eventually (r : ℕ) (hr : 3 ≤ r)
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V = n → ∀ (M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)],
    |meanDegree (V:=V) r M-Real.log n| ≤ 3*Real.log (Real.log n) →
    (terminalLaw r M ell).event (fun F =>
      TerminalDegreeControls C (vertexDegree F.val) ∧
      ∃ u v, u ≠ v ∧ 3 ≤ pairDegree F.val u v) ≤ terminalPairError r n C ∧
    (terminalLaw r M ell).event (fun F =>
      TerminalDegreeControls C (vertexDegree F.val) ∧
      ∃ y, 2 ≤ associationStatistic F.val y ((terminalLowVertices F.val).erase y)) ≤
        terminalStarError r n C := by
  classical
  filter_upwards [eventually_association_rate_bounds r hC,
    eventually_feasibility_parameters 0] with n hn hpar
  obtain ⟨hn0,hl,hn⟩ := hn
  intro V _ _ hcard M ell _ hden
  have hnreal : (0:ℝ)<n := by exact_mod_cast hn0
  have hmean := hpar.2.1 _ hden
  have hsum : (99/100:ℝ)*(n:ℝ)*Real.log n ≤ (r:ℝ)*M := by
    unfold meanDegree at hmean
    rw [hcard] at hmean
    have hh := (le_div_iff₀ hnreal).mp hmean
    nlinarith
  let G : (V → ℕ) → Prop := fun d => TerminalDegreeControls C d ∧ degreeSum d = M*r
  have hG (F : TerminalState V r M ell)
      (h : TerminalDegreeControls C (vertexDegree F.val)) : G (vertexDegree F.val) := by
    refine ⟨h,?_⟩
    dsimp [degreeSum]
    rw [sum_vertexDegree_eq F.property.1,F.property.2.1]
  have hpoint (d : V → ℕ) (hd : G d) :
      (99/100:ℝ)*(n:ℝ)*Real.log n ≤ degreeSum d ∧
      (degreeMaximum d:ℝ) ≤ C*Real.log n ∧
      ((terminalLowDegreeSet d).card:ℝ) ≤ (n:ℝ)^(1/4:ℝ) := by
    refine ⟨?_,?_,?_⟩
    · rw [hd.2]; push_cast; nlinarith
    · apply degreeMaximum_real_le (mul_nonneg hC hl.le)
      simpa [hcard] using hd.1.1
    · simpa [hcard] using hd.1.2
  have hp : 1 ≤ (n:ℝ)^(1/4:ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn0) (by norm_num)
  have hpair : ∀ d, G d → ∀ [Nonempty (FixedDegreeState V r d)],
      (fixedDegreeLaw r d).event (fun F => ∃u v,u≠v ∧ 3≤pairDegree F.val u v) ≤
        terminalPairError r n C := by
    intro d hd _
    obtain ⟨hs,hm,hb⟩ := hpoint d hd
    have hbnd (u v : V) (_huv : u≠v) :
        0 < associationSlack r d {v} ∧
        associationRate r d u {v} ≤ 4*(r:ℝ)*C^2*Real.log n/(n:ℝ) := by
      obtain ⟨hA,hR⟩ := hn V d hs hm {v} (by simpa using hp)
      exact ⟨hA,by simpa using hR u 1 (by norm_num) (by simp)⟩
    simpa [terminalPairError,hcard] using
      fixed_degree_pair_failure_le hr (by positivity) hbnd
  have hstar : ∀ d, G d → ∀ [Nonempty (FixedDegreeState V r d)],
      (fixedDegreeLaw r d).event (fun F => ∃ y,
        2≤associationStatistic F.val y ((terminalLowVertices F.val).erase y)) ≤
        terminalStarError r n C := by
    intro d hd _
    obtain ⟨hs,hm,hb⟩ := hpoint d hd
    have hbnd (y : V) : 0 < associationSlack r d ((terminalLowDegreeSet d).erase y) ∧
        associationRate r d y ((terminalLowDegreeSet d).erase y) ≤
          4*(r:ℝ)*C^2*Real.log n*(n:ℝ)^(1/4:ℝ)/(n:ℝ) := by
      have hB : (((terminalLowDegreeSet d).erase y).card:ℝ) ≤ (n:ℝ)^(1/4:ℝ) :=
        (Nat.cast_le.mpr (card_erase_le)).trans hb
      obtain ⟨hA,hR⟩ := hn V d hs hm _ hB
      exact ⟨hA,hR y _ (by positivity) hB⟩
    have ht := fixed_degree_star_failure_le hr (terminalLowDegreeSet d) (by positivity) hbnd
    simpa only [terminalLowVertices_fixedDegree,terminalStarError,hcard] using ht
  constructor
  · have ht := terminal_event_le_of_fixedDegrees r M (by omega) ell G
      (fun F => ∃u v,u≠v ∧ 3≤pairDegree F u v) (terminalPairError r n C)
      (by dsimp [terminalPairError]; positivity) hpair
    exact ((terminalLaw r M ell).event_mono (fun F h => ⟨hG F h.1,h.2⟩)).trans ht
  · have ht := terminal_event_le_of_fixedDegrees r M (by omega) ell G
      (fun F => ∃y,2≤associationStatistic F y ((terminalLowVertices F).erase y))
      (terminalStarError r n C) (by dsimp [terminalStarError]; positivity) hstar
    exact ((terminalLaw r M ell).event_mono (fun F h => ⟨hG F h.1,h.2⟩)).trans ht
end LooseHamilton
