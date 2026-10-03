module

public import HittingTimeLooseHamilton.ExceptionalSetReduction
public import HittingTimeLooseHamilton.IsolationLimitTransfer
public import HittingTimeLooseHamilton.WindowIsolationAsymptotics

public section

/-! The stopping-window failure is controlled by the early and late tails of
the original random edge-order process. -/
noncomputable section
namespace LooseHamilton
open Finset Filter
open scoped Topology
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

/-- The two tails cover failure of the closed stopping window. Including the
lower boundary in the early tail only enlarges this upper bound. -/
theorem exceptional_stopping_window_probability_le (C : ℝ) (lo hi : ℕ) :
    (processLaw V r).event (exceptionalFailure C lo hi 0) ≤
      (processLaw V r).event (fun σ => tauOne σ ≤ (lo : WithTop ℕ)) +
      (processLaw V r).event (fun σ => (hi : WithTop ℕ) < tauOne σ) := by
  let E : Bool → EdgeOrder V r → Prop := fun b σ =>
    if b then (hi : WithTop ℕ) < tauOne σ else tauOne σ ≤ (lo : WithTop ℕ)
  have hcover : ∀ σ : EdgeOrder V r, exceptionalFailure C lo hi 0 σ → ∃ b, E b σ := by
    intro σ hbad
    by_cases he : tauOne σ ≤ (lo : WithTop ℕ)
    · exact ⟨false,he⟩
    by_cases hl : (hi : WithTop ℕ) < tauOne σ
    · exact ⟨true,hl⟩
    have hhi : tauOne σ ≤ (hi : WithTop ℕ) := le_of_not_gt hl
    have hfinite : tauOne σ ≠ ⊤ := by
      intro htop
      rw [htop] at hhi
      exact (WithTop.coe_ne_top : (hi : WithTop ℕ) ≠ ⊤) (top_le_iff.mp hhi)
    obtain ⟨k,hk⟩ := WithTop.ne_top_iff_exists.mp hfinite
    have hlo : (lo : WithTop ℕ) < tauOne σ := lt_of_not_ge he
    rw [← hk] at hlo hhi
    exact False.elim (hbad ⟨k,hk.symm,(WithTop.coe_lt_coe.mp hlo).le,WithTop.coe_le_coe.mp hhi⟩)
  calc
    _ ≤ (processLaw V r).event (fun σ => ∃ b, E b σ) := (processLaw V r).event_mono hcover
    _ ≤ ∑ b : Bool, (processLaw V r).event (E b) := (processLaw V r).finite_union_bound E
    _ = _ := by simp [E,add_comm]

/-- Vanishing early and late tails yield vanishing probability of the exact
window failure used in the exceptional-set reduction. -/
theorem exceptional_stopping_window_tendsto (C : ℝ) (lo hi : ℕ → ℕ)
    (hearly : Tendsto (fun n => (processLaw (Fin n) r).event
      (fun σ => tauOne σ ≤ (lo n : WithTop ℕ))) atTop (𝓝 0))
    (hlate : Tendsto (fun n => (processLaw (Fin n) r).event
      (fun σ => (hi n : WithTop ℕ) < tauOne σ)) atTop (𝓝 0)) :
    Tendsto (fun n => (processLaw (Fin n) r).event
      (exceptionalFailure C (lo n) (hi n) 0)) atTop (𝓝 0) := by
  have hsum := hearly.add hlate
  simp only [add_zero] at hsum
  exact squeeze_zero' (Eventually.of_forall (fun n => (processLaw (Fin n) r).event_nonneg _))
    (Eventually.of_forall (fun n => exceptional_stopping_window_probability_le C (lo n) (hi n))) hsum

/-- Numerical isolation estimates suffice for the exact stopping-window error.
All probability statements here use the original complete-edge ordering law. -/
theorem exceptional_stopping_window_tendsto_of_scalar {r : ℕ} (hr : 2 ≤ r)
    (C : ℝ) (lo hi : ℕ → ℕ)
    (hgap : ∀ᶠ n in atTop, lo n + (n-1).choose (r-1) < n.choose r)
    (hhi : ∀ᶠ n in atTop, hi n ≤ n.choose r)
    (hfirst : Tendsto (fun n => Real.exp (isolationLowerExponent (Fin n) r (lo n))/(n : ℝ)) atTop (𝓝 0))
    (hpair : Tendsto (fun n => 2*isolationLowerExponent (Fin n) r (lo n) -
      isolationPairExponent (Fin n) r (lo n)) atTop (𝓝 0))
    (hlate : Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(((n-1).choose (r-1) : ℝ) * hi n /
      (n.choose r : ℝ)))) atTop (𝓝 0)) :
    Tendsto (fun n => (processLaw (Fin n) r).event
      (exceptionalFailure C (lo n) (hi n) 0)) atTop (𝓝 0) := by
  apply exceptional_stopping_window_tendsto C lo hi
  · exact tauOne_early_probability_tendsto hr lo hgap hfirst hpair
  · exact tauOne_late_probability_tendsto (by omega) hi hhi hlate
/-- The concrete 0.99/1.01 logarithmic window contains the stopping time with
probability tending to one, expressed as the exact failure-zero estimate. -/
theorem exceptional_stopping_failure_tendsto_zero {r : ℕ} (hr : 3 ≤ r) (C : ℝ) :
    Tendsto (fun n => (processLaw (Fin n) r).event
      (exceptionalFailure C (exceptionalWindowLo r n) (exceptionalWindowHi r n) 0))
      atTop (𝓝 0) := by
  apply exceptional_stopping_window_tendsto_of_scalar (by omega : 2 ≤ r)
    C (exceptionalWindowLo r) (exceptionalWindowHi r)
  · exact exceptionalWindowLo_gap_eventually hr
  · filter_upwards [exceptionalWindow_times_le_complete_eventually hr] with n hn
    exact hn.2
  · exact exceptionalWindowLo_exp_tendsto_zero hr
  · exact exceptionalWindowLo_pair_correction_tendsto_zero hr
  · exact exceptionalWindowHi_exp_tendsto_zero hr
end LooseHamilton
