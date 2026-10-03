module

public import HittingTimeLooseHamilton.CoreConditionalCounting

public section

/-! Conditioning costs at most the reciprocal of the conditioning probability.
The estimate applies to arbitrary path events, so it does not require the
stopping rule to observe the terminal conditioning event. -/
noncomputable section
namespace LooseHamilton.StoppedCounting

theorem conditional_event_le {Ω : Type*} [Fintype Ω]
    (p : FiniteEntropy.Law Ω) (L E : Ω → Prop) (hL : 0 < p.event L) :
    (p.condition L hL).event E ≤ (p.event L)⁻¹ * p.event E := by
  rw [LooseHamilton.condition_event_eq_joint]
  calc
    p.event (fun ω => L ω ∧ E ω) / p.event L ≤ p.event E / p.event L :=
      div_le_div_of_nonneg_right (p.event_mono (fun _ h => h.2)) hL.le
    _ = (p.event L)⁻¹ * p.event E := by ring

theorem conditional_event_bound {Ω : Type*} [Fintype Ω]
    (p : FiniteEntropy.Law Ω) (L E : Ω → Prop) (hL : 0 < p.event L)
    {B : ℝ} (hB : p.event E ≤ B) :
    (p.condition L hL).event E ≤ (p.event L)⁻¹ * B :=
  (conditional_event_le p L E hL).trans
    (mul_le_mul_of_nonneg_left hB (inv_nonneg.mpr hL.le))

end LooseHamilton.StoppedCounting
