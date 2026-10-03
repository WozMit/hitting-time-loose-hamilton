module

public import HittingTimeLooseHamilton.FrameSurvivalConcentration

public section

/-! A convenient fixed relative tolerance after absorbing the boundary bias. -/
noncomputable section
namespace FiniteEntropy.Law
variable {Ω : Type*} [Fintype Ω]

/-- Absorb a deterministic bias at most one quarter of the requested tolerance.
The input is the true-mean Chebyshev bound at one quarter tolerance, so the
loss in probability is exactly the factor sixteen. -/
theorem absorb_relative_bias (p : FiniteEntropy.Law Ω) (X : Ω → ℝ)
    {A δ L h K : ℝ} (hA : 0 ≤ A) (hh : 0 < h)
    (hbias : δ ≤ h/4) (hL : L ≤ 2)
    (hbound : p.event (fun ω => (δ+(h/4)*L)*A < |X ω-A|) ≤ K/(h/4)^2) :
    p.event (fun ω => h*A < |X ω-A|) ≤ 16*K/h^2 := by
  have ht : δ+(h/4)*L ≤ h := by
    have hx := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ h/4)
    nlinarith
  have he : p.event (fun ω => h*A < |X ω-A|) ≤
      p.event (fun ω => (δ+(h/4)*L)*A < |X ω-A|) := by
    apply p.event_mono
    intro ω hω
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right ht hA) hω
  calc
    _ ≤ K/(h/4)^2 := he.trans hbound
    _ = 16*K/h^2 := by ring

end FiniteEntropy.Law
