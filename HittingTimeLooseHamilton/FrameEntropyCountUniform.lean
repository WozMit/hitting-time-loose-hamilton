module

public import HittingTimeLooseHamilton.FrameEntropyUniform
public import HittingTimeLooseHamilton.FrameEntropyBridgeProportion

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Filter

/-- The actual abnormal existing candidate count, with a common threshold for
all frames and tolerances. The strict test uses Y/(X/((r-1)^2 mu)). -/
theorem existingExceptional_uniform_rate (r : ℕ) (hr : 3≤r)
    (C B : ℝ) (hC : 0<C) (hB : 0≤B) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ d : EntropyFrameInput r C B N, ∀ t : ℝ, 0<t →
        ((d.frame.existingExceptional d.host t).card:ℝ) ≤
          K*(d.frame.m d.host:ℝ)/(t*Real.sqrt (Real.log (Real.log (N:ℝ)))) := by
  obtain ⟨K,hK,he⟩ := entropyInstance_uniform_rate r hr C B hC hB
  have hrp : (0:ℝ)<(r*(r-1):ℕ) := by exact_mod_cast (show 0<r*(r-1) by exact Nat.mul_pos (by omega) (by omega))
  refine ⟨K*(r*(r-1):ℕ),mul_pos hK hrp,?_⟩
  filter_upwards [he] with N hN d t ht
  have hp := hN d t ht
  rw [d.frame.entropyInstance_exceptionalProportion hr d.host d.budget.1 t] at hp
  have hq : 0≤K/(t*Real.sqrt (Real.log (Real.log (N:ℝ)))) := by positivity
  have hc := d.frame.existingExceptional_count_of_proportion (by omega) d.host t
    (K/(t*Real.sqrt (Real.log (Real.log (N:ℝ))))) hq hp
  convert hc using 1 <;> ring
end LooseHamilton.AuxiliaryFrame.Frame
