module

public import HittingTimeLooseHamilton.FrameEntropyRate
public import HittingTimeLooseHamilton.FrameEntropyBridgeProportion

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Filter

/-- Actual remainder data with the preserved quarter-logarithmic density. -/
structure RemainderEntropyInput (r : ℕ) (C B : ℝ) (N : ℕ) where
  original : Finset (Finset (Fin N))
  frame : AuxiliaryFrame.Frame r original
  host : SimpleHypergraph (Fin N)
  budget : frame.entropyBudget host B
  markers_small : (original.card:ℝ) ≤ (N:ℝ)^(1/10:ℝ)
  density : Real.log N/4 ≤ frame.mu host
  regular : PathGraphUpperRegular r C 6 (frame.entropyInstance host budget.1).host

/-- The remainder entropy rate has a threshold before every finite frame input
and every positive tolerance, not a threshold depending on a chosen sequence. -/
theorem remainder_entropyInstance_uniform_rate (r : ℕ) (hr : 3≤r)
    (C B : ℝ) (hC : 0<C) (hB : 0≤B) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ d : RemainderEntropyInput r C B N, ∀ t : ℝ, 0<t →
        (d.frame.entropyInstance d.host d.budget.1).exceptionalProportion t ≤
          K/(t*Real.sqrt (Real.log (Real.log (N:ℝ)))) := by
  classical
  obtain ⟨K,hK,hseq⟩ := entropyInstance_exceptional_rate r hr C B 6 hC hB le_rfl
  refine ⟨K,hK,?_⟩
  by_contra hbad
  have hbad' : ∀ i : ℕ, ∃ N : ℕ, i≤N ∧
      ∃ d : RemainderEntropyInput r C B N, ∃ t : ℝ, 0<t ∧
        ¬ (d.frame.entropyInstance d.host d.budget.1).exceptionalProportion t ≤
          K/(t*Real.sqrt (Real.log (Real.log (N:ℝ)))) := by
    simpa only [eventually_atTop, not_exists, not_forall, not_le, Classical.not_imp,
      exists_prop] using hbad
  choose N hN d t ht hfail using hbad'
  have hNt : Tendsto N atTop atTop := tendsto_atTop_mono hN tendsto_id
  have hmu : Tendsto (fun i => (d i).frame.mu (d i).host) atTop atTop := by
    apply tendsto_atTop_mono (fun i => (d i).density)
    exact (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hNt)).atTop_div_const
      (by norm_num : (0:ℝ)<4)
  have hh := hseq N hNt (fun i => (d i).original) (fun i => (d i).frame)
    (fun i => (d i).host) (fun i => (d i).budget) hmu
    (Eventually.of_forall (fun i => (d i).markers_small))
    (Eventually.of_forall (fun i => (d i).regular))
  obtain ⟨i,hi⟩ := hh.exists
  exact hfail i (hi (t i) (ht i))


/-- The actual abnormal existing candidate count, with a common threshold for
all frames and tolerances. The strict test uses Y/(X/((r-1)^2 mu)). -/
theorem remainder_existingExceptional_uniform_rate (r : ℕ) (hr : 3≤r)
    (C B : ℝ) (hC : 0<C) (hB : 0≤B) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ d : RemainderEntropyInput r C B N, ∀ t : ℝ, 0<t →
        ((d.frame.existingExceptional d.host t).card:ℝ) ≤
          K*(d.frame.m d.host:ℝ)/(t*Real.sqrt (Real.log (Real.log (N:ℝ)))) := by
  obtain ⟨K,hK,he⟩ := remainder_entropyInstance_uniform_rate r hr C B hC hB
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
