module

public import HittingTimeLooseHamilton.FrameRemainderStaticEntropy
public import HittingTimeLooseHamilton.FramePersistenceScales

public section

/-! Static entropy errors are negligible compared with the full candidate scale. -/
noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- Every raw edge is an r-set on the actual active vertices. -/
lemma raw_card_le_active_choose (f : Frame r original) (H : SimpleHypergraph V) :
    f.m H ≤ f.n.choose r := by
  have hh := card_le_card (f.numberedEdges_uniform H)
  rw [f.numberedEdges_card (f.rawHost H) (fun e he => (mem_filter.mp he).2),
    completeEdges_card,Fintype.card_fin] at hh
  exact hh
end LooseHamilton.AuxiliaryFrame.Frame

namespace LooseHamilton.FrameScales
open Filter Topology

/-- The implied entropy constant is absorbed before any finite frame data.
The tolerance is exactly alpha/4, used for remainder abnormality. -/
lemma eventually_remainder_entropy_factor (K R : ℝ) (hR : 0 < R) :
    ∀ᶠ N in atTop,
      K/((alpha N/4)*Real.sqrt (L2 N)) ≤ alpha N*R/8 := by
  have ht := (static_error_div_alpha_power 1).const_mul (4*K)
  simp only [Real.rpow_one,mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ)<R/8 by positivity)),
    eventual_range] with N hh hN
  have hh' : (K/((alpha N/4)*Real.sqrt (L2 N)))/alpha N ≤ R/8 := by
    convert hh.le using 1 <;> ring
  have hh'' := (div_le_iff₀ hN.2.2.2.1).mp hh'
  nlinarith only [hh'']
end LooseHamilton.FrameScales
