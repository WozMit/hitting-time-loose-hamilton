module

public import HittingTimeLooseHamilton.BootstrapNestedMeans
public import HittingTimeLooseHamilton.FrameRestrictedBudget

public section

/-! Exact frame normalization and the favorable comparison to the unfiltered
outer host, on the same active vertex set. No entropy assumption is needed. -/
noncomputable section
set_option maxHeartbeats 800000
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset BootstrapMeans
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

theorem mu_eq_filtered_inducedMean (F : Frame r M) (H : SimpleHypergraph V) :
    F.mu H = inducedMean r (H ∩ allowedEdges r (originalPorts M)) F.active := by
  simp only [mu, m, n, rawHost, inducedMean, meanDegree, Fintype.card_coe,
    induced_card_filter]

theorem mu_le_outer_inducedMean (F : Frame r M) (H : SimpleHypergraph V) :
    F.mu H ≤ inducedMean r H F.active := by
  have hsub : F.rawHost H ⊆ H.filter (fun e => e ⊆ F.active) := by
    intro e he
    obtain ⟨he,hs⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨(mem_inter.mp he).1,hs⟩
  simp only [mu, m, n, inducedMean, meanDegree, Fintype.card_coe, induced_card_filter]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hsub)) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

theorem mu_pos_of_cycleCount_pos (F : Frame r M) (hr : 3 ≤ r)
    (H : SimpleHypergraph V) (hW : 0 < F.cycleCount H) : 0 < F.mu H :=
  F.mu_pos_of_cycleFamily_nonempty hr H (card_pos.mp (show 0 < (F.cycleFamily H).card from hW))

end LooseHamilton.AuxiliaryFrame.Frame
