module

public import HittingTimeLooseHamilton.FrameEntropyInheritedRegularity
public import HittingTimeLooseHamilton.FrameConditionalCompletionRemainder
public import HittingTimeLooseHamilton.CandidateBatchRegularity
public import HittingTimeLooseHamilton.FrameSamplingRefined

public section

/-! Regularity is a property of the actual numbered raw host, independent of
whether the surviving cycle family has already been shown nonempty. -/
noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r M : ℕ} {ell : V → ℕ} {original : Finset (Finset V)}

lemma numbered_rawHost_mean (F : Frame r original) (H : SimpleHypergraph V) :
    meanDegree (V:=Fin F.n) r (F.numberedEdges (F.rawHost H)).card=F.mu H := by
  rw [F.numberedEdges_card (F.rawHost H) (fun e he => (mem_filter.mp he).2)]
  simp [meanDegree, mu, m]

/-- No cycle-existence premise is needed for inherited raw-host regularity. -/
theorem numbered_rawHost_inherited_regular (F : Frame r original)
    (j h : ℕ) (c C L : ℝ) (ω : CandidateBalance.Outcome V r M ell)
    (hh : 4*r≤h)
    (hreg : CandidateBalance.InheritedRegularity original j h c C L ω) :
    PathGraphUpperRegular r C L (F.numberedEdges (F.rawHost (extensionState ω.1 ω.2 j))) := by
  have hs := hreg.2.2.2 F.val.deleted (F.val.deleted_card_le.trans hh)
  change PathGraphUpperRegular r C L
    (fixedPortHost (inducedHost F.active (extensionState ω.1 ω.2 j))
      (restrictedPorts F.active (originalPorts original))) at hs
  rw [←F.restrict_rawHost_eq_fixedPortHost _ (extensionState_subset _ _ _)] at hs
  exact hs.vertexEdges F.vertexNumbering

end LooseHamilton.AuxiliaryFrame.Frame
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

lemma unexposed_subset_rawHost (f : Frame r original) (D : Finset V)
    (H : SimpleHypergraph V) : unexposed f D H⊆f.rawHost H := by
  rw [rawHost_decomposition f D H]
  exact subset_union_left

lemma numbered_rawRemainder_subset (f : Frame r original) (D : Finset V)
    (H T : SimpleHypergraph V) (hT : T⊆unexposed f D H) :
    f.numberedEdges (f.rawHost (rawRemainder f D H T))⊆f.numberedEdges (f.rawHost H) := by
  apply f.numberedEdges_mono
  rw [rawRemainder_eq f D H T hT, ←f.rawHost_delete H T]
  rw [rawHost_idempotent]
  rw [f.rawHost_delete]
  exact sdiff_subset

/-- The actual floor-defined batch is bounded using the full raw size, while
its definition continues to use the unexposed size. -/
lemma actual_batch_le_raw (f : Frame r original) (D : Finset V)
    (H : SimpleHypergraph V) (hnu : 0≤FrameScales.nu (Fintype.card V)) :
    (batchSize f D H:ℝ)≤FrameScales.nu (Fintype.card V)*(f.m H:ℝ)/f.k := by
  have hfloor : (batchSize f D H:ℝ)≤
      FrameScales.nu (Fintype.card V)*(unexposed f D H).card/f.k :=
    Nat.floor_le (by positivity)
  apply hfloor.trans
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (card_le_card (unexposed_subset_rawHost f D H))) hnu) (Nat.cast_nonneg _)

end LooseHamilton.CandidateBalance
