module

public import HittingTimeLooseHamilton.FrameRemainderRegularityBasic
public import HittingTimeLooseHamilton.FrameRemainderParameters

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

lemma rawRemainder_mu_half (f : Frame r original) (D : Finset V)
    (H T : SimpleHypergraph V) (hT : T⊆unexposed f D H)
    (ht : 4*T.card≤(unexposed f D H).card) :
    f.mu H≤2*f.mu (rawRemainder f D H T) := by
  have hm0 : (unexposed f D H).card≤f.m H :=
    card_le_card (unexposed_subset_rawHost f D H)
  have htR : (4:ℝ)*T.card≤f.m H := by exact_mod_cast ht.trans hm0
  rw [rawRemainder_mu_eq f D H T hT]
  unfold Frame.mu
  rw [←mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hr : (0:ℝ)≤r := Nat.cast_nonneg _
  nlinarith

lemma numbered_rawRemainder_card_loss (f : Frame r original) (D : Finset V)
    (H T : SimpleHypergraph V) (hT : T⊆unexposed f D H) :
    ((f.numberedEdges (f.rawHost H)).card:ℝ)-
      (f.numberedEdges (f.rawHost (rawRemainder f D H T))).card=T.card := by
  rw [f.numberedEdges_card (f.rawHost H) (fun e he => (mem_filter.mp he).2),
    f.numberedEdges_card (f.rawHost (rawRemainder f D H T)) (fun e he => (mem_filter.mp he).2)]
  change (f.m H:ℝ)-f.m (rawRemainder f D H T)=T.card
  rw [rawRemainder_m f D H T hT]
  have ht : T.card≤f.m H := card_le_card (batch_subset_raw f D H T hT)
  rw [Nat.cast_sub ht]
  ring

/-- The deterministic preservation step keeps the entire current-frame
partition window `L`, in addition to degrees and codegrees. -/
theorem rawRemainder_upper_regular_of_loss (f : Frame r original) (hr : 2≤r)
    (D : Finset V) (H T : SimpleHypergraph V) (C L : ℝ) (hC : 0≤C)
    (hJ : PathGraphUpperRegular r C L (f.numberedEdges (f.rawHost H)))
    (hT : T⊆unexposed f D H) (ht : 4*T.card≤(unexposed f D H).card)
    (hloss : (1+partitionDensity r)*(T.card:ℝ)≤
      C*(r:ℝ)*f.m H*(Real.log (f.n:ℝ))^(-1/8:ℝ)) :
    PathGraphUpperRegular r (4*C) L
      (f.numberedEdges (f.rawHost (rawRemainder f D H T))) := by
  apply candidate_batch_upper_regular hC hr hJ
    (numbered_rawRemainder_subset f D H T hT)
  · simpa only [f.numbered_rawHost_mean] using rawRemainder_mu_half f D H T hT ht
  · rw [numbered_rawRemainder_card_loss f D H T hT,f.numbered_rawHost_mean]
    simp only [Fintype.card_fin]
    convert hloss using 1
    unfold Frame.mu
    have hn : (f.n:ℝ)≠0 := by exact_mod_cast f.n_pos.ne'
    field_simp <;> ring

end LooseHamilton.CandidateBalance
