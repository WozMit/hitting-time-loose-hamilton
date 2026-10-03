module

public import HittingTimeLooseHamilton.FrameSamplingRefined
public import HittingTimeLooseHamilton.FrameEntropyBiasedInstance
public import HittingTimeLooseHamilton.FrameConditionalCompletionRemainder

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- Every sampled edge is counted in the raw host, even when boundary edges
are retained outside the sampling host. -/
lemma batch_subset_raw (f : Frame r original) (D : Finset V)
    (H T : SimpleHypergraph V) (hT : T⊆unexposed f D H) : T⊆f.rawHost H := by
  apply hT.trans
  rw [unexposed_eq_surviving]
  exact filter_subset _ _

lemma rawRemainder_rawHost (f : Frame r original) (D : Finset V)
    (H T : SimpleHypergraph V) (hT : T⊆unexposed f D H) :
    f.rawHost (rawRemainder f D H T)=f.rawHost H\T := by
  rw [rawRemainder_eq f D H T hT,←f.rawHost_delete H T,rawHost_idempotent]

lemma rawRemainder_m (f : Frame r original) (D : Finset V)
    (H T : SimpleHypergraph V) (hT : T⊆unexposed f D H) :
    f.m (rawRemainder f D H T)=f.m H-T.card := by
  unfold Frame.m
  rw [rawRemainder_rawHost f D H T hT,card_sdiff_of_subset (batch_subset_raw f D H T hT)]

/-- Exact raw-mean loss uses the raw edge count, not the unexposed count. -/
lemma rawRemainder_mu_eq (f : Frame r original) (D : Finset V)
    (H T : SimpleHypergraph V) (hT : T⊆unexposed f D H) :
    f.mu (rawRemainder f D H T)=(r:ℝ)*((f.m H:ℝ)-T.card)/f.n := by
  unfold Frame.mu
  rw [rawRemainder_m f D H T hT,Nat.cast_sub]
  exact card_le_card (batch_subset_raw f D H T hT)

lemma rawRemainder_mu_ratio (f : Frame r original) (hr : 0<r)
    (D : Finset V) (H T : SimpleHypergraph V) (hT : T⊆unexposed f D H)
    (hm : 0<f.m H) :
    f.mu (rawRemainder f D H T)/f.mu H=((f.m H:ℝ)-T.card)/f.m H := by
  rw [rawRemainder_mu_eq f D H T hT]
  unfold Frame.mu
  have hn : (f.n:ℝ)≠0 := by exact_mod_cast f.n_pos.ne'
  have hr' : (r:ℝ)≠0 := by exact_mod_cast hr.ne'
  have hm' : (f.m H:ℝ)≠0 := by exact_mod_cast hm.ne'
  field_simp
  <;> ring

lemma rawRemainder_mu_le (f : Frame r original) (D : Finset V)
    (H T : SimpleHypergraph V) (hT : T⊆unexposed f D H) :
    f.mu (rawRemainder f D H T)≤f.mu H := by
  rw [rawRemainder_mu_eq f D H T hT]
  unfold Frame.mu
  gcongr
  exact sub_le_self _ (Nat.cast_nonneg _)
end LooseHamilton.CandidateBalance
