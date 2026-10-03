module

public import HittingTimeLooseHamilton.FrameRestrictedBudgetScales
public import HittingTimeLooseHamilton.CandidateFrameBudget
public import HittingTimeLooseHamilton.FrameConditionalCompletionRemainder

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

lemma mu_pos_of_cycleFamily_nonempty (F : Frame r original) (hr : 3≤r)
    (H : SimpleHypergraph V) (h : (F.cycleFamily H).Nonempty) : 0<F.mu H := by
  have hk := F.k_pos hr h
  have hn : 0<F.n := lt_of_lt_of_le hk F.k_le_n
  obtain ⟨E,hE⟩ := h
  have hm : 0<F.m H := by
    have he : E.card=F.k := F.edge_card hr hE
    exact lt_of_lt_of_le (he ▸ hk) (card_le_card (F.mem_cycleFamily H E |>.mp hE).1)
  unfold mu
  exact div_pos (mul_pos (by exact_mod_cast (show 0<r by omega))
    (Nat.cast_pos.mpr hm)) (Nat.cast_pos.mpr hn)

/-- Positivity and budget preservation use the actual restricted survival
center. The raw-host mean may decrease by a different relative amount than
the sampled-host mean; monotonicity suffices. -/
theorem entropyBudget_after_restricted_survival (F : Frame r original)
    (hr : 3≤r) (H T : SimpleHypergraph V) {m τ : ℕ} {B h ν : ℝ}
    (hm : 0 < m) (hk4 : 4*F.k≤m) (ht4 : 4*τ≤m)
    (hscale : (τ:ℝ)*F.k/m≤ν) (h0 : 0≤h) (hh : h≤1/2)
    (hb : F.entropyBudget H B)
    (hs : |(F.cycleCount (H\T):ℝ)-
      CandidateLogSurvival.zeta m F.k τ*F.cycleCount H|≤
      h*(CandidateLogSurvival.zeta m F.k τ*F.cycleCount H))
    (he : 2*ν+2*h≤(Fintype.card V:ℝ)/Real.sqrt (FrameScales.L1 (Fintype.card V))) :
    0<F.cycleCount (H\T) ∧ F.entropyBudget (H\T) (B+1) := by
  have hz := CandidateLogSurvival.zeta_pos (show F.k+τ<m by omega)
  have hx : (0:ℝ)<F.cycleCount H := by exact_mod_cast hb.1.card_pos
  have hhpos : 0<1-h := by linarith
  have hs' : (1-h)*CandidateLogSurvival.zeta m F.k τ*(F.cycleCount H:ℝ)≤
      F.cycleCount (H\T) := by
    have hh := (abs_le.mp hs).1
    nlinarith
  have hy : (0:ℝ)<F.cycleCount (H\T) :=
    (mul_pos (mul_pos hhpos hz) hx).trans_le hs'
  have hyN : 0<F.cycleCount (H\T) := by exact_mod_cast hy
  have hmu := F.mu_pos_of_cycleFamily_nonempty hr (H\T) (card_pos.mp hyN)
  have hl := Real.log_le_log (mul_pos (mul_pos hhpos hz) hx) hs'
  rw [Real.log_mul (mul_pos hhpos hz).ne' hx.ne',
    Real.log_mul hhpos.ne' hz.ne'] at hl
  have hlh := CandidateLogSurvival.log_one_sub_lower h0 hh
  have hlz := CandidateLogSurvival.log_zeta_lower_of_quarters hm hk4 ht4 hscale
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hr1 : 0<(r:ℝ)-1 := by linarith
  have hlog := Real.log_le_log (mul_pos hr1 hmu)
    (mul_le_mul_of_nonneg_left (F.mu_delete_le H T) hr1.le)
  have hklog := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg F.k : (0:ℝ)≤F.k)
  refine ⟨hyN,(F.entropyBudget_iff (H\T) (B+1)).mpr ⟨hyN,?_⟩⟩
  have hb' := ((F.entropyBudget_iff H B).mp hb).2
  have hsplit : (B+1)*(Fintype.card V:ℝ)/Real.sqrt (FrameScales.L1 (Fintype.card V)) =
      B*(Fintype.card V:ℝ)/Real.sqrt (FrameScales.L1 (Fintype.card V))+
      (Fintype.card V:ℝ)/Real.sqrt (FrameScales.L1 (Fintype.card V)) := by ring
  rw [hsplit]
  linarith

lemma entropyBudget_rawHost (F : Frame r original) (H : SimpleHypergraph V) (B : ℝ) :
    F.entropyBudget (F.rawHost H) B ↔ F.entropyBudget H B := by
  unfold entropyBudget FrameEntropy.budget
  rw [CandidateBalance.cycleFamily_rawHost]
  have hm : F.mu (F.rawHost H)=F.mu H := by
    unfold mu m
    rw [CandidateBalance.rawHost_idempotent]
  rw [hm]
end LooseHamilton.AuxiliaryFrame.Frame
