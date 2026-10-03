module

public import HittingTimeLooseHamilton.CandidateFullHostBatch
public import HittingTimeLooseHamilton.CandidateLogSurvivalBudget
public import HittingTimeLooseHamilton.AuxiliaryFrameEntropy

public section

/-! Entropy-budget preservation for the actual frame after a full-host batch.
Using monotonicity of the allowed-host mean avoids equating the full-host and
allowed-host edge counts. The explicit logarithmic loss must fit in one unit
of the entropy-budget error. -/
noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

lemma mu_delete_le (F : Frame r original) (host T : Finset (Finset V)) :
    F.mu (host\T) ≤ F.mu host := by
  have hc : (F.rawHost (host\T)).card ≤ (F.rawHost host).card := by
    rw [F.rawHost_delete]
    exact card_le_card sdiff_subset
  unfold mu m
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hc) (Nat.cast_nonneg r))
    (Nat.cast_nonneg _)

theorem entropyBudget_after_full_host_survival (F : Frame r original)
    (hr : 3≤r) (host T : Finset (Finset V)) {τ : ℕ} {B h : ℝ}
    (hm : 0<(F.fullHost host).card)
    (hsmall : F.k+τ<(F.fullHost host).card)
    (hmu : 0<F.mu (host\T)) (h0 : 0≤h) (hh : h≤1/2)
    (hbudget : F.entropyBudget host B)
    (hsurvive : (1-h)*FrameSurvival.zeta (F.fullHost host).card τ F.k*
      (F.cycleCount host:ℝ) ≤ F.cycleCount (host\T))
    (herror : 2*h+(F.k:ℝ)*τ/((F.fullHost host).card-F.k-τ:ℕ) ≤
      (Fintype.card V:ℝ)/Real.sqrt (FrameScales.L1 (Fintype.card V))) :
    F.entropyBudget (host\T) (B+1) := by
  have hz := CandidateLogSurvival.zeta_pos hsmall
  have hlz := (CandidateLogSurvival.log_zeta_bounds hm hsmall).1
  change 0<FrameSurvival.zeta (F.fullHost host).card τ F.k at hz
  change -((F.k:ℝ)*τ/((F.fullHost host).card-F.k-τ:ℕ)) ≤
    Real.log (FrameSurvival.zeta (F.fullHost host).card τ F.k) at hlz
  obtain ⟨hx,hb⟩ := (F.entropyBudget_iff host B).mp hbudget
  have hxR : (0:ℝ)<F.cycleCount host := by exact_mod_cast hx
  have hhpos : 0<1-h := by linarith
  have hy : (0:ℝ)<F.cycleCount (host\T) :=
    (mul_pos (mul_pos hhpos hz) hxR).trans_le hsurvive
  have hl := Real.log_le_log (mul_pos (mul_pos hhpos hz) hxR) hsurvive
  rw [Real.log_mul (mul_pos hhpos hz).ne' hxR.ne',
    Real.log_mul hhpos.ne' hz.ne'] at hl
  have hlh := CandidateLogSurvival.log_one_sub_lower h0 hh
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hr1 : 0<(r:ℝ)-1 := by linarith
  have hlog := Real.log_le_log (mul_pos hr1 hmu)
    (mul_le_mul_of_nonneg_left (F.mu_delete_le host T) hr1.le)
  have hklog := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg F.k : (0:ℝ)≤F.k)
  apply (F.entropyBudget_iff (host\T) (B+1)).mpr
  refine ⟨by exact_mod_cast hy, ?_⟩
  have heq : (B+1)*(Fintype.card V:ℝ)/Real.sqrt (FrameScales.L1 (Fintype.card V)) =
      B*(Fintype.card V:ℝ)/Real.sqrt (FrameScales.L1 (Fintype.card V))+
      (Fintype.card V:ℝ)/Real.sqrt (FrameScales.L1 (Fintype.card V)) := by ring
  rw [heq]
  linarith

end LooseHamilton.AuxiliaryFrame.Frame
